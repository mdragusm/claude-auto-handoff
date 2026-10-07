import type { EngineInterface, Register, Timer } from 'claude-code'
import { assembleBrief, briefPrompt, extractFacts, isValidBrief, markUnverifiedFigures } from './brief.ts'
import { chainOf, parseBrief, renderPage, viewerLink, withHeader } from './viewer.ts'
import type { Entry } from './viewer.ts'
import { SERVER_JS, parseAddress } from './server.ts'
import { isSpinning, panelTree } from './panel.tsx'
import type { Line, Panel } from './panel.tsx'
import { ASK_STEP, BRIEF_DIR, DEFAULTS, LAST_RESORT_INSTRUCTIONS, MIN_HEADROOM, SEED_PREFIX, TEMPLATES, expand, k, linkify, parseConfig, short } from './config.ts'
import type { Config, TemplateKey } from './config.ts'

// At the token threshold, Haiku writes a handoff brief, the mod runs /clear, then seeds the
// fresh session with a pointer to the brief. Interactive terminal sessions only: where a
// wrapper pipes the session and owns the context limit (DISABLE_AUTO_COMPACT), the mod only logs.
// In ask mode the threshold only asks; /handoff and the band's buttons hand off on request, and
// a brief can be written first for the person to edit (a draft), then sent.

let cfg: Config = DEFAULTS
// Origins the engine stamps on a prompt the person sent; the seed arrives as { kind: 'plugin' }.
const USER_ORIGINS = new Set(['composer', 'bridge'])
// Rough chars-per-token for tool output, used to project the next request's size.
const CHARS_PER_TOKEN = 4
// The panel above the prompt (panel.tsx) is the whole UI. No status entry: the host draws one
// as "⚠ auto-handoff:", which reads as an error.
const LOG = `~/${BRIEF_DIR}/auto-handoff.log`

// problem: why the brief is facts only, when Haiku's summary was unusable.
// manual: the person asked for this handoff (/handoff or a button), so the seed does not claim a limit.
type Pending = { oldSession: string; briefPath: string; tokens: number; chain: string; link: string; problem?: string; manual?: boolean }



// Module variables survive /clear; $.state does not.
let pending: Pending | undefined
// A brief written for review and not sent yet; Send hands off with the file as the person left it.
let draft: Pending | undefined
// When the mod last queued its own /clear: a SessionStart for it soon after is not the person's clear.
let ownClearAt = 0
// Ask mode: where the threshold question was last shown, so a dismissed one waits ASK_STEP before asking again.
let askedAt: { session: string; tokens: number } | undefined
let inFlight = false
let seededSession: string | undefined
let floor: number | undefined
let unattended = 0 // handoffs since the user last typed a prompt
let pausedSession: string | undefined
// The handoff the fresh session came from, until its first request is measured and shown on the panel.
let handedFrom: { session: string; tokens: number; link: string; problem?: string } | undefined
// The seeded session's place in its chain of handoffs, for its own brief's header. Also kept in
// the store as lineage:<session>, because a hot reload resets module variables: a session seeded
// before a reload would otherwise start a new chain when it hands off.
type Lineage = { from: string; chain: string; depth?: number }
let lineage: Lineage | undefined
// Tokens added since the last response measured the context: tool results and the
// response's own output. turn.complete alone missed a turn whose reads jumped from 63k
// straight past the window, because the request that would have measured it failed.
let unmeasured = 0
// The session whose tool call the gate refused. The refusal tells the model a handoff is coming,
// so one must follow even when the next response measures under the threshold: the gate counts
// tool output at CHARS_PER_TOKEN, which ran high in a live test (projected 83.7k, measured 72.5k)
// and left a session that stopped working with no handoff.
let gated: string | undefined
// From the latest SessionStart; /clear starts a new transcript file.
let transcriptPath: string | undefined

// Windows sets USERPROFILE, not HOME. With HOME unset, every path built on it began with
// "undefined/", which $.fs resolves under the session's working directory: briefs, templates
// and pages landed inside the user's project.
async function homeDir($: EngineInterface): Promise<string | undefined> {
  return (await $.env.get('HOME')) || (await $.env.get('USERPROFILE'))
}

async function log($: EngineInterface, line: string) {
  try {
    const path = `${await homeDir($)}/${BRIEF_DIR}/auto-handoff.log`
    const stamped = `${new Date().toISOString()} ${line}`
    // Where there is a `sh`, append: an append is atomic, so concurrent sessions and the viewer
    // server (which appends its own output here) never drop each other's lines.
    try {
      const { exitCode } = await $.process.run(['sh', '-c', 'mkdir -p "$(dirname "$2")" && printf "%s\\n" "$1" >> "$2"', 'sh', stamped, path])
      if (exitCode === 0) return
    } catch {}
    // Windows has no `sh`. $.fs has no append, so the log is read and rewritten: two lines logged
    // at the same instant can lose one. It keeps the last ~500 KB, cut at a line, so a read never
    // hits $.fs's 4 MiB cap.
    const old = await $.fs.read(path).catch(() => '')
    const kept = typeof old !== 'string' ? '' : old.length > 1_000_000 ? old.slice(old.indexOf('\n', old.length - 500_000) + 1) : old
    await $.fs.write(path, `${kept}${stamped}\n`)
  } catch {}
}


const readText = async ($: EngineInterface, path: string) => {
  try {
    const text = await $.fs.read(path)
    if (typeof text === 'string' && text.trim()) return text
  } catch {}
  return undefined
}
const shipped = ($: EngineInterface, key: TemplateKey) => `${$.plugin.root}/templates/${TEMPLATES.find(t => t[0] === key)![1]}`

// The template file at its configured path, else the default the mod ships, else ''.
async function template($: EngineInterface, key: TemplateKey): Promise<string> {
  return await readText($, expand(cfg[key], await homeDir($) ?? '')) ?? await readText($, shipped($, key)) ?? ''
}

// A new session writes each template to its path if nothing is there yet, so the files exist
// to be edited. A file the user wrote is never touched.
async function writeMissingTemplates($: EngineInterface) {
  const home = await homeDir($) ?? ''
  for (const [key] of TEMPLATES) {
    const path = expand(cfg[key], home)
    try { await $.fs.read(path); continue } catch {}
    const text = await readText($, shipped($, key))
    if (!text) { await log($, `template default unreadable ${shipped($, key)}`); continue }
    try { await $.fs.write(path, text) } catch (err) { await log($, `template write failed ${path} ${String(err)}`) }
  }
}

// The viewer server's address: the Tailscale host resolved to this machine's IPv4, or localhost
// when Tailscale is missing, logged out or has no address, so the link still opens on this machine.
async function serveAddress($: EngineInterface): Promise<{ host: string; port: string } | undefined> {
  const addr = cfg.viewer ? parseAddress(cfg.viewer) : undefined
  if (!addr || addr.host !== 'tailscale') return addr
  const local = { host: '127.0.0.1', port: addr.port }
  try {
    const { exitCode, stdout } = await $.process.run(['tailscale', 'ip', '-4'])
    const ip = stdout.trim().split('\n')[0]?.trim()
    return exitCode === 0 && ip ? { host: ip, port: addr.port } : local
  } catch {
    return local
  }
}

let lastServeTry = 0
// Starts the server detached (setsid, else nohup), so the pages stay served after this session
// exits: a brief's link is opened later, often from a phone, long after the handoff. When a
// server already holds the port, the new child exits at once, so a launch is safe to repeat.
// Its output goes to the mod's log. Answers whether the launch ran: it needs `sh`, which Windows
// lacks, and then the link falls back to the local file.
async function launchServer($: EngineInterface, pagesDir: string, addr: { host: string; port: string }): Promise<boolean> {
  try {
    const home = await homeDir($)
    const { exitCode } = await $.process.run(['sh', '-c', 'mkdir -p "$1"; if command -v setsid >/dev/null 2>&1; then d=setsid; else d=nohup; fi; $d node -e "$2" "$1" "$3" "$4" >>"$5" 2>&1 </dev/null &',
      'sh', pagesDir, SERVER_JS, addr.host, addr.port, `${home}/${BRIEF_DIR}/auto-handoff.log`])
    if (exitCode === 0) return true
    await log($, `viewer server failed exit=${exitCode}`)
  } catch (err) {
    await log($, `viewer server failed ${String(err)}`)
  }
  return false
}

// Brings the server back if it died (a reboot, a crash). Called on startup and after each turn,
// at most once in five minutes. Sessions with the kill switches set serve too: the switches stop
// handoffs, and serving old briefs is not one.
async function keepServing($: EngineInterface) {
  if (Date.now() - lastServeTry < 300_000) return
  lastServeTry = Date.now()
  const addr = await serveAddress($)
  const home = await homeDir($)
  if (addr && home) await launchServer($, `${home}/${BRIEF_DIR}/pages`, addr)
}

/** Writes the page of every brief in sessionId's chain, so each page lists the whole chain. */
async function writeChainPages($: EngineInterface, briefDir: string, pagesDir: string, sessionId: string): Promise<void> {
  const own = await $.fs.read(`${briefDir}/${sessionId}.md`)
  if (typeof own !== 'string') return
  const all: Entry[] = []
  for (const f of await $.fs.list(briefDir)) {
    if (f.kind !== 'file' || !f.name.endsWith('.md')) continue
    const id = f.name.slice(0, -3)
    try {
      const text = await $.fs.read(`${briefDir}/${f.name}`)
      if (typeof text !== 'string') continue
      const { header, body } = parseBrief(text)
      all.push({ id, header, body })
    } catch {}
  }
  const chain = chainOf(all, sessionId)
  for (const e of chain) await $.fs.write(`${pagesDir}/${e.id}.html`, renderPage(e, chain))
}

// Writes the pages for sessionId's chain and makes sure the server is up. Returns the page's
// link, or '' when the pages could not be written. Never throws: the viewer is not the handoff.
async function viewer($: EngineInterface, briefDir: string, pagesDir: string, sessionId: string): Promise<string> {
  try {
    // $.fs.write creates pagesDir, so no `mkdir`: a subprocess Windows can't run.
    await writeChainPages($, briefDir, pagesDir, sessionId)
    const addr = await serveAddress($)
    const served = addr && await launchServer($, pagesDir, addr)
    return viewerLink(served ? addr : undefined, pagesDir, sessionId)
  } catch (err) {
    await log($, `viewer error session=${sessionId} ${String(err)}`)
    return ''
  }
}

async function storedLineage($: EngineInterface, sessionId: string): Promise<Lineage | undefined> {
  try {
    const v = await $.store.get(`lineage:${sessionId}`) as Partial<Lineage> | undefined
    return typeof v?.from === 'string' && typeof v.chain === 'string' ? { from: v.from, chain: v.chain, depth: typeof v.depth === 'number' ? v.depth : undefined } : undefined
  } catch {
    return undefined
  }
}

// Writes the brief and its viewer pages, and answers what the clear and seed need; undefined when
// no brief landed, which the panel says.
async function writeBrief($: EngineInterface, sessionId: string, tokens: number, threshold: number, manual = false): Promise<Pending | undefined> {
  try {
    const own = sessionId === seededSession && lineage ? lineage : await storedLineage($, sessionId)
    const messages = await $.session.messages()
    const facts = extractFacts(messages, cfg.ignoreFiles)
    const { base, source } = await configured($)
    facts.handoffTokens = tokens
    facts.threshold = threshold
    facts.thresholdSource = threshold > base ? `${source} (${k(base)}), raised to leave ${k(MIN_HEADROOM)} above the starting size` : source
    if (sessionId === seededSession && floor !== undefined) facts.seededSessionStartSize = floor
    facts.unattendedCount = unattended
    // A session with no lineage starts its chain. One seeded before depth existed stays unknown.
    const depth = own ? own.depth : 1
    if (depth !== undefined) facts.depth = depth
    const briefTemplate = await template($, 'briefTemplate')
    const result = await $.model.complete({
      model: 'haiku',
      system: 'You summarize coding sessions into precise handoff briefs.',
      prompt: briefPrompt(messages, facts, briefTemplate),
      maxTokens: 1_500, // a lean brief; also a faster one
      timeoutMs: 60_000,
    })
    // A failed, empty or sectionless reply falls back to the facts.
    const text = result.isAnswered ? result.text : ''
    const problem = !result.isAnswered ? result.reason : !text.trim() ? 'empty' : !isValidBrief(text, briefTemplate) ? 'no-sections' : undefined
    if (problem) await log($, `haiku brief unusable session=${sessionId} reason=${problem}; using facts-only brief`)
    const checked = markUnverifiedFigures(text, facts)
    if (!problem && checked.flagged.length) await log($, `brief figures not in Handoff Numbers session=${sessionId}: ${checked.flagged.join(', ')}`)
    const home = await homeDir($)
    const cwd = await $.session.cwd()
    const brief = assembleBrief({
      sessionId,
      // Claude Code keeps transcripts under the cwd with every non-alphanumeric character as '-'.
      transcript: transcriptPath ?? `~/.claude/projects/${cwd.replace(/[^a-zA-Z0-9]/g, '-')}/${sessionId}.jsonl`,
      instructions: await template($, 'instructionsTemplate') || LAST_RESORT_INSTRUCTIONS,
    }, facts, problem ? undefined : checked.text)
    const briefDir = `${home}/${BRIEF_DIR}`
    const briefPath = `${briefDir}/${sessionId}.md`
    const pagesDir = `${briefDir}/pages`
    const chain = own?.chain ?? sessionId
    const header = { from: own?.from, chain, depth: depth !== undefined ? String(depth) : undefined, tokens: String(tokens), at: new Date().toISOString(), cwd }
    await $.fs.write(briefPath, withHeader(header, brief))
    const link = await viewer($, briefDir, pagesDir, sessionId)
    await log($, `brief written ${briefPath} (${brief.length} chars)`)
    return { oldSession: sessionId, briefPath, tokens, chain, link, problem, manual }
  } catch (err) {
    // fired stays 'briefing', which tryHandoff treats as an orphan: the next turn tries again.
    failed($, 'no brief written', manual ? 'this session keeps going; run /handoff to try again' : 'this session keeps going and tries again after the next turn')
    await log($, `handoff error session=${sessionId} ${String(err)}; no clear`)
    return undefined
  }
}

// Queues /clear; the SessionStart hook seeds the fresh session from `pending`.
async function clearAndSeed($: EngineInterface, p: Pending) {
  pending = p
  steps($, [briefStep(p.problem), { mark: 'spin', text: 'clearing' }])
  try {
    await $.store.set(`fired:${p.oldSession}`, p.problem ? `clearing-facts-only:${p.problem}` : 'clearing')
    await log($, `queueing /clear for ${p.briefPath}`)
  } catch (err) {
    await log($, `clear marker failed ${String(err)}`)
  }
  // The mod's own /clear skips its own command.run hook, and live classic.SessionStart never came,
  // so the seed follows the clear's own promise; a SessionStart that does come finds nothing pending.
  ownClearAt = Date.now()
  $.command.run({ command: 'clear' }).then(() => {
    $.clock.after(0, () => void afterClear($, 'clear').catch((err: unknown) => log($, `after clear error ${String(err)}`)))
  }, async (err: unknown) => {
    pending = undefined
    // fired stays 'clearing', so this session does not try again; it carries on as it is.
    failed($, '/clear was rejected', `this session keeps going; the brief is at ${p.briefPath}`)
    await log($, `clear rejected ${String(err)}`)
  })
}

async function handoff($: EngineInterface, sessionId: string, tokens: number, threshold: number, manual = false) {
  const p = await writeBrief($, sessionId, tokens, threshold, manual)
  if (p) await clearAndSeed($, p)
}

// Shared by turn.complete and turn.step: the fired, kill-switch and loop-guard checks, then
// the handoff itself. Returns true when a handoff started.
async function tryHandoff($: EngineInterface, sessionId: string, tokens: number, threshold: number, via: string): Promise<boolean> {
  const fired = await $.store.get(`fired:${sessionId}`)
  // Every caller checks inFlight first, so a 'briefing' marker seen here is an orphan: the
  // module reloaded mid-handoff and the brief never landed. Retry instead of going quiet.
  if (fired === 'briefing') await log($, `stale briefing marker session=${sessionId} (mod reloaded mid-handoff); retrying`)
  else if (fired) return false

  const pane = await paneVar($)
  if (pane) {
    await $.store.set(`fired:${sessionId}`, 'skipped-pane')
    await log($, `skip session=${sessionId} tokens=${tokens} reason=${pane} set`)
    return false
  }

  // Not marked fired: once the user types, the next turn can hand off.
  if (unattended >= cfg.maxUnattended) {
    if (pausedSession !== sessionId) {
      pausedSession = sessionId
      await log($, `loop guard session=${sessionId}: ${unattended} handoffs with no user prompt; paused until one`)
      showPanel($, { header: { mark: 'warn', text: `auto-handoff paused after ${unattended} handoffs in a row` }, steps: [{ mark: 'warn', text: 'send a message to resume' }], sticky: true },
        `paused after ${unattended} handoffs in a row: send a message to resume`)
    }
    return false
  }
  unattended++

  inFlight = true
  gated = undefined
  await $.store.set(`fired:${sessionId}`, 'briefing')
  await log($, `threshold session=${sessionId} tokens=${tokens} threshold=${threshold} via=${via}`)
  showPanel($, { header: { mark: 'spin', text: `auto-handoff · ${k(tokens)} / ${k(threshold)}` }, steps: [{ mark: 'spin', text: 'writing brief' }] },
    `context ${k(tokens)} is past ${k(threshold)}: handing off`)
  // Not awaited: the brief can take a while and /clear only runs once the session is idle.
  handoff($, sessionId, tokens, threshold).finally(() => { inFlight = false })
  return true
}

// Kill switches. AUTO_HANDOFF_DISABLE turns the mod off for one session. DISABLE_AUTO_COMPACT
// means something else owns the context limit (a wrapper that pipes the session, where /clear
// would break the pipe), so the mod stays out of its way too.
async function paneVar($: EngineInterface): Promise<string | undefined> {
  // Literal names: the host lists the variables a module reads.
  if (await $.env.get('AUTO_HANDOFF_DISABLE')) return 'AUTO_HANDOFF_DISABLE'
  if (await $.env.get('DISABLE_AUTO_COMPACT')) return 'DISABLE_AUTO_COMPACT'
  return undefined
}

// Whether tryHandoff would go ahead for this session. The tool gate refuses calls only then,
// so a session the mod will not hand off (pane, loop guard, already fired) is never blocked.
async function canHandOff($: EngineInterface, sessionId: string): Promise<boolean> {
  if (unattended >= cfg.maxUnattended || await paneVar($)) return false
  const fired = await $.store.get(`fired:${sessionId}`)
  return !fired || fired === 'briefing'
}

// The panel above the prompt. A module variable rather than $.state: $.state does not survive
// /clear, and the panel carries the handoff across it.
const FRAME_MS = 100 // the host redraws the band ten times a second at most
const DONE_MS = 10_000
let shown: Panel | undefined
let frame = 0
let spin: Timer | undefined
let collapse: Timer | undefined

// The band above the prompt is drawn on the terminal and desktop only. On the mobile app or in
// VS Code nothing shows it, so the moments that matter go out as a toast there too: the
// threshold tripping, the result, and anything that stays up until dismissed. Never per step.
const BAND_SURFACES = new Set(['terminal', 'desktop'])
async function toastOffBand($: EngineInterface, text: string) {
  try {
    if ((await $.session.surfaces()).some((s) => !BAND_SURFACES.has(s))) $.ui.toast(text, { timeoutMs: 30_000 })
  } catch (err) {
    await log($, `surfaces error ${String(err)}`)
  }
}

function showPanel($: EngineInterface, p: Panel, toast?: string) {
  if (toast) void toastOffBand($, toast)
  shown = p
  collapse?.cancel()
  collapse = undefined
  if (isSpinning(p)) {
    spin ??= $.clock.every(FRAME_MS, () => {
      frame++
      $.ui.invalidate('ui.render')
    })
  } else {
    spin?.cancel()
    spin = undefined
    if (!p.sticky) collapse = $.clock.after(DONE_MS, () => hidePanel($))
  }
  $.ui.invalidate('ui.render')
}

function hidePanel($: EngineInterface) {
  shown = undefined
  spin?.cancel()
  collapse?.cancel()
  spin = collapse = undefined
  $.ui.invalidate('ui.render')
}

// The steps under the panel's current header; a panel lost to a reload gets a plain one.
function steps($: EngineInterface, lines: Line[]) {
  showPanel($, { header: shown?.header ?? { mark: 'spin', text: 'auto-handoff' }, steps: lines })
}

// Adds a step to the panel on screen, or opens one under `header` when nothing is showing.
function addStep($: EngineInterface, step: Line, header: Line, sticky = false) {
  const p = shown ?? { header, steps: [] }
  showPanel($, { ...p, steps: [...p.steps, step], sticky: p.sticky || sticky }, step.mark === 'spin' || step.mark === 'done' ? undefined : step.text)
}

// A facts-only brief is the one quiet failure: the handoff works, but the brief is thin.
const briefStep = (problem?: string): Line => problem
  ? { mark: 'warn', text: `brief is facts only: the summary failed (${problem})` }
  : { mark: 'done', text: 'brief written' }

function failed($: EngineInterface, what: string, next: string) {
  showPanel($, { header: { mark: 'fail', text: `handoff failed: ${what}` }, steps: [{ mark: 'fail', text: next }, { mark: 'fail', text: `log: ${LOG}` }], sticky: true },
    `handoff failed: ${what}. ${next}`)
}

// The fresh session's first measurement: the panel's last step, which says the handoff worked.
// It collapses on its own unless the brief was facts only.
function showHandedOff($: EngineInterface, fresh: number) {
  if (!handedFrom) return
  const { tokens, link, problem } = handedFrom
  showPanel($, { header: { mark: 'done', text: `handed off · ${k(tokens)} → ${k(fresh)}` }, steps: problem ? [briefStep(problem)] : [], link: link || undefined, sticky: !!problem },
    `↪ handed off · ${k(tokens)} → ${k(fresh)}${problem ? ' · the brief is facts only' : ''}`)
  handedFrom = undefined
}

// The configured threshold and where it came from. The env var wins so a test run needs no
// /config change; it also outlives the test in that shell, which is why the headroom warning names it.
async function configured($: EngineInterface): Promise<{ base: number; source: string }> {
  const env = Number(await $.env.get('AUTO_HANDOFF_TOKENS'))
  return env > 0 ? { base: env, source: 'AUTO_HANDOFF_TOKENS' } : { base: cfg.threshold, source: 'threshold in /config' }
}

// A seeded session hands off no sooner than MIN_HEADROOM past its floor, whatever the threshold says.
async function thresholdFor($: EngineInterface, sessionId: string): Promise<number> {
  const { base } = await configured($)
  return sessionId === seededSession ? Math.max(base, (floor ?? 0) + MIN_HEADROOM) : base
}

// Once per seeded session, as its floor lands: when the configured threshold leaves less than
// MIN_HEADROOM above the floor, say so, with the number, the source, and where the line moved to.
// Without this the 2026-10-04 chain looked like a guard bug; nobody had run `env | grep AUTO_HANDOFF`.
let warnedSession: string | undefined
async function warnTightThreshold($: EngineInterface, sessionId: string) {
  if (floor === undefined || warnedSession === sessionId) return
  warnedSession = sessionId
  const { base, source } = await configured($)
  const headroom = base - floor
  if (headroom >= MIN_HEADROOM) return
  await log($, `tight threshold session=${sessionId} threshold=${base} source=${source} floor=${floor} headroom=${headroom} effective=${floor + MIN_HEADROOM}`)
  const left = headroom > 0 ? `leaves ${k(headroom)}` : 'is below'
  addStep($, { mark: 'warn', text: `threshold ${k(base)} (${source}) ${left} this session's ${k(floor)} start: handing off at ${k(floor + MIN_HEADROOM)} instead` }, { mark: 'warn', text: 'auto-handoff' }, true)
}

// A file: link for the panel. Windows paths come with backslashes, and a space breaks a markdown link.
const fileUrl = (path: string) => encodeURI(`file:///${path.replace(/\\/g, '/').replace(/^\/+/, '')}`)

// Opens the draft for editing in the editor setting, else Notepad on Windows, the default text
// editor on macOS, xdg-open elsewhere. Never throws: the panel's link opens it too.
async function openInEditor($: EngineInterface, path: string) {
  try {
    if (await $.env.get('OS') === 'Windows_NT') {
      // Start-Process returns at once; running the editor directly would hold the call until it closes.
      await $.process.run(['powershell', '-NoProfile', '-Command', `Start-Process -FilePath $env:AUTO_HANDOFF_EDITOR -ArgumentList ('"' + $env:AUTO_HANDOFF_BRIEF + '"')`],
        { env: { AUTO_HANDOFF_EDITOR: cfg.editor || 'notepad.exe', AUTO_HANDOFF_BRIEF: path.replace(/\//g, '\\') } })
      return
    }
    if (cfg.editor) {
      await $.process.run(['sh', '-c', '"$0" "$1" >/dev/null 2>&1 &', cfg.editor, path])
      return
    }
    const { stdout } = await $.process.run(['uname'])
    await $.process.run(stdout.trim() === 'Darwin' ? ['open', '-t', path] : ['xdg-open', path])
  } catch (err) {
    await log($, `open draft failed ${path} ${String(err)}`)
  }
}

// The person's own handoff, from /handoff or a band button: no threshold and no loop guard.
// review: write the brief and stop, so it can be edited before Send. With a draft waiting, a
// handoff sends the draft as the person left it.
async function startManual($: EngineInterface, review: boolean): Promise<string> {
  if (inFlight || pending) return 'a handoff is already under way'
  const sessionId = await $.session.id()
  if (draft && draft.oldSession !== sessionId) draft = undefined
  if (draft) {
    if (review) {
      await openInEditor($, draft.briefPath)
      showReview($)
      return `the brief is waiting for review at ${draft.briefPath}`
    }
    const p = draft
    draft = undefined
    unattended = 0
    await log($, `draft sent session=${sessionId} ${p.briefPath}`)
    showPanel($, { header: { mark: 'spin', text: `handing off · ${k(p.tokens)}` }, steps: [] })
    await clearAndSeed($, p)
    return `handing off with the brief at ${p.briefPath}`
  }
  const tokens = ((await $.session.usage()).context.tokens ?? 0) + unmeasured
  const threshold = await thresholdFor($, sessionId)
  unattended = 0
  pausedSession = undefined
  inFlight = true
  gated = undefined
  await $.store.set(`fired:${sessionId}`, 'briefing')
  await log($, `manual ${review ? 'review' : 'handoff'} session=${sessionId} tokens=${tokens}`)
  showPanel($, { header: { mark: 'spin', text: `${review ? 'brief for review' : 'handing off'} · ${k(tokens)}` }, steps: [{ mark: 'spin', text: 'writing brief' }] })
  // Not awaited, as at the threshold: the brief can take a while.
  const work = review ? reviewBrief($, sessionId, tokens, threshold) : handoff($, sessionId, tokens, threshold, true)
  work.finally(() => { inFlight = false })
  return review ? 'writing the brief for review' : 'handing off to a fresh session'
}

async function reviewBrief($: EngineInterface, sessionId: string, tokens: number, threshold: number) {
  const p = await writeBrief($, sessionId, tokens, threshold, true)
  if (!p) return
  draft = p
  // Not cleared or seeded: the threshold leaves this session alone while the draft waits.
  await $.store.set(`fired:${sessionId}`, 'review')
  await openInEditor($, p.briefPath)
  showReview($)
}

function showReview($: EngineInterface) {
  if (!draft) return
  showPanel($, {
    header: { mark: 'warn', text: `handoff brief ready for review · ${k(draft.tokens)}` },
    steps: [...(draft.problem ? [briefStep(draft.problem)] : []), { mark: 'warn', text: `edit and save ${draft.briefPath}, then Send` }],
    link: fileUrl(draft.briefPath),
    linkLabel: 'open the brief',
    sticky: true,
    actions: [{ key: 'handoff-send', label: 'Send handoff', hotkey: '1', primary: true }, { key: 'handoff-discard', label: 'Discard', hotkey: '2' }],
  }, `handoff brief ready for review: ${draft.briefPath}`)
}

async function discardDraft($: EngineInterface) {
  const p = draft
  draft = undefined
  hidePanel($)
  if (!p) return
  askedAt = { session: p.oldSession, tokens: p.tokens }
  await $.store.delete(`fired:${p.oldSession}`)
  await log($, `draft discarded session=${p.oldSession} ${p.briefPath}`)
}

// Ask mode at the threshold: the question, once per ASK_STEP of growth.
async function ask($: EngineInterface, sessionId: string, tokens: number, threshold: number) {
  if (draft || inFlight || pending || await paneVar($)) return
  if (askedAt?.session === sessionId && tokens < askedAt.tokens + ASK_STEP) return
  askedAt = { session: sessionId, tokens }
  await log($, `ask session=${sessionId} tokens=${tokens} threshold=${threshold}`)
  showAsk($, `context ${k(tokens)} is past ${k(threshold)}: hand off to a fresh session?`)
}

function showAsk($: EngineInterface, question: string) {
  showPanel($, {
    header: { mark: 'warn', text: question },
    steps: [],
    sticky: true,
    actions: [{ key: 'handoff-now', label: 'Hand off now', hotkey: '1', primary: true }, { key: 'handoff-review', label: 'Not yet: review the brief', hotkey: '2' }],
  }, `${question} /handoff now to hand off, /handoff review to edit the brief first`)
}

async function onAction($: EngineInterface, key: string) {
  try {
    if (key === 'handoff-now' || key === 'handoff-send') await startManual($, false)
    else if (key === 'handoff-review') await startManual($, true)
    else if (key === 'handoff-discard') await discardDraft($)
  } catch (err) {
    await log($, `action ${key} error ${String(err)}`)
  }
}

async function registerCommand($: EngineInterface) {
  try {
    await $.command.register({ name: 'handoff', description: 'Hand this session off to a fresh one: asks, or "now", or "review" to edit the brief first', argumentHint: '[now|review|send|discard]' })
  } catch (err) {
    await log($, `command register failed ${String(err)}`)
  }
}

// Seeds the fresh session after a /clear: from the mod's own clear once it resolves, from the
// person's /clear through its command.run hook, and from classic.SessionStart where that arrives
// (live on Windows, 2.1.293, it never did). Whichever runs first seeds; the rest find nothing pending.
async function afterClear($: EngineInterface, via: string) {
  await log($, `after clear via=${via} pending=${pending ? short(pending.oldSession) : 'none'}`)
  void registerCommand($)
  // A /clear of the person's own leaves no handoff to report; the panel from the last one goes too.
  // The mod's own clear, seen again after it seeded, is not one.
  if (!pending) {
    const own = via === 'clear' || (via === 'SessionStart' && Date.now() - ownClearAt < 30_000)
    if (!own && !inFlight) {
      draft = undefined
      if (shown) hidePanel($)
    }
    return
  }
  const p = pending
  pending = undefined
  try {
    const newSession = await $.session.id()
    seededSession = newSession
    floor = undefined
    unmeasured = 0
    await $.store.set(`fired:${p.oldSession}`, `seeded:${newSession}`)
    await log($, `seeding new=${newSession} from=${p.oldSession}`)
    handedFrom = { session: p.oldSession, tokens: p.tokens, link: p.link, problem: p.problem }
    steps($, [briefStep(p.problem), { mark: 'done', text: 'cleared' }, { mark: 'spin', text: 'starting the fresh session' }])
    const own = await storedLineage($, p.oldSession)
    const prior = own ? own.depth : 1
    lineage = { from: p.oldSession, chain: p.chain, depth: prior !== undefined ? prior + 1 : undefined }
    await $.store.set(`lineage:${newSession}`, lineage)
    // The old brief learns where it went, and its chain's pages link forward.
    try {
      const old = parseBrief(await $.fs.read(p.briefPath) as string)
      // viewer: the page link, read by the status line script for the session it handed off to.
      await $.fs.write(p.briefPath, withHeader({ ...old.header, to: newSession, ...(p.link ? { viewer: p.link } : {}) }, old.body))
      const briefDir = p.briefPath.replace(/\/[^/]+$/, '')
      await viewer($, briefDir, `${briefDir}/pages`, p.oldSession)
    } catch (err) {
      await log($, `viewer forward link failed ${String(err)}`)
    }
    // One line on screen; the model reads the brief from disk. A full brief as the
    // seed showed up as a wall of text the person never wrote.
    const why = p.manual ? 'The previous session was handed off on request and cleared.' : 'The previous session hit its context limit and was cleared.'
    const text = `${SEED_PREFIX} ${short(p.oldSession)}. ${why} Read the brief at ${p.briefPath} before doing anything else${p.link ? ` (readable copy: ${p.link})` : ''} and follow its Instructions section. Open your first reply with the line "↪ Handoff from session ${short(p.oldSession)}".`
    await log($, `seed submitted new=${newSession}`)
    $.prompt.submit({ text }).catch((err: unknown) => {
      handedFrom = undefined
      failed($, 'the seed prompt was rejected', `paste the brief path to carry on: ${p.briefPath}`)
      return log($, `seed rejected ${String(err)}`)
    })
  } catch (err) {
    await log($, `seed error ${String(err)}`)
  }
}

export const register: Register = (on, options) => {
  cfg = parseConfig(options)
  on('turn.complete', async ($, e, next) => {
    const r = await next(e)
    try {
      if (!e.agentId) await keepServing($)
      if (e.agentId || inFlight || pending) return r // subagent turns fire turn.complete too
      const tokens = (await $.session.usage()).context.tokens
      if (tokens === undefined) return r
      const sessionId = await $.session.id()
      if (sessionId === seededSession && floor === undefined) {
        // Fallback only: turn.step sets the floor from the seed turn's first response. Reached
        // when that response carried no usage.
        floor = tokens
        await log($, `floor set at turn end session=${sessionId} tokens=${tokens} (first response carried no usage)`)
        showHandedOff($, tokens)
        await warnTightThreshold($, sessionId)
        return r
      }
      const threshold = await thresholdFor($, sessionId)
      if (tokens < threshold && gated !== sessionId) return r
      if (cfg.mode === 'ask') {
        await ask($, sessionId, tokens, threshold)
        return r
      }
      await tryHandoff($, sessionId, tokens, threshold, gated === sessionId ? 'turn.complete gated' : 'turn.complete')
    } catch (err) {
      await log($, `turn.complete error ${String(err)}`)
    }
    return r
  })

  // Tool output lands in the next request; count it before that request is sent. Past the
  // threshold, refuse the call instead: one step of parallel reads took a session from 67k to
  // 437k with no request in between for turn.step to stop. A refused call never runs; the
  // next request trips turn.step and the handoff goes through the normal path.
  on('tool.call', async ($, e, next) => {
    if (!e.agentId) {
      try {
        const sessionId = await $.session.id()
        const tokens = (await $.session.usage()).context.tokens
        const projected = (tokens ?? 0) + unmeasured
        const threshold = await thresholdFor($, sessionId)
        if (inFlight || pending || (cfg.mode === 'auto' && tokens !== undefined && projected >= threshold && await canHandOff($, sessionId))) {
          if (!inFlight && !pending) gated = sessionId
          await log($, `tool refused session=${sessionId} tool=${e.tool} projected=${projected} threshold=${threshold}`)
          return { deny: `[auto-handoff] Not run: the context is past the handoff threshold (${k(projected)} ≥ ${k(threshold)}). This session is handing off to a fresh one, which will redo this call. Make no more tool calls.` }
        }
      } catch (err) {
        await log($, `tool.call gate error ${String(err)}`)
      }
    }
    const r = await next(e)
    if (!e.agentId && typeof r.text === 'string') unmeasured += Math.ceil(r.text.length / CHARS_PER_TOKEN)
    return r
  })

  // Before each main-loop request: if the last measured size plus what has landed since
  // crosses the threshold, end the turn here and hand off instead of sending a request
  // that may overflow the window.
  on('turn.step', async function* ($, e, next) {
    if (!e.agentId && cfg.mode === 'auto' && !inFlight && !pending && e.index > 0) {
      try {
        const tokens = (await $.session.usage()).context.tokens
        const sessionId = await $.session.id()
        const isSeedTurn = sessionId === seededSession && floor === undefined
        if (tokens !== undefined && !isSeedTurn) {
          const projected = tokens + unmeasured
          const threshold = await thresholdFor($, sessionId)
          const isGated = gated === sessionId
          if ((projected >= threshold || isGated) && await tryHandoff($, sessionId, projected, threshold, `turn.step measured=${tokens}${isGated ? ' gated' : ''}`)) {
            unmeasured = 0
            // A gated session can measure under the threshold here; "would carry" a number below it reads as a bug.
            const why = projected >= threshold
              ? `The next request would carry about ${Math.round(projected / 1000)}k tokens (threshold ${Math.round(threshold / 1000)}k).`
              : `A tool call was refused at the handoff threshold (${Math.round(threshold / 1000)}k).`
            yield { kind: 'text', index: 0, text: `[auto-handoff] ${why} Stopping this turn to hand off to a fresh session.` }
            yield { kind: 'stop', stopReason: 'end_turn', usage: null }
            return { turnId: e.turnId, index: e.index, answer: '', toolUses: [], stopReason: 'end_turn', usage: null }
          }
        }
      } catch (err) {
        await log($, `turn.step error ${String(err)}`)
      }
    }
    const before = unmeasured
    const seeding = !e.agentId && seededSession !== undefined && floor === undefined
    const r = yield* next(e)
    // The response measured everything up to its request; its own output is new, and so is
    // any tool output that landed while it streamed (core runs tools before the stream ends).
    if (!e.agentId && r.usage) unmeasured = unmeasured - before + r.usage.output_tokens
    // The seed turn's first request is the fresh session's true starting size. Measuring at
    // the end of that turn instead let a busy first turn (47k to 129k of reads) set
    // the floor at 129k, with the pre-request check off the whole way.
    if (seeding && r.usage) {
      floor = r.usage.input_tokens + r.usage.cache_read_input_tokens + r.usage.cache_creation_input_tokens
      await log($, `floor session=${seededSession} tokens=${floor} (seed turn's first request)`)
      showHandedOff($, floor)
      await warnTightThreshold($, seededSession!)
    }
    return r
  })

  // The engine's own auto-compact runs ahead of the turn.step check (live tests 2026-10-03:
  // two compactions, no turn.step line). Catch it here and hand off in its place.
  on('session.compact', async ($, e, next) => {
    if (e.trigger !== 'auto' || e.agentId) return next(e)
    if (inFlight || pending) return { skip: 'auto-handoff in progress' }
    try {
      const sessionId = await $.session.id()
      const tokens = ((await $.session.usage()).context.tokens ?? 0) + unmeasured
      const threshold = await thresholdFor($, sessionId)
      await log($, `auto-compact session=${sessionId} projected=${tokens}`)
      // The window is full, so a draft waiting for review goes out as it stands.
      if (draft?.oldSession === sessionId) {
        // On a timer, as /handoff does: /clear from inside this hook would wait on the turn it holds.
        $.clock.after(0, () => void startManual($, false).catch((err: unknown) => log($, `draft send error ${String(err)}`)))
        unmeasured = 0
        return { skip: 'auto-handoff: sending the reviewed brief instead of compacting' }
      }
      if (await tryHandoff($, sessionId, tokens, threshold, 'session.compact')) {
        unmeasured = 0
        return { skip: 'auto-handoff: handing off to a fresh session instead of compacting' }
      }
    } catch (err) {
      await log($, `session.compact error ${String(err)}`)
    }
    return next(e)
  })

  // The seed row in the transcript: the brief path and the viewer URL drawn as links, so a
  // click opens them. The stored message stays as submitted; only the drawing changes. A
  // Markdown element linkifies http:, https: and file: (the Link element refuses the
  // Tailscale IP), and the panel draws its brief link the same way.
  // Yields the band to a survey, and passes when there is nothing to show.
  on('ui.render', { component: 'AbovePrompt' }, async ($, e, next) => {
    if (!shown || e.props.hasSurvey) return next(e)
    return panelTree($.ui.resolve(e), shown, frame, () => hidePanel($), (key) => void onAction($, key))
  })

  on('ui.render', { component: 'UserMessage', props: { origin: { kind: 'plugin' } } }, async ($, e, next) => {
    const origin = e.props.origin
    if (origin.kind !== 'plugin' || origin.name !== $.plugin.name || !e.props.text.startsWith(SEED_PREFIX)) return next(e)
    const { Markdown } = $.ui.resolve(e)
    return <Markdown text={linkify(e.props.text)} />
  })

  on('prompt.submit', async ($, e, next) => {
    if (e.origin && USER_ORIGINS.has(e.origin.kind)) {
      unattended = 0
      if (pausedSession) hidePanel($) // the pause panel's "send a message to resume" is done
      pausedSession = undefined
    }
    return next(e)
  })

  // Once per process, before the first prompt (never on /clear). Startup work lives here rather
  // than in classic.SessionStart, which did not reach the mod live.
  on('session.start', async ($, e, next) => {
    await registerCommand($)
    await writeMissingTemplates($)
    await keepServing($)
    return next(e)
  })

  on('command.run', { command: 'handoff' }, async ($, e) => {
    const arg = e.args.trim().toLowerCase()
    if (arg === 'discard') {
      if (!draft) return { text: 'no brief is waiting for review' }
      await discardDraft($)
      return { text: 'draft discarded' }
    }
    if (arg && arg !== 'now' && arg !== 'review' && arg !== 'send') return { text: 'usage: /handoff [now|review|send|discard]' }
    if (arg === 'send' && !draft) return { text: 'no brief is waiting for review; /handoff now hands off' }
    if (inFlight || pending) return { text: 'a handoff is already under way' }
    const sessionId = await $.session.id()
    // Bare /handoff asks, with the same buttons as the threshold; a draft waiting shows its own.
    if (!arg) {
      if (draft?.oldSession === sessionId) showReview($)
      else showAsk($, `context ${k((await $.session.usage()).context.tokens ?? 0)}: hand off to a fresh session?`)
      return { text: 'choose above the prompt' }
    }
    const review = arg === 'review'
    // The host refuses /clear from inside a command.run hook (it would wait on this hook), so the
    // work starts on a timer once the command has answered.
    $.clock.after(0, () => void startManual($, review).catch((err: unknown) => log($, `/handoff error ${String(err)}`)))
    const waiting = draft?.oldSession === sessionId ? draft.briefPath : undefined
    return { text: review ? (waiting ? `opening the brief at ${waiting}` : 'writing the brief for review') : waiting ? `handing off with the brief at ${waiting}` : 'handing off to a fresh session' }
  })

  on('command.run', { command: 'clear' }, async ($, e, next) => {
    const r = await next(e)
    // On a timer: a prompt submitted from inside this hook would wait on it.
    $.clock.after(0, () => void afterClear($, 'command').catch((err: unknown) => log($, `after clear error ${String(err)}`)))
    return r
  })

  on('classic.SessionStart', async ($, e, next) => {
    const r = await next(e)
    if (e.transcript_path) transcriptPath = e.transcript_path
    if (e.source === 'clear') await afterClear($, 'SessionStart')
    return r
  })
}
