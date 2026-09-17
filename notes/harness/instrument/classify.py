"""Shared classification helpers for session instrumentation.

Written for /coordinate-research coordinator sessions (2026-09-15); extended
2026-09-17 (first /harness-review) to the attack track: notes/attacks/<name>/
{brief,state,log}.md and the workbook are math, its drivers/ are drivers, the
Lean sources, .refs PDFs and lean-lsp MCP calls are math corpus, HARNESS.md /
notes/harness/ / notes/attacks/{README,TEMPLATE-state}.md are harness."""
import re, json, os

# ---------- file-path classification ----------
HARNESS_PAT = [
    r'\bCLAUDE\.md', r'\bROADMAP\.md', r'\bRESEARCH-ARC\.md', r'\bDESIGN\.md',
    r'\bPHASE-BOUNDARIES\.md', r'\bCLEANUP\.md', r'\bTACTICS-[A-Z]+\.md',
    r'\bREFS\.md', r'\bREADME\.md', r'notes/Phase\d+[a-z]?\.md',
    r'dispatch-log\.md', r'Harness-structure\.md', r'coordinate-research\.md',
    r'coordinate-phase\.md', r'agents-core', r'\.claude/agents', r'\.claude/commands',
    r'FRICTION\.md', r'notes/BlueprintExposition\.md', r'\.claude/settings',
    r'notes/pencil/labels\.md', r'\.claude/skills',
    r'\bHARNESS\.md', r'notes/harness/', r'notes/attacks/README\.md',
    r'notes/attacks/TEMPLATE-state\.md', r'\bPHASE-BOUNDARIES', r'\bHARNESS-',
]
MATH_PAT = [
    r'notes/pencil/workbook/', r'notes/pencil/strategy\.md', r'notes/pencil/fanout\.md',
    r'notes/scripts/w4/', r'notes/pencil/rounds/', r'notes/pencil/[a-z0-9_]+\.md',
    r'blueprint/src/',
    r'notes/attacks/[A-Za-z0-9_-]+/(?:brief|state|log)\.md', r'\.lean\b', r'\.refs/',
    r'notes/Phase\d+-design\.md', r'notes/pencil/adjudications\.md',
]
TOOLING_SCRIPTS = [
    'notes/ledger.py', 'notes/gapmap.py', 'notes/phasenote.py',
    'notes/scripts/gapdiff.py', 'notes/scripts/blindaxes.py',
    'session-usage.py',
]
TOOLING_PAT = [r'notes/ledger\.py', r'notes/gapmap\.py', r'notes/phasenote\.py', r'notes/harness/check\.py',
               r'notes/check-[a-z-]+\.py', r'notes/scripts/gapdiff\.py',
               r'notes/scripts/blindaxes\.py', r'session-usage\.py']
DRIVER_PAT = [r'notes/scripts/w4/[A-Za-z0-9_]+\.py', r'notes/attacks/[A-Za-z0-9_-]+/drivers/']

def _any(pats, s):
    return any(re.search(p, s) for p in pats)

def file_class(path):
    """harness | math | tooling | driver | scratch | other"""
    if _any(TOOLING_PAT, path): return 'tooling'
    if _any(DRIVER_PAT, path):  return 'driver'
    if _any(HARNESS_PAT, path): return 'harness'
    if _any(MATH_PAT, path):    return 'math'
    if '/private/tmp' in path or 'scratchpad' in path: return 'scratch'
    return 'other'

READ_CMDS = re.compile(r'(?:^|[|;&]\s*|\$\(\s*)(sed -n|cat|head|tail|grep|rg|wc|ls|find|awk|nl|less|diff)\b')
WRITE_RE = re.compile(r'(cat\s*>>?\s*|tee\s+|sed -i|>\s*notes/|>\s*ROADMAP|>>\s*notes/|open\([^)]*[\'"]w[\'"]|\.write\(|s\.replace\(|applypatch)')

MATH_EDIT_TARGETS = [r'notes/pencil/workbook/', r'notes/pencil/strategy\.md',
                     r'notes/pencil/rounds/', r'notes/scripts/w4/',
                     r'notes/attacks/[A-Za-z0-9_-]+/(?:brief|state|log)\.md',
                     r'notes/attacks/[A-Za-z0-9_-]+/drivers/']
PROC_EDIT_TARGETS = [r'notes/Phase\d+', r'notes/pencil/fanout\.md', r'ROADMAP\.md',
                     r'dispatch-log\.md', r'Harness-structure\.md', r'RESEARCH-ARC\.md',
                     r'coordinate-research\.md', r'agents-core', r'CLAUDE\.md',
                     r'notes/pencil/labels\.md', r'DESIGN\.md', r'README\.md',
                     r'\.claude/', r'HARNESS\.md', r'notes/harness/', r'TEMPLATE-state']

PY_HEREDOC_TARGET = re.compile(r"(?:^|\n)\s*p\s*=\s*['\"]([^'\"]+)['\"]")
OPEN_TARGET = re.compile(r"open\(\s*['\"]([^'\"]+)['\"]")

def paths_in(cmd):
    out = []
    for m in re.finditer(r"[A-Za-z0-9_./\-]+\.(?:md|py|tex|txt|yaml|yml|json|lean)", cmd):
        out.append(m.group(0))
    for m in PY_HEREDOC_TARGET.finditer(cmd): out.append(m.group(1))
    for m in OPEN_TARGET.finditer(cmd): out.append(m.group(1))
    return out

def is_write(cmd):
    if re.search(r'cat\s*>>?\s*\S', cmd): return True
    if re.search(r'\bsed -i\b', cmd): return True
    if re.search(r"open\([^)]*,\s*['\"]w", cmd): return True
    if re.search(r"\bs\s*=\s*s\.replace\(", cmd): return True
    if re.search(r"f\.write\(|\.write_text\(", cmd): return True
    return False

def write_targets(cmd):
    """paths this command actually writes to"""
    t = []
    for m in re.finditer(r"cat\s*>>?\s*([A-Za-z0-9_./\-\$\{\}]+)", cmd): t.append(m.group(1))
    for m in re.finditer(r"sed -i[^ ]*\s+(?:-e\s+)?['\"][^'\"]*['\"]\s+(\S+)", cmd): t.append(m.group(1))
    # python heredoc rewrite pattern: p='path' ... open(p,'w')
    if re.search(r"open\(p,\s*['\"]w|\bs\.replace\(", cmd):
        for m in PY_HEREDOC_TARGET.finditer(cmd): t.append(m.group(1))
    for m in re.finditer(r"open\(\s*['\"]([^'\"]+)['\"]\s*,\s*['\"][wa]", cmd): t.append(m.group(1))
    for m in re.finditer(r"(?:^|[^>])>>?\s*([A-Za-z0-9_./\-\$\{\}]+\.(?:md|txt|py|json))", cmd): t.append(m.group(1))
    return t

POLL_ONLY = re.compile(r'^[\s\S]*$')
def classify_bash(cmd):
    """returns (bucket, note)."""
    c = cmd
    # 1. math driver invocation (even when redirected to a file / backgrounded)
    if re.search(r'python3?\s+\S*notes/scripts/w4/\S+\.py', c) or re.search(r'python3?\s+\S*/w4/\S+\.py', c):
        return 'd', 'driver'
    if re.search(r'python3?\s+\S*notes/attacks/[A-Za-z0-9_-]+/drivers/\S+\.py', c) or re.search(r'python3?\s+\S*/drivers/\S+\.py', c):
        return 'd', 'driver'
    if re.search(r'\blake\s+(?:env\s+lean|build|exe)\b', c):
        return 'd', 'lean-check'
    # 2. harness tooling invocation
    if re.search(r'python3?\s+\S*(ledger|gapmap|phasenote|check-[a-z-]+|harness/check|gapdiff|blindaxes|session-usage|instrument/\w+)\.py', c):
        return 'c', 'tooling'
    # 3. writes
    if is_write(c):
        tg = write_targets(c)
        joined = ' '.join(tg) if tg else c
        if _any(MATH_EDIT_TARGETS, joined): return 'f_math', joined[:80]
        if _any(PROC_EDIT_TARGETS, joined): return 'f_proc', joined[:80]
        if 'scratchpad' in joined or '/private/tmp' in joined:
            low = joined.lower()
            if re.search(r'msg|commit', low): return 'f_proc', 'scratch:commit-msg'
            if re.search(r'pass|rank|draft|dispatch|prompt', low): return 'f_math', 'scratch:draft'
            return 'f_math', 'scratch'
        return 'i', joined[:80]
    # 4. git
    if re.search(r'(?:^|[|;&]\s*)git\s', c): return 'e', 'git'
    # 5. background-job polling / waiting
    if re.search(r'tasks/\w+\.output|scratchpad/|\$SP|/private/tmp', c):
        if not re.search(r'(?:^|[|;&\n]\s*)(cat|tail|head|grep|sed|rg|awk|nl|diff)\b', c):
            return 'j', 'poll/wait'
        # reading a background driver output or a direction draft = consuming math
        return 'b', 'read driver-output/draft'
    if re.search(r'^\s*(sleep|until|pgrep|ps aux|uptime|date)\b', c): return 'j', 'poll/wait'
    # 6. reads
    ps = paths_in(c)
    classes = [file_class(p) for p in ps]
    if 'math' in classes or 'driver' in classes: return 'b', ','.join(sorted(set(ps)))[:80]
    if 'harness' in classes or 'tooling' in classes: return 'a', ','.join(sorted(set(ps)))[:80]
    if READ_CMDS.search(c):
        if re.search(r'notes/pencil|notes/scripts/w4|notes/attacks/[A-Za-z0-9_-]+/|\.lean\b|\.refs/', c): return 'b', 'grep-math'
        if re.search(r'\.claude|notes/Phase|ROADMAP|CLAUDE\.md|notes/', c): return 'a', 'grep-harness'
        return 'i', 'read-other'
    return 'i', c[:60]

def classify_tool(name, inp):
    if name == 'Bash': return classify_bash(inp.get('command',''))
    if name in ('Agent','SendMessage'): return 'g', name
    if name in ('TaskStop','Monitor'): return 'j', name
    if name in ('CronCreate','CronDelete','CronList'): return 'h', name
    if name in ('Edit','Write','NotebookEdit'):
        p = inp.get('file_path','')
        if _any(MATH_EDIT_TARGETS, p): return 'f_math', p
        if _any(PROC_EDIT_TARGETS, p): return 'f_proc', p
        return 'f_math' if file_class(p)=='math' else ('f_proc' if file_class(p)=='harness' else 'i'), p
    if name == 'Read':
        p = inp.get('file_path','')
        fc = file_class(p)
        return ('b' if fc in ('math','driver') else 'a' if fc=='harness' else 'i'), p
    if name in ('Grep','Glob'):
        pat = json.dumps(inp)
        if re.search(r'notes/pencil|w4|notes/attacks/[A-Za-z0-9_-]+/|\.lean|Molecul|Pencil', pat): return 'b','grep'
        if re.search(r'Phase|ROADMAP|CLAUDE|claude', pat): return 'a','grep'
        return 'i','grep'
    if name.startswith('mcp__lean'): return 'b', name
    if name in ('WebFetch','WebSearch'): return 'b', name
    return 'i', name

# ---------- session kind, from the first slash command that is not a local setting ----------
SKIP_CMDS = {'/model', '/clear', '/help', '/config', '/cost', '/usage', '/status', '/compact', '/fast',
             '/context', '/memory', '/permissions', '/login', '/logout', '/doctor', '/resume', '/init'}
CMD = re.compile(r'<command-name>(.*?)</command-name>(?:.*?<command-args>(.*?)</command-args>)?', re.S)

def kind_of(cmds, prompt=None):
    """(label, group): group is 'attack' for /attack and /review-attack sessions, 'lean' for
    /coordinate-phase, 'review' for /harness-review, else 'other'."""
    for c, a in cmds:
        if c in SKIP_CMDS: continue
        if c == '/attack': return 'attack ' + a, 'attack'
        if c == '/review-attack': return 'review ' + a, 'attack'
        if c == '/coordinate-phase': return 'lean ' + a, 'lean'
        if c == '/harness-review': return 'harness-review', 'review'
        return (c + ' ' + a).strip(), 'other'
    return (prompt or '(no prompt)'), 'other'

BUCKET_NAMES = {
 'a':'read harness/process docs', 'b':'read math corpus',
 'c':'run ledger/gapmap/check tooling', 'd':'run math drivers',
 'e':'git operations', 'f_math':'edit math prose', 'f_proc':'edit status/process surfaces',
 'g':'Agent dispatch / SendMessage', 'h':'cron keepalives', 'i':'other', 'j':'poll/wait on background jobs',
}
