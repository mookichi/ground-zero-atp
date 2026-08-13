# -*- coding: utf-8 -*-
"""Audit backticked names in a documentation file against the live declaration inventory.

Usage:
    python3 scripts/aiprover_audit.py [DOC.md]

DOC.md defaults to AIPROVER.md.  THEOREM_TIERS.md (and any other doc that
uses backticked declaration names) can be audited the same way:

    python3 scripts/aiprover_audit.py THEOREM_TIERS.md

The script walks every .lean file under the repository root (skipping .lake /
.git), builds a declaration inventory (namespace / section / begin..end aware,
covering all `hott` declaration keywords, structure/class fields including
parenthesized ones like `(mulComm : ...)`, inductive constructors, and
`elab`'d tactics/commands), then reports every backticked name from the doc
that does not resolve.

Expected baseline (2026-08-12): AIPROVER.md resolves all real names; the few
reported "missing" items are known benign categories (notation symbols such as
`⬝`/`⁻¹`, core Lean names, intentional historical mentions of retired axioms
such as `gaussPsd`/`infSumLin`, and probe-only names).  A non-empty report is
expected to be triaged, not treated as a failure by itself.
"""
import io, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DOC = os.path.join(ROOT, sys.argv[1] if len(sys.argv) > 1 else 'AIPROVER.md')

# --- identifier charset (incl. unicode sub/superscripts used by the library) ---
WORD = r'A-Za-zΑ-Ωα-ω_0-9₁₂₃₄₅₆₇₈₉₀⁰¹²³⁴⁵⁶⁷⁸⁹⁻Ω′\''
CLS = '[' + WORD + ']'  # character class wrapper
DECL_NAME = CLS + r"+(?:\.[A-Za-zΑ-Ωα-ω_]['" + WORD + r"']*)*"
DECL = re.compile(
    r'^\s*(?:hott\s+)?(?:opaque\s+)?(?:def|definition|theorem|lemma|corollary|axiom|'
    r'structure|class|inductive|instance|abbrev|abbreviation|remark|statement|proposition|implementation|exercise)\s+(' + DECL_NAME + r')(?:\s|:|$|[{<])')
STRUCT_HEAD = re.compile(
    r'^\s*(?:hott\s+)?(?:structure|class)\s+(' + DECL_NAME + r')(?:\s|\{|:|$|\(|where)')
IND_HEAD = re.compile(
    r'^\s*(?:hott\s+)?inductive\s+(' + DECL_NAME + r')(?:\s|\{|:|$|\(|where)')
NS_OPEN = re.compile(r'^\s*namespace\s+([A-Za-z0-9_\.]+)')
NS_CLOSE = re.compile(r'^\s*end(?:\s+([A-Za-z0-9_\.]+))?')
SEC_OPEN = re.compile(r'^\s*section(?:\s|$)')

def load(p):
    with io.open(p, encoding='utf-8', errors='replace') as f:
        return f.read()

def split_ns(ns_stack):
    return '.'.join(ns_stack)

# ---------- 1. inventory ----------
short_decls = set()
qualified = set()
notations = set()

files = []
for dirpath, dirnames, filenames in os.walk(ROOT):
    if '.lake' in dirpath or '.git' in dirpath:
        continue
    for fn in filenames:
        if fn.endswith('.lean'):
            files.append(os.path.join(dirpath, fn))
files.sort()

for fp in files:
    try:
        text = load(fp)
    except Exception:
        continue
    ns_stack = []
    block_kind = []
    lines = text.split('\n')
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        for tok in re.findall(r'\b(begin|end)\b', line):
            if tok == 'begin':
                block_kind.append('tac')
            else:
                if block_kind and block_kind[-1] == 'tac':
                    block_kind.pop()
                elif block_kind and block_kind[-1] == 'sec':
                    block_kind.pop()
                elif ns_stack:
                    ns_stack.pop()
                    block_kind.pop()
        m = NS_CLOSE.match(line)
        if m and m.group(1):
            parts = m.group(1).split('.')
            while block_kind and block_kind[-1] != 'ns':
                block_kind.pop()
            while ns_stack and ns_stack[-len(parts):] == parts:
                del ns_stack[-len(parts):]
                del block_kind[-len(parts):]
                break
            i += 1
            continue
        m = NS_OPEN.match(line)
        if m:
            segs = m.group(1).split('.')
            ns_stack.extend(segs)
            block_kind.extend(['ns'] * len(segs))
            i += 1
            continue
        m = SEC_OPEN.match(line)
        if m:
            block_kind.append('sec')
            i += 1
            continue
        if re.match(r'^\s*end\s*$', line):
            i += 1
            continue
        m = STRUCT_HEAD.match(line)
        if m:
            sname = m.group(1)
            full = split_ns(ns_stack)
            short_decls.add(sname)
            qualified.add(full + '.' + sname if full else sname)
            # fields only after a `:=` or `where` marker; `(T : Prering)` binder
            # params on the head line are NOT fields
            in_field_block = (':=' in line or 'where' in line or '{' in line)
            j = i + 1
            while j < n:
                l2 = lines[j].strip()
                if not l2:
                    j += 1
                    continue
                if l2.startswith('--'):
                    j += 1; continue
                if l2.startswith('/-'):
                    while j < n and '-/' not in lines[j]:
                        j += 1
                    j += 1
                    continue
                if ':=' in l2 or l2.startswith('where'):
                    in_field_block = True
                fm = re.match(r'^([A-Za-zΑ-Ωα-ω_][' + WORD + r'\']*)\s*:', l2)
                # parenthesized field: (name : T ...)  — only inside a `:=`/`where` field block
                pm = re.match(r'^\(([A-Za-zΑ-Ωα-ω_][' + WORD + r'\']*)\s*:', l2) if in_field_block else None
                if fm and not re.match(r'^(where|:|extends|\()', l2):
                    fname = fm.group(1)
                    short_decls.add(fname)
                    qualified.add((full + '.' + sname + '.' + fname) if full else (sname + '.' + fname))
                    j += 1
                    continue
                elif pm:
                    fname = pm.group(1)
                    short_decls.add(fname)
                    qualified.add((full + '.' + sname + '.' + fname) if full else (sname + '.' + fname))
                    j += 1
                    continue
                else:
                    break
            i = j
            continue
        m = IND_HEAD.match(line)
        if m:
            iname = m.group(1)
            full = split_ns(ns_stack)
            short_decls.add(iname)
            qualified.add(full + '.' + iname if full else iname)
            j = i + 1
            while j < n:
                l2 = lines[j].strip()
                if not l2:
                    j += 1
                    continue
                if l2.startswith('--'):
                    j += 1; continue
                if l2.startswith('/-'):
                    while j < n and '-/' not in lines[j]:
                        j += 1
                    j += 1
                    continue
                cm = re.match(r'^\|\s*([A-Za-zΑ-Ωα-ω_][' + WORD + r'\']*)\b', l2)
                if cm:
                    cname = cm.group(1)
                    short_decls.add(cname)
                    qualified.add((full + '.' + iname + '.' + cname) if full else (iname + '.' + cname))
                    j += 1
                    continue
                else:
                    break
            i = j
            continue
        m = DECL.match(line)
        if m:
            dname = m.group(1)
            full = split_ns(ns_stack)
            short_decls.add(dname)
            qualified.add(full + '.' + dname if full else dname)
            i += 1
            continue
        if re.search(r'^\s*(notation|infix|prefix|postfix|macro|syntax|declare_syntax_cat)\b', line) or \
           re.search(r'\b(notation|infix|prefix|postfix|macro)\b.*', line) and 'elab' not in line:
            for tok in re.findall(r'`([^`]+)`', line):
                notations.add(tok)
        # elab'd tactics / commands:  elab "name" ...  (also macro "name")
        em = re.match(r'^\s*(?:elab|macro)\s+"([^" ]+)', line)
        if em:
            tname = em.group(1)
            short_decls.add(tname)
            qualified.add(split_ns(ns_stack) + '.' + tname if split_ns(ns_stack) else tname)
        i += 1

# ---------- 2. doc names (whole doc, sectioned) ----------
doc = load(DOC)
lines = doc.split('\n')

section = '(header)'
doc_names = []  # (section, line_no, span, name)
for ln, l in enumerate(lines, 1):
    m = re.match(r'^#{1,3}\s+(.*)$', l)
    if m:
        section = m.group(1).strip()
        continue
    for span in re.findall(r'`([^`]+)`', l):
        s = span.strip()
        if not s:
            continue
        if '/' in s or s.endswith('.lean') or s.endswith('.md') or '\\' in s:
            continue
        if re.match(r'^[^A-Za-zΑ-Ωα-ω_0-9]+$', s):
            doc_names.append((section, ln, s, s))
            continue
        star = s.endswith('*')
        core = s[:-1] if star else s
        parts = [p for p in re.split(r'[/、]', core) if p]
        for p in parts:
            if re.match(r'^[A-Za-zΑ-Ωα-ω_][' + WORD + r'\']*(?:\.[A-Za-zΑ-Ωα-ω_][' + WORD + r'\']*)*$', p):
                doc_names.append((section, ln, s, p + ('*' if star else '')))

# ---------- 3. compare ----------
missing = []
found = []
for section, ln, span, name in doc_names:
    star = name.endswith('*')
    core = name[:-1] if star else name
    ok = False
    if not star and name in qualified:
        ok = True
    elif not star and name in short_decls:
        ok = True
    elif not star and '.' in name:
        if any(q.endswith('.' + name) or q == name for q in qualified):
            ok = True
    elif star:
        if any(x.startswith(core) for x in short_decls):
            ok = True
    if ok:
        found.append(name)
    else:
        missing.append((section, ln, span, name))

# ---------- 4. report ----------
print('=== %s: names checked: %d ; found: %d ; missing: %d ===' % (os.path.basename(DOC), len(doc_names), len(found), len(missing)))
print()
print('=== MISSING (name not found in inventory), grouped by section ===')
cur = None
for section, ln, span, name in missing:
    if section != cur:
        cur = section
        print()
        print('## %s' % section)
    print('  L%-4d %-30s (span: %s)' % (ln, name, span[:50]))
print()
print('=== notation symbols referenced (informational) ===')
for section, ln, span, name in doc_names:
    if name in notations or name in ('⬝', '⁻¹'):
        print('  %-16s -> %s' % (name, section))
print()
print('=== decl counts ===')
print('files: %d' % len(files))
print('short decls (+ctors+fields): %d' % len(short_decls))
print('qualified names: %d' % len(qualified))
print('notation tokens: %d' % len(notations))
