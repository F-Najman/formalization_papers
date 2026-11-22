"""Write Challenge.lean, the self-contained statement of the compared results, from the library sources.

The Challenge imports only Mathlib. It copies verbatim every declaration of the library that the compared results
use (definitions, instances, inductive types, and the theorems used inside their values), in import order, and then
the compared declarations with their proofs or values replaced by `sorry`. Which declarations are used is computed by
Lean: `scripts/challenge_deps.lean` follows the constants in the statements, in the definitions they use, and so on,
and prints the source range of each. Every copied declaration is put back into the scope it has in its source file
(`@[expose] public section`, `noncomputable section`, namespaces, `section`s, `open`s and `variable`s), and the
Challenge imports exactly the Mathlib modules that the source files of these declarations import, so that the
elaborated constants are the library's. Comparator (with comparator.json) then checks that the library proves these
statements about these definitions.

Run from the project directory, after `lake build`:
    python3 scripts/make_challenge.py          (writes Challenge.lean and comparator.json)
    python3 scripts/make_challenge.py --check  (checks that both are up to date)
"""
import json
import os
import re
import subprocess
import sys

NS = 'NajmanTrbovic'

# The compared declarations, in the order of the paper: (heading, [(name, mode)]); mode is 'stmt' (a theorem, proof
# replaced by sorry) or 'hole' (a definition whose value the Solution supplies; its type is the claim).
TARGETS = [
    ('Section 2: the explicit models, squareclasses and quadratic fields', [
        ('represents_iff_rational_twist', 'stmt'),
        ('quadraticOrder_isIntegralClosure', 'stmt'),
        ('numberField_discriminant', 'stmt'),
        ('radicand_eq_of_isomorphic', 'stmt'),
        ('residueRingEquiv', 'hole'),
    ]),
    ('Theorem 2.2 (Table 2)', [
        ('table2_split', 'stmt'),
        ('table2_unramified', 'stmt'),
        ('table2_not_inert', 'stmt'),
        ('table2_odd_radicand', 'stmt'),
        ('table2_real', 'stmt'),
        ('table2_refinements', 'stmt'),
        ('table2_odd_split_residue', 'stmt'),
        ('real_radicand_of_specialization', 'stmt'),
    ]),
    ('Lemma 2.6 (the odd-valuation lemma, in its corrected form)', [
        ('squareclass_of_prime_power_residue', 'stmt'),
    ]),
    ('Theorem 2.8', [
        ('field_odd_ramified_imp_square', 'stmt'),
        ('field_ramified_imp_square', 'stmt'),
    ]),
    ('Theorem 2.12', [
        ('infinite_ramified_field_parameters', 'stmt'),
    ]),
    ('Theorem 2.13 and Table 7, corrected (non-exceptional points)', [
        ('table7_field_iff', 'stmt'),
    ]),
    ('Errata: an exceptional point at level 26, and counterexamples to the printed Lemmas 2.6(b) and 2.9', [
        ('exceptional26', 'stmt'),
        ('eleven_ramifies_exceptional26', 'stmt'),
        ('lemma26b_counterexample', 'stmt'),
        ('lemma26b_conclusion_fails', 'stmt'),
        ('lemma29_counterexample', 'stmt'),
    ]),
    ('Section 3: the descended model and its invariants', [
        ('Cubic.descended_invariants', 'stmt'),
        ('Cubic.descended_j', 'stmt'),
        ('Cubic.r_splits_mod_prime', 'stmt'),
        ('Cubic.valuation_j_at_two', 'stmt'),
        ('Cubic.marked_j_cross_multiplication', 'stmt'),
        ('Cubic.finiteChart_factors_from_root', 'stmt'),
    ]),
    ('Proposition 3.1: local splitting', [
        ('Cubic.threeProjectiveLifts_at_two', 'stmt'),
        ('Cubic.threeProjectiveLifts_of_nonintegral_ratio', 'stmt'),
        ('Cubic.cubic_tensor_splits_of_nonintegral_j', 'stmt'),
        ('Cubic.norm_j_gt_one_of_multiplicative_reduction', 'stmt'),
        ('Cubic.residue_algebra_of_split_tensor', 'stmt'),
        ('Cubic.distinct_prime_factors_of_residue_product', 'stmt'),
        ('Cubic.cubic_residue_splits_of_multiplicative_reduction', 'stmt'),
        ('Cubic.cubic_prime_splits_of_multiplicative_reduction', 'stmt'),
        ('Cubic.cubic_residue_splits_at_two', 'stmt'),
    ]),
    ('Proposition 3.1: from the torsion hypothesis to the marked model', [
        ('Cubic.short_equation_of_two_torsion', 'stmt'),
        ('Cubic.marked_parameters_of_order_fourteen', 'stmt'),
        ('Cubic.normalized_torsion_has_affine_model', 'stmt'),
        ('Cubic.marked_fiber_j', 'stmt'),
        ('Cubic.cubic_torsion_group_has_marked_model', 'stmt'),
        ('Cubic.cubic_torsion_group_has_descended_j', 'stmt'),
    ]),
    ('Proposition 3.1: the splitting conclusion, under the hypotheses named in each statement', [
        ('Cubic.cubic_prime_splits_of_torsion_and_rational_projection', 'stmt'),
        ('Cubic.two_torsion_polynomial_has_root_of_multiplicative_reduction', 'stmt'),
        ('Cubic.cubic_prime_splits_of_torsion_and_nonrational_two_torsion', 'stmt'),
        ('Cubic.cubic_prime_splits_or_full_rational_two_torsion', 'stmt'),
        ('Cubic.torsion_group_has_galois_stable_order_seven', 'stmt'),
        ('Cubic.cubic_prime_splits_of_torsion_and_integral_j_at_level_fourteen', 'stmt'),
    ]),
]

HEADER = '''module

{imports}

/-!
# Splitting of primes in number fields generated by points on some modular curves: statements

From F. Najman, A. Trbović, Res. Number Theory 8 (2022), Article 28 (arXiv:2009.02485). Generated by
`scripts/make_challenge.py`: the library declarations that the statements use, copied verbatim in import order and in
the scopes of their source files, then the statements, with their proofs replaced by `sorry`. `residueRingEquiv` is a
definition whose type is the claim. The curves are the paper's explicit affine models (`Level.form`, `Cubic.fibre`).
-/

/-- Empties Lean's per-module cache of auxiliary proofs (`foo._proof_1`), so that a copied definition cannot reuse an
auxiliary proof made for a definition from another library module. It runs before the copied declarations of each
module. Defining this command adds two auxiliary constants; running it adds no declaration. -/
elab "reset_aux_lemma_cache" : command =>
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {{}}
'''

DECL_START = re.compile(r'^(@\[[^\]]*\]\s*)*((private|protected|noncomputable|public|partial|unsafe)\s+)*'
                        r'(theorem|lemma|def|abbrev|instance|inductive|structure|class|opaque)\b')


def path_of(module):
    return module.replace('.', '/') + '.lean'


def lean_deps(names):
    """Run scripts/challenge_deps.lean on the compared declarations; its lines, parsed."""
    listed = set(re.findall(r'^import all (\S+)$', open('scripts/challenge_deps.lean').read(), re.M))
    modules = {f'{NS}.' + f[:-5] for f in os.listdir(NS) if f.endswith('.lean')} | {NS}
    if listed != modules:
        raise SystemExit(f'scripts/challenge_deps.lean must `import all` exactly the library modules; missing '
                         f'{sorted(modules - listed)}, extra {sorted(listed - modules)}')
    os.makedirs('.lake', exist_ok=True)
    with open('.lake/challenge_targets.txt', 'w') as f:
        f.write('\n'.join(f'{NS}.{n}' for n in names) + '\n')
    r = subprocess.run(['lake', 'env', 'lean', 'scripts/challenge_deps.lean'], capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit('challenge_deps.lean failed:\n' + r.stdout + r.stderr)
    rows = []
    for line in r.stdout.splitlines():
        role, idx, module, first, last, kind, name = line.split('\t')
        rows.append(dict(role=role, idx=int(idx), module=module, first=int(first), last=int(last), kind=kind,
                         name=name))
    return rows


def scopes_at(lines, n):
    """The scopes open at line n (1-based) of a source file: a list of frames [opener, end line, [opens and
    variables]] from the outermost."""
    stack = []
    comment = False
    for line in lines[:n - 1]:
        s = line.strip()
        if comment:
            comment = '-/' not in s
            continue
        if s.startswith('/-'):
            comment = '-/' not in s
            continue
        if re.match(r'^(@\[expose\] )?public section$', s):
            stack.append([s, 'end', []])
        elif s == 'noncomputable section':
            stack.append([s, 'end', []])
        elif re.match(r'^section(\s+\S+)?$', s):
            name = s.split()[1] if len(s.split()) > 1 else ''
            stack.append([s, f'end {name}'.strip(), []])
        elif s.startswith('namespace '):
            stack.append([s, 'end ' + s.split()[1], []])
        elif re.match(r'^end(\s+\S+)?$', s):
            if not stack:
                raise SystemExit(f'unbalanced end: {s}')
            stack.pop()
        elif re.match(r'^(open|variable|universe)\b', s) and line == s:
            if not stack:
                raise SystemExit(f'open/variable outside any scope: {s}')
            stack[-1][2].append(s)
    return stack


def opener_lines(stack):
    out = []
    for opener, _end, cmds in stack:
        out.append(opener)
        out += cmds
    return out


def closer_lines(stack):
    return [end for _opener, end, _cmds in reversed(stack)]


def decl_text(lines, row, copy):
    """The source text of a declaration (docstring and attributes included), with a preceding `set_option ... in`
    kept for copied declarations."""
    first, last = row['first'], row['last']
    while copy and first > 1 and re.match(r'^set_option \S+ \S+ in$', lines[first - 2]):
        first -= 1
    text = '\n'.join(lines[first - 1:last]).rstrip() + '\n'
    body = [l for l in text.split('\n') if not l.startswith(('/--', ' ', 'set_option', '-/')) and l]
    if not body or not DECL_START.match(body[0]) and not text.lstrip().startswith(('/--', '@[', 'set_option')):
        raise SystemExit(f'{row["name"]}: unexpected source text at {row["module"]}:{row["first"]}')
    return text


def sorried(text, name):
    """Replace the proof or value after the declaration's top-level `:=` by `sorry`."""
    m = re.search(r':=( by)?[ \t]*\n', text)
    if not m:
        raise SystemExit(f'{name}: cannot find the end of the statement')
    return text[:m.start()] + ':= sorry\n'


def file_imports(path):
    """The imports of a source file, as (public, module) pairs."""
    return [(bool(m.group(1)), m.group(2)) for m in re.finditer(r'^(public )?import (\S+)\s*$', open(path).read(), re.M)]


def exported(module):
    """The Mathlib modules that a library module makes visible to its importers: its public imports, recursively."""
    out = []
    for public, mod in file_imports(path_of(module)):
        if public:
            out += [mod] if mod.startswith('Mathlib') else exported(mod)
    return out


def imports(modules):
    """The Mathlib modules visible in the given source files: their own imports, and what their library imports
    export."""
    mods = []
    for module in modules:
        for _, mod in file_imports(path_of(module)):
            for m in [mod] if mod.startswith('Mathlib') else exported(mod):
                if m not in mods:
                    mods.append(m)
    return '\n'.join(f'public import {m}' for m in mods)


def library_namespaces():
    """The namespaces opened by `namespace` commands in the library sources (full names)."""
    out = set()
    for root, _dirs, files in os.walk(NS):
        for f in files + ([] if root != NS else []):
            if f.endswith('.lean'):
                stack = []
                for line in open(os.path.join(root, f)).read().split('\n'):
                    m = re.match(r'^namespace (\S+)$', line)
                    if m:
                        stack.append(m.group(1))
                        out.add('.'.join(stack))
                    elif re.match(r'^end (\S+)$', line) and stack and line.split()[1] == stack[-1]:
                        stack.pop()
    return out


def filter_opens(stack, local, present):
    """Drop from `open` commands the namespaces that exist only in the library (namespaces of library declarations
    that the Challenge does not copy): nothing in the Challenge can refer to them, and Lean rejects an `open` of a
    namespace that does not exist."""
    current = '.'.join(s.split()[1] for s, _e, _c in stack if s.startswith('namespace '))
    prefixes = [current.split('.')[:i] for i in range(len(current.split('.')), -1, -1)] if current else [[]]
    out = []
    for opener, end, cmds in stack:
        kept = []
        for c in cmds:
            if not c.startswith('open '):
                kept.append(c)
                continue
            words = c.split()[1:]
            keep = []
            for w in words:
                if w == 'scoped' or w.startswith('('):
                    keep.append(w)
                    continue
                cands = ['.'.join(p + [w]) for p in prefixes]
                if any(x in local for x in cands) and not any(x in present for x in cands):
                    continue
                keep.append(w)
            if [w for w in keep if w != 'scoped']:
                kept.append('open ' + ' '.join(keep))
        out.append([opener, end, kept])
    return out


def emit(items):
    """Lean text for a list of items, in order: ('heading', text) or ('decl', module, stack, text, copied). A scope
    (section, namespace, `open`s and `variable`s) stays open while consecutive declarations share it, and only the frames
    that differ are closed and opened; a frame is extended in place when the new declaration has the same frame with
    more `open`s or `variable`s after it. `reset_aux_lemma_cache` runs before the first copied declaration of each
    library module."""
    out = []
    cur = []
    last_module = None
    pending = []
    for item in items:
        if item[0] == 'heading':
            pending.append(item[1])
            continue
        _, module, stack, text, copied = item
        k = 0
        while k < min(len(cur), len(stack)) and cur[k] == stack[k]:
            k += 1
        extend = (k < min(len(cur), len(stack)) and cur[k][0] == stack[k][0]
                  and stack[k][2][:len(cur[k][2])] == cur[k][2])
        keep = k + 1 if extend else k
        closers = closer_lines(cur[keep:])
        openers = (stack[k][2][len(cur[k][2]):] if extend else []) + opener_lines(stack[keep:])
        if closers:
            out.append('\n'.join(closers) + '\n')
        out.append('\n')
        for h in pending:
            out.append(h + '\n\n')
        pending = []
        if openers:
            out.append('\n'.join(openers) + '\n')
        if copied and module != last_module:
            out.append('reset_aux_lemma_cache\n')
            last_module = module
        out.append(text)
        cur = stack
    out.append('\n'.join(closer_lines(cur)) + '\n' if cur else '')
    return ''.join(out)


def challenge():
    names = [n for _, decls in TARGETS for n, _ in decls]
    modes = {n: m for _, decls in TARGETS for n, m in decls}
    rows = lean_deps(names)
    source = {}

    def lines_of(module):
        if module not in source:
            source[module] = open(path_of(module)).read().split('\n')
        return source[module]

    deps = sorted((r for r in rows if r['role'] == 'dep'), key=lambda r: (r['idx'], r['first']))
    targets = {r['name']: r for r in rows if r['role'] == 'target'}
    used_modules = list(dict.fromkeys(r['module'] for r in sorted(rows, key=lambda r: r['idx'])))
    local = library_namespaces()
    present = {'.'.join(r['name'].split('.')[:i]) for r in rows for i in range(1, len(r['name'].split('.')))}

    def scopes(module, first):
        return filter_opens(scopes_at(lines_of(module), first), local, present)
    out = [HEADER.format(imports=imports(used_modules))]
    # A theorem among the declarations used is used inside an instance proof; it is stated (with `sorry`) and compared
    # by its statement, since Comparator compares the proofs of the declarations it does not treat as statements, and
    # a proof term contains auxiliary lemmas whose names depend on the module. (Instances of propositional classes are
    # theorems too; they are copied with their proofs.)

    def stated(r):
        return r['kind'] == 'theorem' and re.search(r'^(theorem|lemma) ', decl_text(lines_of(r['module']), r, False),
                                                    re.M) is not None

    aux = [r['name'][len(NS) + 1:] for r in deps if stated(r)]
    items = [('heading', '/-! ## Definitions used by the statements, copied from the library -/')]
    for r in deps:
        text = decl_text(lines_of(r['module']), r, not stated(r))
        items.append(('decl', r['module'], scopes(r['module'], r['first']),
                      sorried(text, r['name']) if stated(r) else text, not stated(r)))
    for heading, decls in TARGETS:
        items.append(('heading', f'/-! ## {heading} -/'))
        for n, _ in decls:
            r = targets[f'{NS}.{n}']
            text = decl_text(lines_of(r['module']), r, False)
            items.append(('decl', r['module'], scopes(r['module'], r['first']), sorried(text, n), False))
    out.append(emit(items))
    config = {
        'challenge_module': 'Challenge',
        'solution_module': 'Solution',
        'theorem_names': [f'{NS}.{n}' for n in names if modes[n] == 'stmt'] + [f'{NS}.{n}' for n in aux],
        'definition_names': [f'{NS}.{n}' for n in names if modes[n] == 'hole'],
        'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'],
    }
    return ''.join(out), json.dumps(config, indent=4) + '\n'


if __name__ == '__main__':
    os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
    text, config = challenge()
    if '--check' in sys.argv:
        ok = all(os.path.exists(p) and open(p).read() == t
                 for p, t in [('Challenge.lean', text), ('comparator.json', config)])
        print('Challenge.lean and comparator.json are up to date' if ok else
              'Challenge.lean or comparator.json is NOT up to date')
        sys.exit(0 if ok else 1)
    open('Challenge.lean', 'w').write(text)
    open('comparator.json', 'w').write(config)
    print(f'wrote Challenge.lean: {text.count(chr(10))} lines, {len(text.encode())} bytes; comparator.json')
