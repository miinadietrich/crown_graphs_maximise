#!/usr/bin/env python3
"""Finite certificate and arithmetic verification for the crown bound. Python 3.10+, C++17.

No graph-family enumerator, SAT solver, Lean process or Comparator is invoked.
See README.md for the mathematical scope and requirements.
"""
import sys
sys.dont_write_bytecode = True
import argparse
from collections import Counter, deque
from fractions import Fraction
import gzip
import hashlib
from itertools import product
import json
from math import comb, factorial
from pathlib import Path
import platform
import subprocess
import time
import traceback
import uuid

ROOT = Path(__file__).resolve().parent
DATA = ROOT / 'data'
OLD = DATA


def require(test, message):
    if not test:
        raise ValueError(message)


def digest(path):
    with path.open('rb') as stream:
        return hashlib.sha256(stream.read()).hexdigest()


def matchings(items):
    if not items:
        yield ()
    else:
        first, *rest = items
        for index, other in enumerate(rest):
            for tail in matchings(rest[:index] + rest[index + 1:]):
                yield ((first, other),) + tail


def pairings(k):
    result = [tuple(pair[::-1] if flip else pair for pair, flip in zip(matching, (0,) + bits))
              for matching in matchings(list(range(2 * k)))
              for bits in product((0, 1), repeat=k - 1)]
    expected = factorial(2 * k) // (2 * factorial(k))
    require(len(result) == len(set(result)) == expected, 'Pairing representatives incomplete/duplicated')
    for pairs in result:
        require(sorted(x for pair in pairs for x in pair) == list(range(2 * k)), 'Invalid matching')
    return result


def below(a, b):
    return all(x == 0 or y == 0 or x < y for x, y in zip(a, b))


def horn_closure(rows, selected):
    """Least forced-high set, using only rows in the supplied small support."""
    fixed = [b for b in selected if 0 not in rows[b]]
    one = [b for b in selected if rows[b].count(0) == 1]
    forced = {b for b in one if any(below(rows[b], rows[u]) for u in fixed)}
    queue = deque(forced)
    while queue:
        b = queue.popleft()
        for c in one:
            if c not in forced and below(rows[c], rows[b]):
                forced.add(c)
                queue.append(c)
    conflict = any(below(rows[l], rows[u]) for l in fixed for u in fixed)
    conflict |= any(below(rows[l], rows[b]) for l in fixed for b in forced)
    return forced, conflict


def check_closure():
    data = json.loads((DATA / 'three-pair-closure.json').read_bytes())
    rows = [tuple(r) for r in data['rows']]
    require(data['limit'] == 6 and rows == list(product(range(4), repeat=3)), 'Incorrect closure domain')
    states = [(owner, frozenset(s)) for owner, s in data['states']]
    cores = [frozenset(s) for s in data['cores']]
    require(len(states) == len(set(states)) == 2517 and len(cores) == len(set(cores)) == 759,
            'Incorrect closure inventory')
    fixed = [b for b, r in enumerate(rows) if 0 not in r]
    one = [b for b, r in enumerate(rows) if r.count(0) == 1]
    owned = {b: [] for b in one}
    for owner, support in states:
        require(owner in one and owner in support and 1 <= len(support) <= 6 and
                all(type(x) is int and 0 <= x < 64 for x in support), 'Invalid support')
        require(owner in horn_closure(rows, support)[0], 'Unsupported forced-high witness')
        owned[owner].append(support)
    for core in cores:
        require(2 <= len(core) <= 6 and all(type(x) is int and 0 <= x < 64 for x in core), 'Invalid core')
        require(horn_closure(rows, core)[1], 'Listed core is feasible')
        require(all(not horn_closure(rows, core - {b})[1] for b in core), 'Core is not minimal')
    counters = Counter()
    for b in one:
        for u in fixed:
            if below(rows[b], rows[u]):
                require(any(s <= {b, u} for s in owned[b]), 'Missing seed coverage')
                counters['seed'] += 1
    for b, support in states:
        for c in one:
            extended = support | {c}
            if len(extended) <= 6 and below(rows[c], rows[b]):
                require(any(s <= extended for s in owned[c]), 'Missing implication closure')
                counters['step'] += 1
        for l in fixed:
            extended = support | {l}
            if len(extended) <= 6 and below(rows[l], rows[b]):
                require(any(core <= extended for core in cores), 'Missing terminal obstruction')
                counters['terminal'] += 1
    for l in fixed:
        for u in fixed:
            if below(rows[l], rows[u]):
                require(any(core <= {l, u} for core in cores), 'Missing fixed-pair obstruction')
                counters['fixed_pair'] += 1
    histogram = dict(sorted(Counter(map(len, cores)).items()))
    require(histogram == {2: 27, 3: 18, 4: 6, 5: 204, 6: 504}, 'Core size counts differ')
    return rows, data['cores'], {'rows': 64, 'states': len(states), 'cores': len(cores),
                               'core_sizes': histogram, 'local_obligations': dict(counters),
                               'support_soundness_checked': True, 'core_minimality_checked': True}


def mask(pairs, row):
    return sum((1 << x if rank in (1, 2) else 0) + (1 << y if rank in (2, 3) else 0)
               for (x, y), rank in zip(pairs, row))


def catalogue(k, canonical=None):
    pairs = pairings(k)
    cores, ids, templates = [], {}, []
    for pairing in pairs:
        if k == 3:
            row_values, canonical_cores = canonical
            # Ordering deliberately agrees with the archived full-CNF generator.
            local = [tuple(sorted(mask(pairing, row_values[i]) for i in core)) for core in canonical_cores]
        else:
            local = set()
            for types in product(((1, 2), (1, 3), (2, 3)), repeat=4):
                local.add(tuple(sorted((mask(pairing, [r[0] for r in types]),
                                        mask(pairing, [r[1] for r in types])))))
            for j, (x, y) in enumerate(pairing):
                center = 255 ^ (1 << x) ^ (1 << y)
                for a in (1, 2, 3):
                    for b in (1, 2, 3):
                        if a >= b:
                            lower, upper = [1] * 4, [3] * 4
                            lower[j], upper[j] = a, b
                            local.add(tuple(sorted((mask(pairing, lower), mask(pairing, upper), center))))
            local = sorted(local)
        require(len(local) == len(set(local)) == (759 if k == 3 else 105), 'Wrong template size')
        # The rank-to-neighbourhood correspondence is a bijection for every pairing.
        require(len({mask(pairing, row) for row in product(range(4), repeat=k)}) == 4**k,
                'Rank/mask transformation not bijective')
        template = []
        for core in local:
            if core not in ids:
                ids[core] = len(cores)
                cores.append(core)
            template.append(ids[core])
        templates.append(template)
    expected = 38430 if k == 3 else 4935
    require(len(cores) == expected, 'Wrong global catalogue size')
    if k == 4:
        require(Counter(map(len, cores)) == {2: 2415, 3: 2520}, 'Wrong four-pair core sizes')
    return cores, templates, pairs


def formula(k, cores, templates):
    universe, limit = 2 ** (2 * k), 2 * k
    variables, clauses = [], []
    def variable(name):
        variables.append(name)
        return len(variables)
    def add(*literals):
        if not any(-x in literals for x in literals):
            clauses.append(list(dict.fromkeys(literals)))
    selectors = [variable(f'select_{m}') for m in range(universe)]
    falsum = variable('false')
    add(-falsum)
    counts = {}
    def count(i, j):
        return -falsum if j == 0 else falsum if j > i else counts[i, j]
    for i in range(1, universe + 1):
        for j in range(1, min(i, limit + 1) + 1):
            z = counts[i, j] = variable(f'count_{i}_{j}')
            u, x, w = count(i - 1, j), selectors[i - 1], count(i - 1, j - 1)
            add(-u, z); add(-x, -w, z); add(-z, u, x); add(-z, u, w)
    add(-count(universe, limit + 1))
    permutations = []
    for a in range(2 * k - 1):
        p = list(range(2 * k)); p[a], p[a + 1] = p[a + 1], p[a]
        permutations.append(p)
    permutations += [list(range(a, 2 * k)) + list(range(a)) for a in range(1, 2 * k)]
    for t, p in enumerate(permutations):
        require(sorted(p) == list(range(2 * k)), 'Invalid coordinate permutation')
        previous = -falsum
        for m in reversed(range(universe)):
            image = sum(((m >> a) & 1) << p[a] for a in range(2 * k))
            if image != m:
                x, y = selectors[m], selectors[image]
                add(-previous, x, -y)
                z = variable(f'lex_{t}_{m}')
                add(-z, previous); add(-z, -x, y); add(-z, x, -y)
                add(-previous, -x, -y, z); add(-previous, x, y, z)
                previous = z
    core_variables = [variable(f'core_{c}') for c in range(len(cores))]
    for c, core in enumerate(cores):
        for m in core:
            add(-core_variables[c], selectors[m])
    for template in templates:
        add(*(core_variables[c] for c in template))
    clauses.insert(0, list(range(1, len(variables) + 1)))
    return variables, clauses


def cnf_hash(variables, clauses, newline='\n'):
    checksum = hashlib.sha256(f'p cnf {variables} {len(clauses)}{newline}'.encode('ascii'))
    for clause in clauses:
        checksum.update((' '.join(map(str, clause)) + ' 0' + newline).encode('ascii'))
    return checksum.hexdigest()


def parse_cnf(path):
    clauses, pending = [], []
    variables = promised = None
    with path.open(encoding='ascii') as stream:
        for line in stream:
            tokens = line.split()
            if not tokens or tokens[0] == 'c':
                continue
            if tokens[0] == 'p':
                require(variables is None and len(tokens) == 4 and tokens[1] == 'cnf', 'Bad CNF header')
                variables, promised = map(int, tokens[2:])
                require(variables > 0 and promised >= 0, 'Bad CNF dimensions')
                continue
            require(variables is not None, 'CNF data before header')
            for token in tokens:
                literal = int(token)
                if literal:
                    require(1 <= abs(literal) <= variables, 'Out-of-range CNF literal')
                    pending.append(literal)
                else:
                    require(len(pending) == len(set(pending)) and not (set(pending) & {-x for x in pending}),
                            'Duplicate or tautological CNF clause')
                    clauses.append(pending)
                    pending = []
    require(not pending and variables is not None and len(clauses) == promised, 'CNF count/termination error')
    return variables, clauses


def hint_check(clause, hints, database):
    """Boolean assignments, implemented independently of the producer's literal-set checker."""
    assignment = {abs(literal): literal < 0 for literal in clause}  # negate learned clause
    for index, ident in enumerate(hints):
        require(0 < ident < len(database), 'Hint cites future/missing clause')
        undecided = []
        for literal in database[ident]:
            value = assignment.get(abs(literal))
            require(value is None or value != (literal > 0), 'Hint clause is already satisfied')
            if value is None:
                undecided.append(literal)
        require(len(undecided) <= 1, 'Hint clause is not unit or conflicting')
        if not undecided:
            require(index == len(hints) - 1, 'Hints continue after conflict')
            return
        literal = undecided[0]
        assignment[abs(literal)] = literal > 0
    raise ValueError('Hints do not conclude with contradiction')


def check_lrat(variables, clauses, path):
    database = [None] + clauses
    additions = references = 0
    with path.open(encoding='ascii') as stream:
        for line_number, line in enumerate(stream, 1):
            words = line.split()
            require(words and all(repr(int(w)) == w for w in words), f'Non-canonical LRAT syntax line {line_number}')
            data = list(map(int, words))
            require(data.count(0) == 2 and data[-1] == 0, 'LRAT needs exactly two delimiters')
            delimiter = data.index(0)
            ident, clause, hints = data[0], data[1:delimiter], data[delimiter + 1:-1]
            require(ident == len(database) and hints and all(0 < h < ident for h in hints), 'Invalid LRAT IDs')
            require(all(1 <= abs(x) <= variables for x in clause) and len(clause) == len(set(clause))
                    and not (set(clause) & {-x for x in clause}), 'Malformed learned clause')
            hint_check(clause, hints, database)
            database.append(clause)
            additions += 1
            references += len(hints)
    require(additions > 0 and database[-1] == [], 'LRAT does not finish with the empty clause')
    return {'additions': additions, 'hint_references': references, 'final_empty_clause': True}


def arithmetic():
    def matching(k, x, y, z):
        if min(k, x, y, z) < 0 or x + y + z != 2*k or max(x, y, z) > k:
            return 0
        numerator = factorial(x)*factorial(y)*factorial(z)
        denominator = factorial(k-x)*factorial(k-y)*factorial(k-z)
        require(numerator % denominator == 0, 'Nonintegral factorial count')
        return numerator // denominator
    def p(k, x, y, z, t):
        if t == 0:
            return 2*matching(k,x,y,z)+y*(y-1)*matching(k-1,x,y-2,z)+x*(x-1)*matching(k-1,x-2,y,z)
        if t == 1:
            return 2*y*matching(k-1,x,y-1,z)+2*x*matching(k-1,x-1,y,z)
        return 0
    expected = {(6,0):[5040,5040,7200,8640,8064,5040,1440],
                (6,1):[1440,2400,2880,3456,2880,1440,0],
                (7,0):[40320,40320,60480,79200,86400,72000,40320,10080],
                (7,1):[10080,17280,21600,28800,28800,23040,10080,0]}
    tables = {}
    for (k,t), claimed in expected.items():
        maxima = [max(p(k,x,2*k-t-z-x,z,t) for x in range(2*k-t-z+1)) for z in range(2*k-t+1)]
        require(maxima[:k+1] == claimed and not any(maxima[k+1:]), 'Per-z table mismatch')
        tables[f'{k},{t}'] = maxima
    five = [(x,y,10-x-y,matching(5,x,y,10-x-y)) for x in range(11) for y in range(11-x)]
    require(max(t[3] for t in five) == 216, 'Five-pair maximum mismatch')
    q = {k: factorial(2*k)//factorial(k) for k in (5,6,7)}
    require(q == {5:30240,6:665280,7:17297280}, 'Matching denominator mismatch')
    require(max(d*comb(10-d,2) for d in range(11)) == 63, 'Triple count maximum mismatch')
    require(Fraction(2*216,q[5]) == Fraction(1,70), 'Five-pair pair probability mismatch')
    require(Fraction(2,9*comb(8,4)) == Fraction(1,315), 'Five-pair triple probability mismatch')
    require(Fraction(45,70)+Fraction(63,315) == Fraction(59,70) < 1, 'Five-pair union bound mismatch')
    ratios = {str(k): str(Fraction(max(max(tables[f'{k},{t}']) for t in (0,1)),q[k])) for k in (6,7)}
    require(ratios == {'6':'1/77','7':'5/1001'}, 'Probability ratio mismatch')
    unions = {str(k): Fraction(comb(2*k,2))*Fraction(ratios[str(k)]) for k in (6,7)}
    require(unions == {'6':Fraction(6,7),'7':Fraction(5,11)} and all(v<1 for v in unions.values()),
            'Six/seven-pair union bound mismatch')
    five_sorted = {(x,y,z):value for x,y,z,value in five if x<=y<=z<=5}
    require(five_sorted == {(0,5,5):120,(1,4,5):120,(2,3,5):120,(2,4,4):192,(3,3,4):216},
            'Five-pair factorial table mismatch')
    return {'all_per_z_maxima_including_omitted_zeros': tables, 'Q':q, 'probability_maxima':ratios,
            'union_bounds':{k:str(v) for k,v in unions.items()},
            'M5_sorted_table':{str(k):v for k,v in five_sorted.items()},
            'M5_maximum':216, 'five_pair_pair_probability':'1/70',
            'five_pair_triple_probability':'1/315', 'triple_count_d_domain':list(range(11)),
            'five_pair_union_bound':'59/70'}


def checker_controls(executable, destination):
    # Positive and negative controls test execution, not general compiler correctness.
    cnf = destination/'control.cnf'; proof = destination/'control.rup'
    cnf.write_text('p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n',encoding='ascii')
    proof.write_text('1 0\n0\n',encoding='ascii')
    good = subprocess.run([str(executable),str(cnf),str(proof)],capture_output=True,text=True)
    require(good.returncode == 0, 'RUP positive control rejected')
    cnf.write_text('p cnf 2 1\n1 2 0\n',encoding='ascii')
    proof.write_text('0\n',encoding='ascii')
    bad = subprocess.run([str(executable),str(cnf),str(proof)],capture_output=True,text=True)
    require(bad.returncode != 0, 'RUP negative control accepted')
    try:
        hint_check([], [1], [None,[1,2]])
    except ValueError:
        pass
    else:
        raise ValueError('LRAT negative control accepted')
    hint_check([], [1,2], [None,[1],[-1]])
    return {'rup_positive':good.stdout.strip(),'rup_negative':bad.stderr.strip(),
            'rup_negative_exit':bad.returncode,'lrat_positive_and_negative_passed':True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cxx',default='g++')
    args = parser.parse_args()
    run = ROOT/'build'/'validation'/('run-'+time.strftime('%Y%m%dT%H%M%SZ',time.gmtime())+'-'+uuid.uuid4().hex[:8])
    run.mkdir(parents=True)
    report = {'status':'running','scope':'Finite certificate and exact arithmetic verification',
              'command':[Path(sys.executable).name,'verify.py',*sys.argv[1:]], 'cwd':'.', 'python':sys.version,'platform':platform.platform(),
              'started_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()), 'steps':{}}
    started = time.monotonic()
    log = (run/'verification.log').open('x',encoding='utf-8')
    def announce(message):
        print(message,flush=True);log.write(message+'\n');log.flush()
    def checkpoint():
        (run/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    try:
        inputs = [DATA/'pairing6.cnf',DATA/'pairing6.lrat',DATA/'pairing6-provenance.json',DATA/'three-pair-closure.json',
                  OLD/'pairing8.cnf',OLD/'pairing8.rup.gz',ROOT/'check_rup.cpp',ROOT/'check_rup_counters.cpp',Path(__file__).resolve()]
        report['input_sha256'] = {p.relative_to(ROOT).as_posix():digest(p) for p in inputs};checkpoint()
        rows, cores, result = check_closure();report['steps']['closure']=result;announce('PASS three-pair local closure coverage and support/core soundness');checkpoint()
        c3,t3,p3 = catalogue(3,(rows,cores));v3,f3 = formula(3,c3,t3)
        provenance = json.loads((DATA/'pairing6-provenance.json').read_bytes())
        expected_full = provenance['full_formula_sha256']
        # The historical full formula was generated on Windows with CRLF lines.
        require((len(v3),len(f3)) == (39382,222795) and cnf_hash(len(v3),f3,'\r\n')==expected_full,'Full three-pair formula regeneration mismatch')
        n6,reduced = parse_cnf(DATA/'pairing6.cnf');indices=provenance['original_clause_indices_one_based']
        require(n6==len(v3) and len(reduced)==141926 and len(indices)==len(reduced) and indices==sorted(set(indices)), 'Bad reduced clause map')
        require(all(1<=i<=len(f3) and c==f3[i-1] for i,c in zip(indices,reduced)), 'Reduced clause is not its indexed original')
        report['steps']['three_pair_formula']={'variables':len(v3),'full_clauses':len(f3),'reduced_clauses':len(reduced),'full_sha256':expected_full,'templates':len(t3),'global_cores':len(c3),'all_reduced_clauses_are_exact_indexed_members':True}
        announce('PASS full three-pair CNF regeneration and exact reduced-clause membership');checkpoint()
        del f3,v3,c3,t3
        result=check_lrat(n6,reduced,DATA/'pairing6.lrat')
        require(result['additions']==3305 and result['hint_references']==provenance['hint_references'],'LRAT inventory mismatch')
        report['steps']['three_pair_lrat']=result;announce('PASS all 3305 positive-hint LRAT additions through empty clause');checkpoint()
        del reduced
        c4,t4,p4=catalogue(4);v4,f4=formula(4,c4,t4)
        n4,original=parse_cnf(OLD/'pairing8.cnf')
        require(n4==len(v4)==10116 and len(f4)==38240 and original==f4,'Four-pair formula regeneration mismatch')
        report['steps']['four_pair_formula']={'variables':n4,'clauses':len(f4),'sha256':digest(OLD/'pairing8.cnf'),'templates':len(p4),'global_cores':len(c4),'exact_regeneration_matches':True}
        announce('PASS four-pair formula/catalogue regeneration');checkpoint()
        del original,f4,c4,t4,v4
        report['steps']['arithmetic']=arithmetic();announce('PASS exact factorial tables, all omitted z values, and five-pair maxima');checkpoint()
        exe=run/('check_rup.exe' if sys.platform=='win32' else 'check_rup')
        command=[args.cxx,'-O3','-std=c++17','check_rup.cpp','-o',exe.relative_to(ROOT).as_posix()]
        compiled=subprocess.run(command,cwd=ROOT,capture_output=True,text=True)
        report['compiler']={'command':command,'exit_code':compiled.returncode,'stdout':compiled.stdout,'stderr':compiled.stderr}
        require(compiled.returncode==0,'C++ checker compilation failed')
        report['steps']['checker_controls']=checker_controls(exe,run)
        unpacked=run/'pairing8.rup';line_count=0
        with gzip.open(OLD/'pairing8.rup.gz','rt',encoding='ascii') as stream,unpacked.open('x',encoding='ascii') as out:
            last=None
            for line in stream:
                data=list(map(int,line.split()));require(data and data[-1]==0 and data.count(0)==1 and all(1<=abs(x)<=n4 for x in data[:-1]),'Malformed four-pair RUP')
                require(len(data[:-1])==len(set(data[:-1])) and not (set(data[:-1]) & {-x for x in data[:-1]}),'Duplicate/tautological RUP')
                out.write(line);line_count+=1;last=data
        require(line_count==34482 and last==[0],'Four-pair trace must end in empty clause')
        command=[exe.relative_to(ROOT).as_posix(),'data/pairing8.cnf',unpacked.relative_to(ROOT).as_posix()]
        checked=subprocess.run(command,cwd=ROOT,capture_output=True,text=True)
        report['steps']['four_pair_rup']={'command':command,'exit_code':checked.returncode,'stdout':checked.stdout,'stderr':checked.stderr,'strict_trace_lines':line_count}
        require(checked.returncode==0 and json.loads(checked.stdout)['verified_unsat'] is True,'Four-pair RUP failed')
        announce('PASS four-pair watched-literal RUP contradiction check');checkpoint()
        exe2=run/('check_rup_counters.exe' if sys.platform=='win32' else 'check_rup_counters')
        command=[args.cxx,'-O3','-std=c++17','check_rup_counters.cpp','-o',exe2.relative_to(ROOT).as_posix()]
        compiled=subprocess.run(command,cwd=ROOT,capture_output=True,text=True)
        report['counter_compiler']={'command':command,'exit_code':compiled.returncode,'stdout':compiled.stdout,'stderr':compiled.stderr}
        require(compiled.returncode==0,'Second C++ checker compilation failed')
        report['steps']['counter_checker_controls']=checker_controls(exe2,run)
        command=[exe2.relative_to(ROOT).as_posix(),'data/pairing8.cnf',unpacked.relative_to(ROOT).as_posix()]
        checked=subprocess.run(command,cwd=ROOT,capture_output=True,text=True)
        report['steps']['four_pair_rup_counters']={'command':command,'exit_code':checked.returncode,'stdout':checked.stdout,'stderr':checked.stderr}
        require(checked.returncode==0 and json.loads(checked.stdout)['verified_unsat'] is True,'Four-pair occurrence-count RUP failed')
        announce('PASS four-pair occurrence-count RUP contradiction check');checkpoint()
        require(all(digest(p)==report['input_sha256'][p.relative_to(ROOT).as_posix()] for p in inputs),'Input changed during verification')
        report.update(status='all_checks_passed',elapsed_seconds=round(time.monotonic()-started,3))
        checkpoint();announce('ALL CHECKS PASSED; report '+(run/'report.json').relative_to(ROOT).as_posix())
    except BaseException:
        report.update(status='failed',error=traceback.format_exc(),elapsed_seconds=round(time.monotonic()-started,3));checkpoint();log.write(report['error']);raise
    finally:
        log.close()


if __name__=='__main__':
    main()
