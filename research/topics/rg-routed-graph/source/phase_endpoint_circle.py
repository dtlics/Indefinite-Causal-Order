"""Exact Laurent Gram investigation of the entire phase circle."""
from pathlib import Path
from itertools import product
import json
import numpy as np
import sympy as s
from phase_endpoint_exact import row_tensor, coefficient_table, specialize, LABELS, WORDS
ROOT = Path(__file__).parent
z = s.Symbol('z')
t = s.Symbol('t', real=True)


def laurent_table(which):
    T = row_tensor(which, 1)
    masks = np.zeros((16,16), dtype=np.int64)
    for r, o in enumerate(WORDS):
        for a, n in enumerate(WORDS):
            if which == 4:
                masks[r,a] = int(o[1] == 0 and ((n[0] == 0 and n[3] == 0) or (n[0] == 1 and n[2] == 0)))
            else:
                masks[r,a] = int(o[3] == 0 and (n[2] == 0 or (n[0] == 0 and n[1] == 1 and n[2] == 1)))
    exponent = masks[:,:,None]-masks.diagonal()[None,None,:]
    return {e: coefficient_table(T*(exponent == e)) for e in [-1,0,1]}


def grams_for(which, i, side='last'):
    coeff = laurent_table(which)
    others = [j for j in range(4) if j != i]
    singles = {e: specialize(c,[i]) for e,c in coeff.items()}
    bars = {e: specialize(c,others) for e,c in coeff.items()}
    assert all(np.max(np.abs(m)) <= 4 for units in singles.values() for m in units.values())
    assert all(np.max(np.abs(m)) <= 4 for entries in bars.values() for m in entries.values())
    grams = {e:np.zeros((16,16),dtype=np.int64) for e in range(-4,5)}
    for lab in LABELS:
        D = {e:np.zeros((16,16),dtype=np.int64) for e in range(-2,3)}
        for e in [-1,0,1]: D[e] += 4*coeff[e][lab]
        for e,f in product([-1,0,1],repeat=2):
            A=singles[e][(lab[i],)];B=bars[f][tuple(lab[j] for j in others)]
            D[e+f] -= A@B if side == 'last' else B@A
        # A uniform a priori bound: each D coefficient has at most three
        # products, each with sixteen terms bounded by 4*4, plus 4*4.
        assert all(np.max(np.abs(d)) <= 784 for d in D.values())
        for e,f in product(range(-2,3),repeat=2):
            if side == 'last': grams[e-f] += D[e] @ D[f].T
            else: grams[f-e] += D[e].T @ D[f]
    assert 256*25*16*784**2 < 2**63
    assert all(np.array_equal(grams[e],grams[-e].T) for e in range(-4,5))
    return grams


def components(grams):
    adj = np.zeros((16,16),dtype=bool)
    for g in grams.values(): adj |= g != 0
    unseen = set(range(16));out=[]
    while unseen:
        block={unseen.pop()};front=list(block)
        while front:
            a=front.pop()
            for b in list(unseen):
                if adj[a,b]: unseen.remove(b);block.add(b);front.append(b)
        out.append(sorted(block))
    return out


def symmetric_laurent_to_real(poly):
    """Exact substitution t=z+z^-1 for a reciprocal Laurent polynomial."""
    terms = {}
    for term in s.Add.make_args(s.expand(poly)):
        power = int(term.as_powers_dict().get(z, 0))
        coefficient = s.cancel(term/z**power)
        assert not coefficient.has(z)
        terms[power] = terms.get(power, 0)+coefficient
    assert all(terms.get(k,0) == terms.get(-k,0) for k in terms)
    out = terms.get(0,0)
    for k in range(1,max([abs(k) for k in terms]+[0])+1):
        out += 2*terms.get(k,0)*s.chebyshevt(k,t/2)
    assert s.cancel(out.subs(t,z+1/z)-poly) == 0
    return s.factor(out)


if __name__ == '__main__':
    out=[]
    for which,i in product([4,5],range(4)):
        gram = grams_for(which,i)
        blocks=components(gram)
        record={'projector_rank':which,'query':i+1,'blocks':[]}
        for block in blocks:
            G=s.Matrix(len(block),len(block),lambda a,b:sum(int(g[block[a],block[b]])*z**e for e,g in gram.items()))
            det=s.factor(G.det(method='domain-ge'))
            realdet=symmetric_laurent_to_real(det)
            P=s.Poly(realdet,t)
            zeros=int(P.count_roots(-2,2)) if P.degree()>0 else 0
            assert zeros == 0 and realdet.subs(t,-2)>0 and realdet.subs(t,2)>0
            print('rank',which,'query',i+1,'block',block,'det',det,flush=True)
            record['blocks'].append({'indices':block,'determinant':str(det),
                'determinant_in_t':str(realdet),
                'exact_real_root_count_on_minus2_plus2':zeros,
                'value_at_minus2':str(realdet.subs(t,-2)),
                'value_at_plus2':str(realdet.subs(t,2)),
                'strictly_positive_on_entire_interval':True})
        out.append(record)
        (ROOT/'phase_endpoint_circle_checks.json').write_text(json.dumps({'status':'PASS' if len(out)==8 else 'RUNNING',
            'results':out,'conclusion':'Every phase of both normalized families has zero last-query support at every port.',
            'method':'Full matrix-unit coefficient Gram; exact Laurent determinants; rational Sturm root counts on [-2,2].',
            'scope':'Entire phase circle; no routed-host realization or exclusion is inferred.'},indent=2)+'\n')
    print('PASS: all eight last-Gram matrices are nonsingular on the entire unit circle.',flush=True)
