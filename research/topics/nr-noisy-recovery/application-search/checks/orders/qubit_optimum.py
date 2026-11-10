"""Exact flag-heralded identity optimum for all once-each slot permutations."""
import sympy as s
import json
from pathlib import Path
from exact_certificates import matrices,accept,sign

def main():
    out={}
    for m in (1,2,3,4):
        ps,A,B=matrices(m,2)
        A=s.Matrix([[s.Rational(v.numerator,v.denominator) for v in row] for row in A])
        B=s.Matrix([[s.Rational(v.numerator,v.denominator) for v in row] for row in B])
        vv=B.nullspace()
        if vv:
            N=s.Matrix.hstack(*vv);P=N*(N.T*N).inv()*N.T
        else:P=s.zeros(len(ps))
        val=s.factor(s.trace(P*A)/len(ps))
        # Positivity of A on this kernel follows from Choi positivity;
        # exact spectrum is also computed here.
        ev={str(k):int(v) for k,v in (P*A*P).eigenvals().items()}
        out[f'd2_m{m}']={'nullity_B':len(vv),'max_exact_heralded_p':str(val),'restricted_A_spectrum':ev}
    assert out['d2_m4']['max_exact_heralded_p']=='3/64'
    assert all(out[f'd2_m{m}']['max_exact_heralded_p']=='0' for m in (1,2,3))
    import itertools
    from fractions import Fraction as F
    ps=list(itertools.permutations(range(3)))
    r=accept(3,2,ps,[F(sign(p),6) for p in ps])
    assert r['p']=='1/8' and r['F']=='3/4'
    out['d2_m3_alternating']=r
    Path(__file__).with_name('qubit_optimum.json').write_text(json.dumps(out,indent=2))
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
