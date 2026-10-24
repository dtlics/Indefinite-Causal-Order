"""Independent exact coefficient guards for the thermal mean BS operator.

The full trace identity and history pairing are analytic in the sibling
note. This finite replay is not a Fock truncation of a thermal channel.
"""
from fractions import Fraction as F
from math import comb
from math import factorial
from itertools import product
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def diagonal(m, n, t):
    return sum(F((-1)**k*comb(m,k)*comb(n,k))*t**(m+n-2*k)
               *(1-t*t)**k for k in range(min(m,n)+1))


def coefficient(m, n, t):
    # Coefficient of z^n in (1-z)(t-z)^m/(1-zt)^(m+1).
    def base(n0):
        if n0 < 0:
            return F(0)
        return sum(F((-1)**k*comb(m,k))*t**(m-k)
                   *F(comb(m+n0-k,n0-k))*t**(n0-k)
                   for k in range(min(m,n0)+1))
    return base(n)-base(n-1)


def _plus(a, b, factor=F(1)):
    out=dict(a)
    for key,value in b.items():
        out[key]=out.get(key,F(0))+factor*value
        if not out[key]:
            del out[key]
    return out


def _bs(vector, bath, t=F(3,5), s=F(4,5)):
    """Literal creation-polynomial action; output basis norm is product n!."""
    require(t*t+s*s==1,"unitary beam splitter")
    out={}
    for occ,value in vector.items():
        p,q=occ[0],occ[bath]
        for k in range(p+1):
            for l in range(q+1):
                target=list(occ)
                target[0],target[bath]=k+l,p+q-k-l
                target=tuple(target)
                amplitude=(value*comb(p,k)*comb(q,l)*t**k*(-s)**(p-k)
                           *s**l*t**(q-l))
                out[target]=out.get(target,F(0))+amplitude
    return {key:value for key,value in out.items() if value}


def _word(signal, baths, word):
    occ=(signal,)+baths
    vector={occ:F(1)}
    for bath in word:
        vector=_bs(vector,bath)
    require(all(sum(key)==sum(occ) for key in vector),"complete number sector")
    norm=sum(value*value*F(factorial(key[0]))
             *F(factorial(key[1])*factorial(key[2])*factorial(key[3])*factorial(key[4]))
             for key,value in vector.items())
    require(norm==1,"literal full-output isometry column")
    return vector


def _trace_baths(left, right):
    # Coefficients multiply unnormalized signal |m><n|; tracing the bath
    # contributes product n!, and no output occupation is discarded.
    out={}
    for a,x in left.items():
        for b,y in right.items():
            if a[1:]==b[1:]:
                weight=F(1)
                for n in a[1:]:
                    weight*=factorial(n)
                key=(a[0],b[0])
                out[key]=out.get(key,F(0))+x*y*weight
    return {key:value for key,value in out.items() if value}


def finite_record_guards():
    """Finite NON-Gaussian bath fixture; no oscillator-output truncation."""
    # Four records label A_early,A_late,B_early,B_late. Each source is
    # p0|0><0|+(1-p0)|1><1| with its orthogonal input-number purifier.
    # Unused windows are gated identities. The source is not tau_thermal.
    words=((1,4),(3,2),(1,3),(2,4),(3,1),(4,2))
    # Native 0/1; ordinary forward 0/1; ordinary reverse 0/1.
    source_inputs=tuple(product((0,1),repeat=4))
    vectors={(s,baths,word):_word(s,baths,word)
             for s in (0,1) for baths in source_inputs for word in words}
    trace_cache={}
    def block(c,d,s,u,pair,p0a,p0b):
        total={}
        for baths in source_inputs:
            weight=F(1)
            for j,n in enumerate(baths):
                p0=p0a if j<2 else p0b
                weight*=p0 if n==0 else 1-p0
            key=(s,u,baths,pair[c],pair[d])
            if key not in trace_cache:
                trace_cache[key]=_trace_baths(vectors[(s,baths,pair[c])],
                                             vectors[(u,baths,pair[d])])
            total=_plus(total,trace_cache[key],weight)
        return total
    native,forward,reverse=words[:2],words[2:4],words[4:]
    full_units=cross_units=0
    p0a=p0b=F(2,3)
    mean=lambda m,p0:p0*diagonal(m,0,F(3,5))+(1-p0)*diagonal(m,1,F(3,5))
    for c,d,s,u in product((0,1),repeat=4):
        actual=block(c,d,s,u,native,p0a,p0b)
        ordinary=block(c,d,s,u,forward,p0a,p0b)
        require(actual==ordinary,"full C/signal fresh-clock ordinary equality")
        full_units+=1
        if c!=d:
            target={(s,u):mean(s,p0a)*mean(s,p0b)*mean(u,p0a)*mean(u,p0b)}
            target={key:value for key,value in target.items() if value}
            require(actual==target,"literal fresh-clock thermal-mean cross map")
            cross_units+=1
    # Unequal bath mixtures generally have noncommuting serial channels.
    # Compare only initial-helper+ followed by measured X, coarse-graining
    # the ordinary fair order coin. Every map remains subnormalized.
    p0a,p0b=F(2,3),F(1,4)
    x_units=0
    def xmap(pair,sign,s,u):
        out={}
        for c,d in product((0,1),repeat=2):
            out=_plus(out,block(c,d,s,u,pair,p0a,p0b),
                      F(1,4)*(sign if c!=d else 1))
        return out
    require(block(0,0,0,0,native,p0a,p0b)!=block(1,1,0,0,native,p0a,p0b),
            "unequal finite sources have genuinely different ordered diagonals")
    for sign,s,u in product((1,-1),(0,1),(0,1)):
        ordinary=_plus({},xmap(forward,sign,s,u))
        ordinary=_plus(ordinary,xmap(reverse,sign,s,u))
        ordinary={key:value/2 for key,value in ordinary.items()}
        require(xmap(native,sign,s,u)==ordinary,"measured-X faircoin full signal map")
        x_units+=1
    return {"finite_source_isometry_columns":len(vectors),
            "full_C_signal_matrix_units":full_units,
            "literal_mean_cross_units":cross_units,
            "unequal_source_measured_X_matrix_units":x_units,
            "maximum_total_photons":5,
            "scope":"Finite diagonal 0/1 bath mixtures, rational physical BS, gated idle windows, all output occupations and input-number purifiers retained before trace; not a finite-temperature Gaussian bath or bath-output equality."}


def verify():
    count=0
    for t in (F(0),F(3,5),F(4,5),F(1)):
        for m in range(7):
            for n in range(9):
                # The thermal weight (1-z) gives adjacent diagonal difference.
                physical=diagonal(m,n,t)-(diagonal(m,n-1,t) if n else 0)
                require(physical == coefficient(m,n,t), "literal BS thermal coefficient")
                count+=1
    t,z=F(3,5),F(1,2)
    alpha,beta=(1-z)/(1-z*t),(t-z)/(1-z*t)
    require((alpha,beta)==(F(5,7),F(1,7)),"thermal mean parameters")
    fresh=(1-alpha**4)/2
    occupation=z/(1-z)
    d=1+2*occupation*(1-t)*(1-t*t)+occupation**2*(1-t*t)**2
    standard=(1-1/d)/2
    require(fresh==F(888,2401) and standard==F(288,1201),"vacuum record-pairing falsifier")
    require(fresh!=standard,"distinct instruments")
    t0,z0=F(1,5),F(3,4)
    require((t0-z0)/(1-z0*t0)==F(-11,17),"negative thermal mean beta retained")
    # The offdiagonal reference unit |0><1| retains the sign that the
    # control-only visibility squares away. These are full-thermal means.
    ca,za,cb,zb=F(3,5),F(4,5),F(4,5),F(0)
    aa,ba=(1-za)/(1-za*ca),(ca-za)/(1-za*ca)
    ab,bb=(1-zb)/(1-zb*cb),(cb-zb)/(1-zb*cb)
    k0,k1=aa*ab,aa*ab*ba*bb
    require(k0*k1==F(-100,2197),"negative-beta reference cross coherence")
    return {"status":"passed","literal_thermal_coefficients":count,
            "negative_beta_cross_coherence":str(k0*k1),
            "fresh_clock_vacuum_minus":str(fresh),
            "standard_module_vacuum_minus":str(standard),
            "finite_record_guard":finite_record_guards(),
            "scope":"Exact finite coefficients plus analytic full-thermal trace/history proof; gated unused windows only. No physical router, recovery, bath-output equivalence or hardware claim."}


if __name__ == "__main__":
    print(json.dumps(verify(),sort_keys=True,indent=2))
