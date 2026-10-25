"""Exact finite feedback guards, extended to full even-ring Hilbert spaces.

The costs and physical interface assumptions remain explicit. No scalable
cooling advantage, general receiver optimum or physical router is proved.
The original three-site fixture is retained unchanged in its own verifier.
"""
from fractions import Fraction as F
from itertools import product
from math import comb
import json


def require(test, message):
    if not test:
        raise RuntimeError(message)


def zero():
    return [[F(0) for _ in range(3)] for _ in range(3)]


def eye():
    return [[F(i == j) for j in range(3)] for i in range(3)]


def add(a, b, weight=F(1)):
    return [[a[i][j]+weight*b[i][j] for j in range(3)] for i in range(3)]


def scale(a, weight):
    return [[weight*v for v in row] for row in a]


def mul(a, b):
    return [[sum(a[i][k]*b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


def adj(a):
    return [list(row) for row in zip(*a)]


def diag(v):
    return [[F(v[i] if i == j else 0) for j in range(3)] for i in range(3)]


def permutation(v):
    return [[F(i == v[j]) for j in range(3)] for i in range(3)]


def ad(k, rho):
    return mul(mul(k, rho), adj(k))


def channel(kraus, rho):
    out=zero()
    for k in kraus:
        out=add(out,ad(k,rho))
    return out


def ground_mass(rho):
    return sum(sum(row) for row in rho)/3


def bond(i, j):
    p=zero()
    p[i][i]=p[j][j]=F(1,2)
    p[i][j]=p[j][i]=F(-1,2)
    z=[1,1,1];z[i]=-1
    return p,(add(eye(),p,-1),mul(diag(z),p))


def verify_three_site_fixture():
    G=[[F(1,3) for _ in range(3)] for _ in range(3)]
    pa,a=bond(0,1)
    pb,b=bond(1,2)
    local_units=0
    for p,ks in ((pa,a),(pb,b)):
        effect=pumped=zero()
        for k in ks:
            effect=add(effect,mul(adj(k),k))
            pumped=add(pumped,mul(mul(adj(k),G),k))
        require(effect==eye(),'Local update is not CPTP.')
        require(channel(ks,G)==G,'Local update does not fix the ground.')
        require(pumped==add(G,scale(p,F(2,3))),'Ground pumping identity failed.')
        for r,s in product(range(3),repeat=2):
            unit=zero();unit[r][s]=F(1)
            require(channel(ks,channel(ks,unit))==channel(ks,unit),'Local update is not idempotent.')
            local_units+=1

    # A clean helper measuring a controlled physical SWAP implements exactly
    # the source's A measurement plus feedback. It is a priced third update.
    swap=permutation((1,0,2))
    qp=scale(add(eye(),swap),F(1,2))
    qm=scale(add(eye(),swap,-1),F(1,2))
    corrected=mul(diag((-1,1,1)),qm)
    require(qp==a[0] and corrected==a[1],'Compiled check differs from source A.')
    check_units=0
    for r,s,index in product(range(3),range(3),range(2)):
        unit=zero();unit[r][s]=F(1)
        require(ad((qp,corrected)[index],unit)==ad(a[index],unit),
                'Complete flagged compiled-check instrument differs.')
        check_units+=1
    mixed=scale(eye(),F(1,3))
    site2=zero();site2[1][1]=F(1)
    pair13=zero()
    for r,s in product((0,2),repeat=2):
        pair13[r][s]=F(1,2)
    scores=[]
    for rho in (mixed,site2,pair13):
        out=channel(a,channel(b,channel(a,rho)))
        scores.append(ground_mass(out))
    require(scores==[F(8,9),F(11,12),F(23,24)],'Ordinary ABA witness scores changed.')
    require(channel(a,channel(b,channel(a,G)))==G,'Ordinary ABA is not ground fixing.')

    # One-shot coarse-read order selection is useful, but NOT stationary.
    q12,q3=diag((1,1,0)),diag((0,0,1))
    coarse=[mul(mul(bj,ai),q12) for ai,bj in product(a,b)]
    coarse += [mul(mul(ai,bj),q3) for ai,bj in product(a,b)]
    effect=zero()
    for k in coarse:
        effect=add(effect,mul(adj(k),k))
    require(effect==eye(),'Coarse-read order-selection instrument is not complete.')
    require(ground_mass(channel(coarse,mixed))==F(5,6),'Coarse-read mixed score failed.')
    require(ground_mass(channel(coarse,G))==F(5,6),'Coarse-read nonstationarity guard failed.')

    # The spatial involution exchanges the two known feedback channels.
    reflection=permutation((2,1,0))
    for index in range(2):
        require(mul(mul(reflection,a[index]),reflection)==scale(b[index],(-1)**index),
                'A-to-B covariance failed.')
        require(mul(mul(reflection,b[index]),reflection)==scale(a[index],(-1)**index),
                'B-to-A covariance failed.')

    # Standard paired-module SWITCH: both pointers start PURE |00> and stay
    # quantum accessible. On C=1, swap their output labels and apply Z on
    # both. This is a ready-input isometry equality, not an arbitrary-bath
    # unitary identity. No initial pointer SWAP is needed on pure |00>.
    ready_columns=[]
    for c,s in product(range(2),range(3)):
        ordinary={}
        native={}
        for i,j,k in product(range(2),range(2),range(3)):
            fixed=mul(b[j],a[i])
            actual=fixed if c==0 else mul(mul(reflection,fixed),reflection)
            pointer=(i,j) if c==0 else (j,i)
            sign=1 if c==0 else (-1)**(i+j)
            actual_key=(c,k,*pointer)
            ordinary[actual_key]=ordinary.get(actual_key,F(0))+sign*actual[k][s]
            expected=fixed if c==0 else mul(a[i],b[j])
            expected_key=(c,k,i,j)
            native[expected_key]=native.get(expected_key,F(0))+expected[k][s]
        ordinary={key:value for key,value in ordinary.items() if value}
        native={key:value for key,value in native.items() if value}
        require(ordinary==native,'Standard pure-ready-pointer isometry column differs.')
        ready_columns.append(ordinary)
    for i,j in product(range(6),repeat=2):
        overlap=sum(value*ready_columns[j].get(key,F(0))
                    for key,value in ready_columns[i].items())
        require(overlap==F(i==j),'Standard ready-pointer columns are not an isometry.')

    clock_units=0
    for c,d,r,s in product(range(2),range(2),range(3),range(3)):
        rho=zero();rho[r][s]=F(1)
        ordinary={}
        native={}
        for i,j in product(range(2),repeat=2):
            left0=mul(b[j],a[i])
            left1=mul(mul(reflection,left0),reflection)
            # Deliberate C dephasing after any nonzero actual source record.
            if c!=d and (i or j):
                continue
            pair=(left0,left1)
            value=mul(mul(pair[c],rho),adj(pair[d]))
            label=((i,0,0,j) if c==0 else (0,j,i,0))
            ordinary[label]=add(ordinary.get(label,zero()),value)
        # Literal four independent clean clock pointers, gated when unused.
        for i1,i2,j1,j2 in product(range(2),repeat=4):
            left=mul(b[j2],a[i1]) if i2==j1==0 else zero()
            right=mul(a[i2],b[j1]) if i1==j2==0 else zero()
            pair=(left,right)
            value=mul(mul(pair[c],rho),adj(pair[d]))
            if value!=zero():
                label=(i1,i2,j1,j2)
                native[label]=add(native.get(label,zero()),value)
        ordinary={k:v for k,v in ordinary.items() if v!=zero()}
        native={k:v for k,v in native.items() if v!=zero()}
        require(ordinary==native,'Full C/signal/classical-clock matrix unit differs.')
        clock_units+=1
    return {'status':'passed','local_feedback_cases':2,'local_idempotence_matrix_units':local_units,
            'compiled_third_check_instrument_units':check_units,
            'ordinary_ABA_ground_mass':list(map(str,scores)),
            'coarse_read_mixed_ground_mass':'5/6','coarse_read_ground_input_ground_mass':'5/6',
            'standard_pure_ready_pointer_isometry_columns':len(ready_columns),
            'fresh_clock_full_C_signal_classical_record_matrix_units':clock_units,
            'scope':'Exact three-site one-excitation source-channel identities; two update calls '
                    'plus a compiled third feedback check are distinct resource currencies. '
                    'The standard compiler assumes pure ready quantum pointers and controlled '
                    'pointer SWAP/phases; it is not an arbitrary incoming-bath unitary identity. '
                    'The fresh-clock compiler compares full retained C/signal and relabelled classical '
                    'pointer records; additional authentic module/time logs need separate matching. '
                    'It does not compare coherent four-pointer outputs, inaccessible emissions or future baths. '
                    'No scalable cooling, ordinary optimum or hardware advantage certificate.'}


def s_clean(a):
    return {key:value for key,value in a.items() if value}


def s_eye(n):
    return {(i,i):F(1) for i in range(1<<n)}


def s_scale(a, weight):
    return s_clean({key:weight*value for key,value in a.items()})


def s_add(a, b, weight=F(1)):
    out=dict(a)
    for key,value in b.items():
        out[key]=out.get(key,F(0))+weight*value
    return s_clean(out)


def s_adj(a):
    return {(j,i):value for (i,j),value in a.items()}


def s_mul(a, b):
    by_column={}
    for (i,k),value in a.items():
        by_column.setdefault(k,[]).append((i,value))
    out={}
    for (k,j),value in b.items():
        for i,left in by_column.get(k,()):
            key=(i,j)
            out[key]=out.get(key,F(0))+left*value
    return s_clean(out)


def s_channel(kraus, rho):
    out={}
    for k in kraus:
        out=s_add(out,s_mul(s_mul(k,rho),s_adj(k)))
    return out


def basis_permutation(n, sites):
    require(sorted(sites)==list(range(n)),'Site map is not a permutation.')
    return tuple(sum(((x>>j)&1)<<sites[j] for j in range(n)) for x in range(1<<n))


def s_permutation_matrix(basis):
    return {(out,source):F(1) for source,out in enumerate(basis)}


def s_conjugate(a, basis):
    return {(basis[i],basis[j]):value for (i,j),value in a.items()}


def literal_feedback(n, j, k):
    """Embed the literal two-spin singlet table, with Z on FIRST endpoint.

    Local labels are |00>,|01>,|10>,|11>. No SWAP formula is used here.
    """
    table={(1,1):F(1,2),(1,2):F(-1,2),(2,1):F(-1,2),(2,2):F(1,2)}
    p={}
    mask=(1<<j)|(1<<k)
    for source in range(1<<n):
        local=2*((source>>j)&1)+((source>>k)&1)
        for row in range(4):
            value=table.get((row,local),F(0))
            if value:
                out=(source&~mask)|(((row>>1)&1)<<j)|((row&1)<<k)
                p[out,source]=value
    jump={(out,source):(-1 if (out>>j)&1 else 1)*value
          for (out,source),value in p.items()}
    return p,(s_add(s_eye(n),p,-1),jump)


def physical_swap(n, j, k):
    sites=list(range(n));sites[j],sites[k]=sites[k],sites[j]
    return s_permutation_matrix(basis_permutation(n,sites))


def symmetric_ground(n):
    # Direct sum of the normalized Dicke projectors in all weight sectors.
    return {(i,j):F(1,comb(n,i.bit_count()))
            for i,j in product(range(1<<n),repeat=2) if i.bit_count()==j.bit_count()}


def literal_layer(n, starts, record):
    out=s_eye(n)
    for j,outcome in zip(starts,record):
        out=s_mul(literal_feedback(n,j,(j+1)%n)[1][outcome],out)
    return out


def complete_effect(kraus):
    out={}
    for k in kraus:
        out=s_add(out,s_mul(s_adj(k),k))
    return out


def verify_full_three_qubits():
    n=3;identity=s_eye(n);ground=symmetric_ground(n)
    reflected=basis_permutation(n,(2,1,0))
    require(all(reflected[reflected[x]]==x for x in range(1<<n)),
            'Three-qubit reflection is not an involution.')
    units=0
    for j,k in ((0,1),(1,2)):
        p,ks=literal_feedback(n,j,k)
        require(p==s_scale(s_add(identity,physical_swap(n,j,k),-1),F(1,2)),
                'Literal full-space singlet differs from SWAP projector.')
        reverse=literal_feedback(n,k,j)[1]
        require(reverse[0]==ks[0] and reverse[1]==s_scale(ks[1],-1),
                'Reversing local endpoints has the wrong jump sign.')
        require(complete_effect(ks)==identity,'Full three-qubit update is not CPTP.')
        require(s_channel(ks,ground)==ground,'Full symmetric ground is not fixed.')
        target=literal_feedback(n,1-j,2-j)[1]
        for outcome in range(2):
            require(s_conjugate(ks[outcome],reflected)==s_scale(target[outcome],(-1)**outcome),
                    'Full three-qubit signed reflection covariance failed.')
        for r,s in product(range(1<<n),repeat=2):
            unit={(r,s):F(1)}
            once=s_channel(ks,unit)
            require(s_channel(ks,once)==once,'Full three-qubit update is not idempotent.')
            units+=1
    return {'hilbert_dimension':8,'local_feedback_updates':2,
            'local_idempotence_matrix_units':units,'signed_local_reflection_components':4}


def verify_even_ring(n):
    require(n>=4 and n%2==0,'Only even periodic rings N>=4 are supported.')
    m=n//2;identity=s_eye(n);ground=symmetric_ground(n)
    sites=tuple((-j)%n for j in range(n))
    reflected=basis_permutation(n,sites)
    translation_sites=tuple((j+1)%n for j in range(n))
    translated=basis_permutation(n,translation_sites)
    routed=tuple(range(1<<n));routing_count=0
    for left in range(n-2,-1,-1):
        routing_sites=list(range(n))
        routing_sites[left],routing_sites[left+1]=routing_sites[left+1],routing_sites[left]
        gate=basis_permutation(n,routing_sites)
        routed=tuple(gate[out] for out in routed)
        routing_count+=1
    require(routed==translated,'Adjacent-SWAP sequence does not implement cyclic translation.')
    require(all(reflected[reflected[x]]==x for x in range(1<<n)),
            'Ring reflection is not an involution on every computational basis state.')
    require(all(reflected[x].bit_count()==x.bit_count() for x in range(1<<n)),
            'Ring reflection changes magnetization.')
    require(s_conjugate(ground,reflected)==ground,'Reflection does not fix every Dicke sector.')
    require(s_conjugate(ground,translated)==ground,'Translation does not fix every Dicke sector.')
    edge_map=tuple((-j-1)%n for j in range(n))
    local_components=0
    for j,k in enumerate(edge_map):
        require((sites[j],sites[(j+1)%n])==((k+1)%n,k),
                'Reflected edge does not have reversed canonical endpoints.')
        require(j%2!=k%2,'Ring reflection does not exchange edge colours.')
        p,ks=literal_feedback(n,j,(j+1)%n)
        require(p==s_scale(s_add(identity,physical_swap(n,j,(j+1)%n),-1),F(1,2)),
                'Literal ring singlet differs from SWAP projector.')
        require(complete_effect(ks)==identity,'A full ring local instrument is incomplete.')
        target=literal_feedback(n,k,(k+1)%n)[1]
        for outcome in range(2):
            require(s_conjugate(ks[outcome],reflected)==s_scale(target[outcome],(-1)**outcome),
                    'Full-space signed local ring covariance failed.')
            translated_target=literal_feedback(n,(j+1)%n,(j+2)%n)[1][outcome]
            require(s_conjugate(ks[outcome],translated)==translated_target,
                    'Full-space orientation-preserving translation covariance failed.')
            local_components+=1
    starts=(tuple(range(0,n,2)),tuple(range(1,n,2)))
    records=tuple(product(range(2),repeat=m))
    require(set(tuple(reversed(word)) for word in records)==set(records),
            'Record reversal is not a bijection.')
    layers=tuple({word:literal_layer(n,edges,word) for word in records} for edges in starts)
    layer_components=0
    translation_layer_components=0
    for colour in range(2):
        require(complete_effect(layers[colour].values())==identity,'Layer instrument is incomplete.')
        for word,kraus in layers[colour].items():
            require(kraus==literal_layer(n,tuple(reversed(starts[colour])),tuple(reversed(word))),
                    'Disjoint-bond layer depends on multiplication order.')
            require(s_mul(kraus,ground)==(ground if not any(word) else {}),
                    'A layer record does not act correctly on all Dicke ground sectors.')
            expected=s_scale(layers[1-colour][tuple(reversed(word))],(-1)**sum(word))
            require(s_conjugate(kraus,reflected)==expected,
                    'All-record signed layer covariance failed.')
            shifted=word[-1:]+word[:-1]
            translation_word=word if colour==0 else shifted
            require(s_conjugate(kraus,translated)==layers[1-colour][translation_word],
                    'All-record translation layer covariance failed.')
            layer_components+=1
            translation_layer_components+=1
    # These per-record OPERATOR identities imply the full standard ready-meter
    # isometry by linearity, without sampling states or enumerating CSR units.
    pairs=tuple(product(records,repeat=2));zero_word=(0,)*m
    first_labels=set();second_labels=set();pointer_outputs=set()
    translated_labels=set();translation_pointer_outputs=set()
    standard_components=0
    for a,b in pairs:
        fixed=s_mul(layers[1][b],layers[0][a])
        ra,rb=tuple(reversed(a)),tuple(reversed(b))
        reverse=s_mul(layers[0][rb],layers[1][ra])
        branch1=s_conjugate(fixed,reflected)
        require(s_scale(branch1,(-1)**(sum(a)+sum(b)))==reverse,
                'Standard ready-pointer component differs after pointer permutation/phases.')
        shifted_b=b[-1:]+b[:-1]
        translation_reverse=s_mul(layers[0][shifted_b],layers[1][a])
        require(s_conjugate(fixed,translated)==translation_reverse,
                'Translated standard ready-pointer component differs after pointer permutation.')
        pointer_outputs.add((rb,ra))
        translation_pointer_outputs.add((shifted_b,a))
        first_labels.add((a,zero_word,zero_word,b))
        second_labels.add((zero_word,rb,ra,zero_word))
        translated_labels.add((zero_word,shifted_b,a,zero_word))
        standard_components+=1
    require(pointer_outputs==set(pairs),'Conditional quantum-pointer map is not bijective.')
    require(translation_pointer_outputs==set(pairs),'Translated quantum-pointer map is not bijective.')
    require(first_labels&second_labels=={(zero_word,)*4},
            'Fresh clock branches share a nonzero record.')
    require(first_labels&translated_labels=={(zero_word,)*4},
            'Translated fresh clock branches share a nonzero record.')
    zero_fixed=s_mul(layers[1][zero_word],layers[0][zero_word])
    zero_reverse=s_mul(layers[0][zero_word],layers[1][zero_word])
    require(s_conjugate(zero_fixed,reflected)==zero_reverse,
            'Fresh all-zero cross component differs.')
    require(s_conjugate(zero_fixed,translated)==zero_reverse,
            'Translated fresh all-zero cross component differs.')
    return {'sites':n,'hilbert_dimension':1<<n,'reflection_site_images':list(sites),
            'reflection_edge_images':list(edge_map),'layer_record_permutation':'word reversal',
            'signed_local_components':local_components,'complete_layer_instruments':2,
            'signed_layer_record_components':layer_components,
            'translation_site_images':list(translation_sites),
            'translation_local_components':local_components,
            'translation_layer_record_components':translation_layer_components,
            'translation_B_to_A_record_map':'cyclic right shift',
            'standard_ready_pointer_record_pair_operator_components':standard_components,
            'translation_standard_record_pair_operator_components':standard_components,
            'fresh_clock_shared_classical_records':1,
            'physical_transpositions_per_reflection':m-1,
            'adjacent_site_SWAPS_per_translation_or_inverse_on_line':routing_count,
            'reflection_quantum_pointer_transpositions_on_control_branch_one':m}


def verify():
    return {'status':'passed','three_site_one_excitation_fixture':verify_three_site_fixture(),
            'full_three_qubit_local_checks':verify_full_three_qubits(),
            'even_ring_checks':[verify_even_ring(n) for n in (4,6)],
            'scope':'Exact full-Hilbert finite guards for local three-qubit updates and '
                    'four/six-site even periodic rings. The separate tensor proof gives the '
                    'even-N reflection/translation covariance; finite guards alone do not '
                    'establish an all-N theorem. '
                    'Standard equality assumes pure ready coherently accessible meter registers '
                    'and priced controlled spatial/pointer permutations and pointer phases. '
                    'Fresh equality concerns full CSR and declared relabelled classical pointer '
                    'records after nonzero-record control dephasing; additional authentic module/time '
                    'logs require separate matching. No coherent clock outputs or arbitrary baths are compared. '
                    'No scalable cooling gain, runtime advantage or general ordinary optimum.'}


if __name__=='__main__':
    print(json.dumps(verify(),sort_keys=True))
