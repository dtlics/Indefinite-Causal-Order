"""Standard-library-only mixed-tensor diagram algebra for exact replay.

No numerical libraries or on-disk multiplication caches are imported. The
lexicographic permutation basis fixes the pairing conventions, and this
engine derives every operation directly from pairings.
It is deliberately small enough to audit together with the SOS checker.
"""
from __future__ import annotations
if not __debug__:
    raise RuntimeError('Exact diagram replay requires Python without -O.')

from itertools import permutations
from numbers import Integral


def _integer(value, name):
    if not isinstance(value, Integral) or isinstance(value, bool):
        raise ValueError(f'{name} must be an integer')
    return int(value)


def _cycles(permutation):
    seen = set()
    count = 0
    for start in range(len(permutation)):
        if start in seen:
            continue
        count += 1
        j = start
        while j not in seen:
            seen.add(j)
            j = permutation[j]
    return count


class ExactBrauerAlgebra:
    """Exact basis with P_pi placing input slot j into output slot pi[j].

    Before partial transpose, TOP pi[j] is paired with BOTTOM j.  Negative
    wires exchange top and bottom endpoints.  A product puts the left
    diagram above the right diagram and joins the middle endpoints.
    """

    def __init__(self, signature):
        self.signature = tuple(_integer(x, 'signature entry') for x in signature)
        if any(x not in (-1, 1) for x in self.signature):
            raise ValueError('signature entries must be +1 or -1')
        self.n = len(self.signature)
        if self.n > 8:
            raise ValueError('At most eight wires are supported')
        self.permutations = tuple(permutations(range(self.n)))
        self.size = self.basis_size = len(self.permutations)
        self.index_by_permutation = {pi: i for i, pi in enumerate(self.permutations)}
        self.identity = self.index_by_permutation[tuple(range(self.n))]
        def transpose(v):
            w = v % self.n
            return v if self.signature[w] > 0 else (v + self.n) % (2*self.n)
        pairings = []
        for pi in self.permutations:
            partner = [-1] * (2*self.n)
            for j in range(self.n):
                a, b = transpose(pi[j]), transpose(self.n+j)
                partner[a], partner[b] = b, a
            pairings.append(tuple(partner))
        self.pairs = tuple(pairings)
        self.index_by_pairs = {pair: i for i, pair in enumerate(self.pairs)}
        self.star = []
        for pair in self.pairs:
            flipped = [-1] * (2*self.n)
            for a, b in enumerate(pair):
                flipped[(a+self.n) % (2*self.n)] = (b+self.n) % (2*self.n)
            self.star.append(self.index_by_pairs[tuple(flipped)])
        self.star = tuple(self.star)
        self.cups = tuple(sum(a < b < self.n for a, b in enumerate(pair[:self.n]))
                          for pair in self.pairs)
        self._edges = tuple(tuple((a, b) for a, b in enumerate(pair) if a < b)
                            for pair in self.pairs)
        self._products = {}

    def multiply(self, i, j):
        i, j = _integer(i, 'left index'), _integer(j, 'right index')
        if not 0 <= i < self.size or not 0 <= j < self.size:
            raise IndexError((i, j))
        key = i, j
        if key in self._products:
            return self._products[key]
        n = self.n
        if n == 0:
            return 0, 0
        # Union-find describes the three rows of the glued diagram.  A
        # component has either two external vertices or zero (a closed loop).
        parent = list(range(3*n))
        def find(v):
            while parent[v] != v:
                parent[v] = parent[parent[v]]
                v = parent[v]
            return v
        for a, b in self._edges[i]:
            a, b = find(a), find(b)
            if a != b:
                parent[a] = b
        for a, b in self._edges[j]:
            a, b = find(a+n), find(b+n)
            if a != b:
                parent[a] = b
        external = {}
        roots = {find(v) for v in range(3*n)}
        for v in range(2*n):
            physical = v if v < n else v+n
            external.setdefault(find(physical), []).append(v)
        partner = [-1] * (2*n)
        for endpoints in external.values():
            if len(endpoints) != 2:
                raise RuntimeError('A glued diagram has an invalid boundary component')
            a, b = endpoints
            partner[a], partner[b] = b, a
        loops = len(roots - external.keys())
        result = self.index_by_pairs[tuple(partner)], loops
        self._products[key] = result
        return result

    def multiplication_table(self):
        if self.size**2 > 5_000_000:
            raise ValueError('Refusing a huge multiplication table')
        index, loops = [], []
        for i in range(self.size):
            row = [self.multiply(i, j) for j in range(self.size)]
            index.append(tuple(x[0] for x in row))
            loops.append(tuple(x[1] for x in row))
        return tuple(index), tuple(loops)

    def trace_vector(self, D):
        D = _integer(D, 'D')
        if D < 1:
            raise ValueError('D must be positive')
        return tuple(D**_cycles(pi) for pi in self.permutations)

    def norm_bounds(self, D):
        D = _integer(D, 'D')
        if D < 1:
            raise ValueError('D must be positive')
        return tuple(D**c for c in self.cups)

    def gram(self, D):
        D = _integer(D, 'D')
        if D < 1:
            raise ValueError('D must be positive')
        rows = []
        for pi in self.permutations:
            inverse = [0] * self.n
            for j, value in enumerate(pi):
                inverse[value] = j
            rows.append(tuple(D**_cycles(tuple(inverse[value] for value in sigma))
                              for sigma in self.permutations))
        return tuple(rows)

    def partial_trace_map(self, remove_wire):
        w = _integer(remove_wire, 'removed wire')
        if not 0 <= w < self.n:
            raise IndexError(w)
        n = self.n
        target = ExactBrauerAlgebra(self.signature[:w] + self.signature[w+1:])
        indices, loops = [], []
        def remap(v):
            if v < n:
                return v - (v > w)
            return n-1 + v-n - (v-n > w)
        for pair in self.pairs:
            traced = {w, n+w}
            output = [-1] * (2*(n-1))
            loop = int(pair[w] == n+w)
            if not loop:
                a, b = remap(pair[w]), remap(pair[n+w])
                output[a], output[b] = b, a
            for a, b in enumerate(pair):
                if a < b and a not in traced and b not in traced:
                    a, b = remap(a), remap(b)
                    output[a], output[b] = b, a
            indices.append(target.index_by_pairs[tuple(output)])
            loops.append(loop)
        return target, tuple(indices), tuple(loops)

    def insert_identity_map(self, position, sign):
        position, sign = _integer(position, 'position'), _integer(sign, 'sign')
        if not 0 <= position <= self.n:
            raise IndexError(position)
        if sign not in (-1, 1):
            raise ValueError('sign must be +1 or -1')
        n = self.n
        target = ExactBrauerAlgebra(self.signature[:position] + (sign,) + self.signature[position:])
        def remap(v):
            if v < n:
                return v + (v >= position)
            return n+1 + v-n + (v-n >= position)
        indices = []
        for pair in self.pairs:
            output = [-1] * (2*(n+1))
            for a, b in enumerate(pair):
                if a < b:
                    a, b = remap(a), remap(b)
                    output[a], output[b] = b, a
            output[position] = n+1+position
            output[n+1+position] = position
            indices.append(target.index_by_pairs[tuple(output)])
        return target, tuple(indices)


# A convenient drop-in name for callers that only need the exact engine.
BrauerAlgebra = ExactBrauerAlgebra
