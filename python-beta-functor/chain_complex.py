"""
Chain complexes with an A-infinity (capped at 2nd order) functor.

Core types
----------
Generator       : int, the index n in T(n)
MapCoeff        : dict[(src: int, tgt: int, idx: int) -> int]
                  Formal Z-linear combination of maps between generators.
GradedObject    : dict[degree: int -> list[Generator]]
ChainMap        : degree-shifted collection of MapCoeff entries
ChainComplex    : GradedObject + differential ChainMap
AInfinityData   : mu1 table and mu2 table
"""

from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Dict, List, Tuple


# ---------------------------------------------------------------------------
# 1.  MapCoeff  —  formal Z-linear combination of maps T(i)->T(j)
# ---------------------------------------------------------------------------

# A single map key: (source_generator, target_generator, map_index)
MapKey = Tuple[int, int, int]

# The full linear combination
MapCoeff = Dict[MapKey, int]


def mc_zero() -> MapCoeff:
    return {}


def mc_add(a: MapCoeff, b: MapCoeff) -> MapCoeff:
    """Add two MapCoeff objects, dropping zero coefficients."""
    result = dict(a)
    for key, coeff in b.items():
        result[key] = result.get(key, 0) + coeff
    return {k: v for k, v in result.items() if v != 0}


def mc_scale(a: MapCoeff, scalar: int) -> MapCoeff:
    """Scalar multiply a MapCoeff."""
    if scalar == 0:
        return {}
    return {k: v * scalar for k, v in a.items()}


def _composition_index(i: int, j: int, k: int, idx1: int, idx2: int) -> int:
    """
    Compose map T(i)->T(j) with index idx1,
    and map T(j)->T(k) with index idx2.

    Result index = idx1 + idx2 + (|i-j| + |j-k| - |i-k|) // 2
    """
    extra = (abs(i - j) + abs(j - k) - abs(i - k)) // 2
    return idx1 + idx2 + extra


def mc_compose(f: MapCoeff, g: MapCoeff) -> MapCoeff:
    """
    Compose f: ?->? with g: ?->? (g after f).
    Only pairs whose intermediate generator matches are combined.
    Result is bilinear (distributes over addition).
    """
    result: MapCoeff = {}
    for (i, j1, idx_f), cf in f.items():
        for (j2, k, idx_g), cg in g.items():
            if j1 != j2:
                continue
            new_idx = _composition_index(i, j1, k, idx_f, idx_g)
            key = (i, k, new_idx)
            result[key] = result.get(key, 0) + cf * cg
    return {k: v for k, v in result.items() if v != 0}


def mc_repr(m: MapCoeff) -> str:
    """Human-readable string for a MapCoeff."""
    if not m:
        return "0"
    terms = []
    for (i, j, idx), coeff in sorted(m.items()):
        sign = "+" if coeff > 0 else "-"
        abs_c = abs(coeff)
        c_str = "" if abs_c == 1 else str(abs_c)
        terms.append(f"{sign}{c_str}f(T{i:+d}->T{j:+d},{idx})")
    s = " ".join(terms)
    return s.lstrip("+").strip()


# ---------------------------------------------------------------------------
# 2.  GradedObject
# ---------------------------------------------------------------------------

# Maps homological degree -> list of generator indices (repetition = multiplicity)
GradedObject = Dict[int, List[int]]


def go_degrees(obj: GradedObject) -> List[int]:
    return sorted(obj.keys())


def go_generators_at(obj: GradedObject, deg: int) -> List[int]:
    return obj.get(deg, [])


def go_repr(obj: GradedObject) -> str:
    parts = []
    for deg in go_degrees(obj):
        gens = obj[deg]
        gen_str = " ⊕ ".join(f"T({g:+d})" for g in gens)
        parts.append(f"  deg {deg:+d}: {gen_str}")
    return "\n".join(parts) if parts else "  (zero)"


# ---------------------------------------------------------------------------
# 3.  ChainMap
# ---------------------------------------------------------------------------

@dataclass
class ChainMap:
    """
    A graded map between two GradedObjects.

    components[(src_deg, src_pos, tgt_pos)] = MapCoeff
      where src_pos indexes into source.generators_at(src_deg)
        and tgt_pos indexes into target.generators_at(src_deg + shift)

    shift: int   0 for a chain map, -1 for the mu2 homotopy term.
    """
    source: GradedObject
    target: GradedObject
    shift: int
    components: Dict[Tuple[int, int, int], MapCoeff] = field(default_factory=dict)

    def get(self, src_deg: int, src_pos: int, tgt_pos: int) -> MapCoeff:
        return self.components.get((src_deg, src_pos, tgt_pos), mc_zero())

    def set(self, src_deg: int, src_pos: int, tgt_pos: int, val: MapCoeff) -> None:
        key = (src_deg, src_pos, tgt_pos)
        cleaned = {k: v for k, v in val.items() if v != 0}
        if cleaned:
            self.components[key] = cleaned
        elif key in self.components:
            del self.components[key]

    def add_to(self, src_deg: int, src_pos: int, tgt_pos: int, val: MapCoeff) -> None:
        current = self.get(src_deg, src_pos, tgt_pos)
        self.set(src_deg, src_pos, tgt_pos, mc_add(current, val))

    def repr_at_degree(self, src_deg: int) -> str:
        src_gens = go_generators_at(self.source, src_deg)
        tgt_gens = go_generators_at(self.target, src_deg + self.shift)
        if not src_gens or not tgt_gens:
            return f"  deg {src_deg:+d}: (empty)"
        lines = [f"  deg {src_deg:+d} -> deg {src_deg + self.shift:+d}:"]
        for sp, sg in enumerate(src_gens):
            for tp, tg in enumerate(tgt_gens):
                m = self.get(src_deg, sp, tp)
                if m:
                    lines.append(
                        f"    T({sg:+d})[{sp}] -> T({tg:+d})[{tp}]: {mc_repr(m)}"
                    )
        return "\n".join(lines)

    def __repr__(self) -> str:
        degs = sorted(set(k[0] for k in self.components))
        if not degs:
            return "ChainMap(zero)"
        return "ChainMap(\n" + "\n".join(self.repr_at_degree(d) for d in degs) + "\n)"


# ---------------------------------------------------------------------------
# 4.  ChainComplex
# ---------------------------------------------------------------------------

@dataclass
class ChainComplex:
    """
    A chain complex: a GradedObject with a differential of shift -1.
    d^2 = 0 is not enforced automatically; use check_differential() to verify.
    """
    objects: GradedObject
    differential: ChainMap

    def __post_init__(self):
        assert self.differential.shift == -1, "Differential must have shift -1"

    def repr_objects(self) -> str:
        return go_repr(self.objects)

    def repr_differential(self) -> str:
        degs = go_degrees(self.objects)
        lines = []
        for d in degs:
            lines.append(self.differential.repr_at_degree(d))
        return "\n".join(lines)

    def __repr__(self) -> str:
        return self.__str__()

    def __str__(self) -> str:
        return _render_complex(self)

    @staticmethod
    def single_generator(gen: int, degree: int) -> "ChainComplex":
        """The complex 0 -> T(gen) -> 0 concentrated in one degree."""
        obj: GradedObject = {degree: [gen]}
        diff = ChainMap(source=obj, target=obj, shift=-1)
        return ChainComplex(objects=obj, differential=diff)


# ---------------------------------------------------------------------------
# 5.  Cone construction
# ---------------------------------------------------------------------------

def cone(f: ChainMap) -> ChainComplex:
    """
    Cone of a chain map f: A -> B (both chain complexes implicit via f.source/target).
    
    cone(f) has objects  A[1] ⊕ B  in each degree,
    i.e. at degree n:  A_{n+1} ⊕ B_n
    
    The differential is the block matrix:
        d_cone = [[-d_A,  0  ],
                  [ f,   d_B ]]
    where d_A acts on the A[1] part (with a sign from the shift).
    
    We encode this in a single ChainComplex whose GradedObject is
    the concatenation of A[1] and B generators at each degree.
    """
    A = f.source
    B = f.target

    # Build the cone GradedObject: at degree n, A_{n+1} generators then B_n generators
    all_degs = set(A.keys()) | set(B.keys())
    # A contributes at degree (orig_deg - 1)
    a_shifted_degs = {d - 1 for d in A.keys()}
    cone_degs = all_degs | a_shifted_degs

    cone_obj: GradedObject = {}
    for n in cone_degs:
        a_part = go_generators_at(A, n + 1)   # A_{n+1}
        b_part = go_generators_at(B, n)        # B_n
        if a_part or b_part:
            cone_obj[n] = list(a_part) + list(b_part)

    # We need the differentials of A and B — caller must pass them in separately
    # This function takes the chain map f and the two complexes explicitly.
    # For the standalone version, embed d_A and d_B inside f's source/target
    # complexes. We lift them out by convention: the caller passes a ChainMap
    # whose .source and .target carry the differentials as attributes if they
    # are ChainComplex objects. We handle both cases below.
    raise NotImplementedError(
        "cone() needs the differentials of source and target complexes. "
        "Use cone_of_complexes(f, A_cx, B_cx) instead."
    )


def cone_of_complexes(f: ChainMap, A_cx: ChainComplex, B_cx: ChainComplex) -> ChainComplex:
    """
    Cone of a chain map f: A_cx -> B_cx.

    At degree n, the cone has generators:  A_{n+1} generators, then B_n generators.
    Positions 0..|A_{n+1}|-1 are the A part; |A_{n+1}|.. are the B part.

    Differential blocks (source degree n -> target degree n-1):
      - Top-left    (-d_A):  A_{n+1} -> A_n,   negated
      - Bottom-left (f):     A_{n+1} -> B_n,   from f at degree n+1 -> n... 
                             actually f: A -> B has shift 0, so f at src_deg=n+1
                             maps to B_{n+1}. We want f at src_deg=n to map to B_n.
      - Bottom-right (d_B):  B_n -> B_{n-1}
    """
    A = A_cx.objects
    B = B_cx.objects
    d_A = A_cx.differential
    d_B = B_cx.differential

    # Build cone GradedObject
    cone_obj: GradedObject = {}
    all_degs: set = set()
    for d in A.keys():
        all_degs.add(d - 1)
    for d in B.keys():
        all_degs.add(d)

    for n in all_degs:
        a_part = go_generators_at(A, n + 1)
        b_part = go_generators_at(B, n)
        if a_part or b_part:
            cone_obj[n] = list(a_part) + list(b_part)

    cone_diff = ChainMap(source=cone_obj, target=cone_obj, shift=-1)

    for n in sorted(cone_obj.keys()):
        a_src = go_generators_at(A, n + 1)   # A part at degree n
        b_src = go_generators_at(B, n)        # B part at degree n
        a_tgt = go_generators_at(A, n)        # A part at degree n-1
        b_tgt = go_generators_at(B, n - 1)    # B part at degree n-1

        n_a_src = len(a_src)
        n_b_src = len(b_src)
        n_a_tgt = len(a_tgt)
        n_b_tgt = len(b_tgt)

        # Block 1: -d_A  from A_{n+1} (positions 0..n_a_src-1)
        #                 to   A_n    (positions 0..n_a_tgt-1)
        # d_A has src_deg = n+1, maps A_{n+1} -> A_n
        for sp in range(n_a_src):
            for tp in range(n_a_tgt):
                m = d_A.get(n + 1, sp, tp)
                if m:
                    cone_diff.add_to(n, sp, tp, mc_scale(m, -1))

        # Block 2: f  from A_{n+1} (positions 0..n_a_src-1)
        #               to   B_n    (positions n_a_tgt..n_a_tgt+n_b_tgt-1)
        # f has shift 0, src_deg = n+1... wait: f: A->B shift 0 means
        # f at src_deg maps A_{src_deg} -> B_{src_deg}.
        # We want A_{n+1} -> B_n, so this is the degree-(-1) part of f,
        # i.e. f.shift should be -1 here for the mu2 term. 
        # For the standard cone of a degree-0 chain map, f maps A_n -> B_n.
        # In the cone differential at degree n, we want f: A_{n+1} -> B_n,
        # so we look up f at src_deg = n+1 (f has shift -1 in this context... 
        # but wait, a chain map f: A->B of degree 0 maps A_n -> B_n,
        # so in the cone we access f.get(n+1, sp, tp) which gives A_{n+1}->B_{n+1},
        # not B_n. We need f to have shift -1, OR we access f at src_deg=n.
        # Convention: f is a degree-0 chain map, so f.get(n, sp, tp): A_n -> B_n.
        # In the cone at degree n, the A-part is A_{n+1}, so we use f.get(n+1,...).
        # That maps A_{n+1} -> B_{n+1} which is wrong. 
        # Correct cone formula: use f.get(n, ...) mapping A_n (=A-part at n-1 in cone)
        # -- let me re-index cleanly.
        #
        # Standard cone: cone_n = A_{n+1} ⊕ B_n
        # diff: cone_n -> cone_{n-1} = A_n ⊕ B_{n-1}
        # blocks:
        #   A_{n+1} -> A_n   : -d_A (src_deg=n+1 in d_A)  ✓ above
        #   A_{n+1} -> B_{n-1}: this would be wrong
        #   B_n -> B_{n-1}   : d_B  (src_deg=n in d_B)
        #
        # The f block: A_{n+1} -> B_n. f: A->B degree 0 means f_n: A_n->B_n.
        # So the f block is f_{n+1}: A_{n+1} -> B_{n+1}? No that maps to B_{n+1}.
        # 
        # RESOLUTION: the standard formula uses f_n: A_n -> B_{n-1}, i.e. f has degree -1.
        # OR equivalently, the cone differential uses f as a degree -1 map (which is
        # exactly your mu2 case). For a standard degree-0 chain map, the off-diagonal
        # block in the cone is f: A_{n+1} -> B_n, accessed as f.get(n+1, sp, tp)
        # with f having shift -1.  We enforce shift in the assertions.
        
        if f.shift == -1:
            # f: A->B degree -1, f.get(src_deg, sp, tp): A_{src_deg} -> B_{src_deg - 1}
            # We want A_{n+1} -> B_n, so src_deg = n+1
            b_count = len(go_generators_at(B, n))
            for sp in range(n_a_src):
                for tp in range(b_count):
                    m = f.get(n + 1, sp, tp)
                    if m:
                        cone_diff.add_to(n, sp, n_a_tgt + tp, m)
        elif f.shift == 0:
            # f: A->B degree 0, f.get(src_deg, sp, tp): A_{src_deg} -> B_{src_deg}
            # We want A_{n+1} -> B_n. There's no direct entry; this means
            # the chain map doesn't contribute at this block for degree-0 maps.
            # Actually for degree-0, the cone formula is:
            #   cone_n = A_n ⊕ B_n, diff = (-d_A, 0; f, d_B)
            # i.e. a DIFFERENT cone convention. We use that here.
            for sp in range(len(go_generators_at(A, n))):
                for tp in range(len(go_generators_at(B, n))):
                    m = f.get(n, sp, tp)
                    if m:
                        cone_diff.add_to(n, sp, n_a_tgt + tp, m)

        # Block 3: d_B  from B_n (positions n_a_src..n_a_src+n_b_src-1)
        #                 to   B_{n-1} (positions n_a_tgt..n_a_tgt+n_b_tgt-1)
        for sp in range(n_b_src):
            for tp in range(n_b_tgt):
                m = d_B.get(n, sp, tp)
                if m:
                    cone_diff.add_to(n, n_a_src + sp, n_a_tgt + tp, m)

    # Rebuild cone_obj to match actual convention used above
    if f.shift == 0:
        # Re-build: cone_n = A_n ⊕ B_n
        cone_obj2: GradedObject = {}
        all_degs2 = set(A.keys()) | set(B.keys())
        for n in all_degs2:
            a_part = go_generators_at(A, n)
            b_part = go_generators_at(B, n)
            if a_part or b_part:
                cone_obj2[n] = list(a_part) + list(b_part)
        cone_diff2 = ChainMap(source=cone_obj2, target=cone_obj2, shift=-1)
        for n in sorted(cone_obj2.keys()):
            a_src = go_generators_at(A, n)
            b_src = go_generators_at(B, n)
            a_tgt = go_generators_at(A, n - 1)
            b_tgt = go_generators_at(B, n - 1)
            n_a_src = len(a_src)
            n_a_tgt = len(a_tgt)
            # -d_A block
            for sp in range(n_a_src):
                for tp in range(n_a_tgt):
                    m = d_A.get(n, sp, tp)
                    if m:
                        cone_diff2.add_to(n, sp, tp, mc_scale(m, -1))
            # f block
            for sp in range(n_a_src):
                for tp in range(len(go_generators_at(B, n))):
                    m = f.get(n, sp, tp)
                    if m:
                        cone_diff2.add_to(n, sp, n_a_tgt + tp, m)
            # d_B block
            for sp in range(len(b_src)):
                for tp in range(len(b_tgt)):
                    m = d_B.get(n, sp, tp)
                    if m:
                        cone_diff2.add_to(n, n_a_src + sp, n_a_tgt + tp, m)
        return ChainComplex(objects=cone_obj2, differential=cone_diff2)

    return ChainComplex(objects=cone_obj, differential=cone_diff)


# ---------------------------------------------------------------------------
# 6.  A-infinity functor data
# ---------------------------------------------------------------------------

@dataclass
class AInfinityData:
    """
    mu1 / beta0:
        dict[gen: int -> ChainComplex]
        The image of each generator T(gen) under the functor.

    mu1_maps / beta1:
        dict[(src_gen, tgt_gen, map_index) -> ChainMap]
        For each morphism T(src)->T(tgt) with a given index, the induced
        degree-0 chain map between the beta0 images.

    mu2 / beta2:
        dict[(src_gen, tgt_gen, composed_index) -> ChainMap]
        For each composable pair T(i)->T(j)->T(k), a degree-(+1) chain map
        from beta0(T(i)) to beta0(T(k)), representing the homotopy term.
        Keyed by (src_gen, tgt_gen, composed_index) where composed_index is
        computed via _composition_index(i, j, k, idx1, idx2).
        When two different paths yield the same key their contributions are
        combined by adding the chain maps (done in functors.py at build time).
    """
    mu1: Dict[int, ChainComplex] = field(default_factory=dict)
    # beta1: (src_gen, tgt_gen, map_index) -> ChainMap, shift=0
    mu1_maps: Dict[Tuple[int, int, int], ChainMap] = field(default_factory=dict)
    # beta2: (src_gen, tgt_gen, composed_index) -> ChainMap, shift=+1
    mu2: Dict[Tuple[int, int, int], ChainMap] = field(default_factory=dict)

    def __call__(self, cx: "ChainComplex") -> "ChainComplex":
        """Allow functor(cx) syntax."""
        return apply_functor(cx, self)


# ---------------------------------------------------------------------------
# 7.  Apply functor to a chain complex
# ---------------------------------------------------------------------------

def apply_functor(cx: ChainComplex, functor: AInfinityData) -> ChainComplex:
    """
    Apply the A-infinity functor to a chain complex cx.

    Algorithm:
      1. For each generator T(g) at cx-degree d, replace it with functor.mu1[g]
         shifted by d (result_degree = d + internal_degree).  The internal
         differentials of each mu1[g] block are copied into the result.

      2. For each differential component f(T(i)->T(j), idx) with coefficient c
         in cx, look up functor.mu1_maps[(i, j, idx)] — a degree-0 chain map
         from mu1[i] to mu1[j] — and add c * that map into the result
         differential, with source block shifted by cx_deg and target block
         shifted by cx_deg - 1.

      3. For each composable pair of differentials T(i)->[idx1]->T(j)->[idx2]->T(k),
         compute the composed index and look up functor.mu2[(i, k, composed_idx)].
         mu2 is a degree-(+1) chain map from mu1[i] to mu1[k].  Add c1*c2 times
         that map into the result differential, with source block shifted by
         cx_deg and target block shifted by cx_deg - 2, but the internal degree
         offset is +1 (shift=+1 means internal_deg in source maps to
         internal_deg+1 in target).

    Returns a new ChainComplex.
    """

    # ------------------------------------------------------------------
    # Step 1: Build result GradedObject as direct sum of shifted mu1 blocks.
    #
    # block_map[(cx_deg, pos)] = dict[internal_deg -> (result_deg, start_pos)]
    # records where each sub-block lands in the result.
    # ------------------------------------------------------------------
    result_obj: GradedObject = defaultdict(list)
    block_map: Dict[Tuple[int, int], Dict[int, Tuple[int, int]]] = {}

    for cx_deg in go_degrees(cx.objects):
        for pos, g in enumerate(go_generators_at(cx.objects, cx_deg)):
            mu1_g = functor.mu1[g]
            inner: Dict[int, Tuple[int, int]] = {}
            for int_deg, int_gens in sorted(mu1_g.objects.items()):
                res_deg = cx_deg + int_deg
                start = len(result_obj[res_deg])
                result_obj[res_deg].extend(int_gens)
                inner[int_deg] = (res_deg, start)
            block_map[(cx_deg, pos)] = inner

    result_obj = dict(result_obj)
    result_diff = ChainMap(source=result_obj, target=result_obj, shift=-1)

    # ------------------------------------------------------------------
    # Step 2a: Internal differentials of each mu1[g] block.
    # ------------------------------------------------------------------
    for cx_deg in go_degrees(cx.objects):
        for pos, g in enumerate(go_generators_at(cx.objects, cx_deg)):
            d_mu1 = functor.mu1[g].differential
            inner = block_map[(cx_deg, pos)]
            for int_deg in go_degrees(functor.mu1[g].objects):
                if (int_deg - 1) not in inner:
                    continue
                res_src_deg, res_src_start = inner[int_deg]
                res_tgt_deg, res_tgt_start = inner[int_deg - 1]
                n_src = len(go_generators_at(functor.mu1[g].objects, int_deg))
                n_tgt = len(go_generators_at(functor.mu1[g].objects, int_deg - 1))
                for sp in range(n_src):
                    for tp in range(n_tgt):
                        m = d_mu1.get(int_deg, sp, tp)
                        if m:
                            result_diff.add_to(
                                res_src_deg, res_src_start + sp,
                                res_tgt_start + tp, m
                            )

    # ------------------------------------------------------------------
    # Step 2b: beta1 — induced maps from differentials of cx.
    #
    # For each d-component f(T(i)->T(j), idx) with coeff c in cx, look up
    # mu1_maps[(i, j, idx)]: a degree-0 ChainMap from mu1[i] to mu1[j].
    # Its entry at (int_deg, sp, tp) maps:
    #   source block (cx_deg, src_pos) at internal degree int_deg
    #   -> target block (cx_deg-1, tgt_pos) at internal degree int_deg
    # (degree 0 means same internal degree in source and target).
    # ------------------------------------------------------------------
    for cx_deg in go_degrees(cx.objects):
        src_gens = go_generators_at(cx.objects, cx_deg)
        tgt_gens = go_generators_at(cx.objects, cx_deg - 1)
        for sp, sg in enumerate(src_gens):
            for tp, tg in enumerate(tgt_gens):
                d_comp = cx.differential.get(cx_deg, sp, tp)
                if not d_comp:
                    continue
                src_inner = block_map[(cx_deg, sp)]
                tgt_inner = block_map[(cx_deg - 1, tp)]
                for (i, j, idx), coeff in d_comp.items():
                    beta1 = functor.mu1_maps.get((i, j, idx))
                    if beta1 is None:
                        raise KeyError(
                            f"Missing beta1 entry for (i={i}, j={j}, idx={idx}). "
                            f"Add it to mu1_maps in functors.py."
                        )
                    # beta1 is a degree-0 map: int_deg in mu1[i] -> int_deg in mu1[j]
                    for int_deg, (res_src_deg, res_src_start) in src_inner.items():
                        if int_deg not in tgt_inner:
                            continue
                        res_tgt_deg, res_tgt_start = tgt_inner[int_deg]
                        n_src = len(go_generators_at(functor.mu1[i].objects, int_deg))
                        n_tgt = len(go_generators_at(functor.mu1[j].objects, int_deg))
                        for bsp in range(n_src):
                            for btp in range(n_tgt):
                                m = beta1.get(int_deg, bsp, btp)
                                if m:
                                    result_diff.add_to(
                                        res_src_deg, res_src_start + bsp,
                                        res_tgt_start + btp,
                                        mc_scale(m, coeff)
                                    )

    # ------------------------------------------------------------------
    # Step 3: beta2 — homotopy terms from composable pairs.
    #
    # For each pair T(i)->[idx1]->T(j)->[idx2]->T(k) in cx, compute
    # composed_idx = _composition_index(i, j, k, idx1, idx2) and look up
    # mu2[(i, k, composed_idx)]: a degree-(+1) ChainMap from mu1[i] to mu1[k].
    #
    # shift=+1 means: entry at (int_deg, bsp, btp) maps
    #   source at internal degree int_deg  ->  target at internal degree int_deg+1
    #
    # In the result:
    #   source block is (cx_deg_ij, sp_i), shifted by cx_deg_ij
    #     -> result_deg = cx_deg_ij + int_deg
    #   target block is (cx_deg_ij - 2, tp_k), shifted by cx_deg_ij - 2
    #     -> result_deg = (cx_deg_ij - 2) + (int_deg + 1) = cx_deg_ij + int_deg - 1
    # This is exactly result_deg - 1, consistent with shift=-1 on result_diff. ✓
    # ------------------------------------------------------------------
    for cx_deg_ij in go_degrees(cx.objects):
        src_gens_ij = go_generators_at(cx.objects, cx_deg_ij)
        mid_gens    = go_generators_at(cx.objects, cx_deg_ij - 1)
        tgt_gens_jk = go_generators_at(cx.objects, cx_deg_ij - 2)

        for sp_i, sg_i in enumerate(src_gens_ij):
            for mp_j, sg_j in enumerate(mid_gens):
                d_ij = cx.differential.get(cx_deg_ij, sp_i, mp_j)
                if not d_ij:
                    continue
                for tp_k, sg_k in enumerate(tgt_gens_jk):
                    d_jk = cx.differential.get(cx_deg_ij - 1, mp_j, tp_k)
                    if not d_jk:
                        continue
                    for (i, j1, idx1), c1 in d_ij.items():
                        for (j2, k, idx2), c2 in d_jk.items():
                            if j1 != j2:
                                continue
                            composed_idx = _composition_index(i, j1, k, idx1, idx2)
                            mu2_map = functor.mu2.get((i, k, composed_idx))
                            if mu2_map is None:
                                continue   # beta2 is zero for this triple
                            src_inner = block_map[(cx_deg_ij, sp_i)]
                            tgt_inner = block_map[(cx_deg_ij - 2, tp_k)]
                            # mu2_map has shift=+1: int_deg -> int_deg + 1 in target
                            for int_deg, (res_src_deg, res_src_start) in src_inner.items():
                                tgt_int_deg = int_deg + 1
                                if tgt_int_deg not in tgt_inner:
                                    continue
                                res_tgt_deg, res_tgt_start = tgt_inner[tgt_int_deg]
                                n_src = len(go_generators_at(functor.mu1[i].objects, int_deg))
                                n_tgt = len(go_generators_at(functor.mu1[k].objects, tgt_int_deg))
                                for bsp in range(n_src):
                                    for btp in range(n_tgt):
                                        m2 = mu2_map.get(int_deg, bsp, btp)
                                        if m2:
                                            result_diff.add_to(
                                                res_src_deg, res_src_start + bsp,
                                                res_tgt_start + btp,
                                                mc_scale(m2, c1 * c2)
                                            )

    return ChainComplex(objects=result_obj, differential=result_diff)


# ---------------------------------------------------------------------------
# 8.  ASCII renderer for ChainComplex
# ---------------------------------------------------------------------------

def _gen_label(g: int) -> str:
    """Short label for a generator, e.g. T0, T1, T-1."""
    return f"T{g}"


def _mc_short(m: MapCoeff) -> str:
    """
    Compact representation of a MapCoeff for use inside the diagram.
    Single term {(i,j,k):1} -> 'k' (just the index).
    Single term {(i,j,k):c} -> 'c·k'.
    Multiple terms        -> comma-separated.
    Zero morphism ({})    -> '-'.
    """
    if not m:
        return "-"
    parts = []
    for (i, j, idx), coeff in sorted(m.items(), key=lambda x: x[0][2]):
        if coeff == 1:
            parts.append(str(idx))
        elif coeff == -1:
            parts.append(f"-{idx}")
        else:
            parts.append(f"{coeff}·{idx}")
    return ",".join(parts)


def _render_transition_lines(
    src_labels: list,   # labels for source (upper) row
    tgt_labels: list,   # labels for target (lower) row
    maps: list,         # maps[sp][tp] = MapCoeff or None
    src_centers: list,  # x-center of each source label
    tgt_centers: list,  # x-center of each target label
    width: int,
) -> list:
    """
    Draw ASCII lines between src and tgt nodes for a single degree transition.
    Uses 3 rows: top-connector, middle, bottom-connector.
    Index-0 single maps: bare line char. Others: line char + index label.
    Returns list of strings (rows), each of length `width`.
    """
    # We'll use 4 rows of connector lines
    rows = [list(" " * width) for _ in range(4)]

    for sp, sx in enumerate(src_centers):
        for tp, tx in enumerate(tgt_centers):
            m = maps[sp][tp]
            if not m:
                continue
            label = _mc_short(m)
            show_label = (label != "0" and label != "0")
            # pick line character based on direction
            dx = tx - sx
            if dx == 0:
                chars = ["│", "│", "│", "│"]
            elif dx > 0:
                chars = ["╲", "╲", "╲", "╲"]
            else:
                chars = ["╱", "╱", "╱", "╱"]

            # Place characters stepping from sx toward tx across 4 rows
            for row_i in range(4):
                frac = (row_i + 0.5) / 4
                x = int(sx + frac * (tx - sx))
                x = max(0, min(width - 1, x))
                rows[row_i][x] = chars[row_i]

            # Place label next to midpoint if index != 0
            if label != "0":
                mid_x = int(sx + 0.5 * (tx - sx))
                label_x = min(mid_x + 1, width - len(label) - 1)
                label_x = max(0, label_x)
                for ci, ch in enumerate(label):
                    if label_x + ci < width:
                        rows[1][label_x + ci] = ch

    return ["".join(r) for r in rows]


def _render_transition_matrix(
    src_labels: list,
    src_centers: list,
    tgt_labels: list,
    maps: list,
    deg_label_w: int,
    canvas_width: int,
) -> list:
    """
    Render a matrix whose columns are anchored directly above the source
    generator positions in the degree row below, and whose rows are labelled
    by the target generator names on the left.

    maps[sp][tp] is the MapCoeff from source pos sp to target pos tp.

    The degree row is:  'deg X: ' + canvas  (prefix_w + canvas_width chars)
    Each matrix row is: row_label + ' | ' + canvas  right-aligned into prefix_w,
    so the canvas portion starts at exactly the same column as the degree row.
    """
    n_src = len(src_labels)
    n_tgt = len(tgt_labels)
    row_label_w = max((len(l) for l in tgt_labels), default=0)
    prefix_w = deg_label_w + 1   # e.g. len('deg 0: ')

    # The row prefix is 'LABEL | ' — must fit in prefix_w chars.
    # Format: label right-justified, then ' | ', total = row_label_w + 3.
    # If row_label_w + 3 > prefix_w, we just let it extend (rare).
    sep = " | "

    # Cell strings: cells[sp][tp]
    cells = [[_mc_short(maps[sp][tp]) for tp in range(n_tgt)]
             for sp in range(n_src)]

    row_lines = []
    for tp, tl in enumerate(tgt_labels):
        # Build canvas of width canvas_width, cells anchored at src_centers
        canvas = list(" " * canvas_width)
        for sp in range(n_src):
            cell = cells[sp][tp]
            cx_ = src_centers[sp]
            start = cx_ - len(cell) // 2
            for ci, ch in enumerate(cell):
                pos = start + ci
                if 0 <= pos < canvas_width:
                    canvas[pos] = ch
        # Build left part: right-align label into (prefix_w - len(sep)) chars
        label_field_w = prefix_w - len(sep)
        left = tl.rjust(label_field_w) + sep
        row_lines.append(left + "".join(canvas))

    return row_lines


def _render_complex(cx: ChainComplex) -> str:
    """
    Render a ChainComplex as a readable ASCII diagram.

    Degrees are shown top-to-bottom (highest first). Between each adjacent
    pair of degrees, either ASCII lines (if both layers have ≤3 generators)
    or a matrix block is printed.
    """
    MATRIX_THRESHOLD = 3   # use matrix if src OR tgt exceeds this

    degs = sorted(cx.objects.keys())  # lowest first = bottom of diagram at top of output
    if not degs:
        return "(empty complex)"

    # --- compute node labels and layout ---
    NODE_SEP = 6    # horizontal spacing between node centers
    INDENT = 4      # left margin for degree label

    # Per-degree: list of labels and their x-centers
    deg_labels: Dict[int, list] = {}
    deg_centers: Dict[int, list] = {}

    for d in degs:
        gens = go_generators_at(cx.objects, d)
        labels = [_gen_label(g) for g in gens]
        deg_labels[d] = labels
        deg_centers[d] = []   # filled below after we know total width

    # Width: enough to fit the widest degree
    max_n = max(len(go_generators_at(cx.objects, d)) for d in degs)
    # Each node label ~ 3 chars, NODE_SEP apart
    node_w = max(len(l) for d in degs for l in deg_labels[d]) if degs else 3
    total_node_width = max_n * (node_w + NODE_SEP)
    canvas_width = max(total_node_width, 40)

    # Assign centers: use the SAME set of evenly-spaced slots for all degrees,
    # based on max_n, so lines stay vertical/diagonal rather than skewing.
    slot_centers: list = []
    if max_n == 1:
        slot_centers = [canvas_width // 2]
    else:
        margin = (node_w + NODE_SEP) // 2
        span = canvas_width - 2 * margin
        step = span // (max_n - 1)
        slot_centers = [margin + i * step for i in range(max_n)]

    for d in degs:
        n = len(deg_labels[d])
        if n == 0:
            deg_centers[d] = []
        elif n == 1:
            # Single node always goes in the centre slot
            deg_centers[d] = [canvas_width // 2]
        else:
            # Centre the n nodes within the max_n slots
            offset = (max_n - n) // 2
            deg_centers[d] = slot_centers[offset: offset + n]

    lines = []
    deg_label_w = max(len(f"deg {d}:") for d in degs)

    for di, d in enumerate(degs):
        labels = deg_labels[d]
        centers = deg_centers[d]

        # --- degree row ---
        row = list(" " * canvas_width)
        for lbl, cx_ in zip(labels, centers):
            start = cx_ - len(lbl) // 2
            for ci, ch in enumerate(lbl):
                pos = start + ci
                if 0 <= pos < canvas_width:
                    row[pos] = ch
        prefix = f"deg {d}:".ljust(deg_label_w + 1)
        lines.append(prefix + "".join(row))

        # --- transition to next degree (which is higher, printed below) ---
        if di + 1 < len(degs):
            d_upper = degs[di + 1]
            # The differential goes d_upper -> d (downward in degree).
            # On screen d is printed first (top), d_upper below it.
            # So src of the differential = d_upper (bottom row on screen),
            # tgt = d (top row on screen). We draw lines top=tgt, bottom=src.
            src_labels = deg_labels[d_upper]   # higher degree = bottom on screen
            tgt_labels = deg_labels[d]         # lower degree  = top on screen
            src_centers = deg_centers[d_upper]
            tgt_centers = deg_centers[d]
            n_src = len(src_labels)
            n_tgt = len(tgt_labels)

            # maps[sp][tp]: differential from d_upper pos sp -> d pos tp
            maps = [[cx.differential.get(d_upper, sp, tp)
                     for tp in range(n_tgt)]
                    for sp in range(n_src)]

            has_any = any(maps[sp][tp] for sp in range(n_src) for tp in range(n_tgt))

            if not has_any:
                lines.append(prefix + "")
            elif n_src <= MATRIX_THRESHOLD and n_tgt <= MATRIX_THRESHOLD:
                pad = " " * (deg_label_w + 1)
                # Transpose maps: for display, tgt (lower deg, top on screen)
                # is the "from" row and src (higher deg, bottom on screen) is "to".
                maps_T = [[maps[sp][tp] for sp in range(n_src)] for tp in range(n_tgt)]
                connector_rows = _render_transition_lines(
                    tgt_labels, src_labels, maps_T,
                    tgt_centers, src_centers, canvas_width
                )
                for r in connector_rows:
                    lines.append(pad + r)
            else:
                pad = " " * (deg_label_w + 1)
                lines.append("")   # blank line between upper degree row and matrix
                mat_lines = _render_transition_matrix(
                    src_labels, src_centers,
                    tgt_labels, maps,
                    deg_label_w, canvas_width,
                )
                lines.extend(mat_lines)
                lines.append("")   # blank line between matrix and lower degree row

    return "\n".join(lines)


def print_morphisms(cx: ChainComplex) -> None:
    """Print all nonzero differential components of a chain complex."""
    """Print all nonzero differential components of a chain complex."""
    print("=== Chain Complex ===")
    print("Objects:")
    print(cx.repr_objects())
    print("\nDifferential (nonzero components):")
    found_any = False
    for deg in sorted(cx.objects.keys()):
        src_gens = go_generators_at(cx.objects, deg)
        tgt_gens = go_generators_at(cx.objects, deg - 1)
        for sp in range(len(src_gens)):
            for tp in range(len(tgt_gens)):
                m = cx.differential.get(deg, sp, tp)
                if m:
                    found_any = True
                    sg = src_gens[sp]
                    tg = tgt_gens[tp]
                    print(
                        f"  d: T({sg:+d}) at deg {deg:+d} [slot {sp}]"
                        f" -> T({tg:+d}) at deg {deg-1:+d} [slot {tp}]"
                        f"  :  {mc_repr(m)}"
                    )
    if not found_any:
        print("  (zero differential)")


# ---------------------------------------------------------------------------
# 9.  Example / smoke test
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    # --- Build a trivial functor: identity-like on T(0) ---
    # mu1[0] = complex  0 -> T(0) -> 0  concentrated at degree 0
    mu1_T0 = ChainComplex.single_generator(0, 0)
    mu1_T1 = ChainComplex.single_generator(1, 0)
    mu1_Tm1 = ChainComplex.single_generator(-1, 0)

    functor = AInfinityData(
        mu1={0: mu1_T0, 1: mu1_T1, -1: mu1_Tm1},
        mu2={}
    )

    # --- Build a simple input complex: 0 -> T(0) -f-> T(0) -> 0 ---
    # Two copies of T(0): one at degree 1, one at degree 0.
    # Differential: d(T(0) at deg 1) = f(0,0,2) * T(0) at deg 0
    input_obj: GradedObject = {1: [0], 0: [0]}
    input_diff = ChainMap(source=input_obj, target=input_obj, shift=-1)
    input_diff.set(1, 0, 0, {(0, 0, 2): 1})   # d = f(T0->T0, index=2)

    input_cx = ChainComplex(objects=input_obj, differential=input_diff)
    print("Input complex:")
    print_morphisms(input_cx)
    print()

    # --- Apply the functor ---
    output_cx = apply_functor(input_cx, functor)
    print("Output complex:")
    print_morphisms(output_cx)

    # --- Composition law check ---
    print("\n--- Composition index check ---")
    # T(0) -> T(1) -> T(-1): extra = (|0-1| + |1-(-1)| - |0-(-1)|) / 2 = (1+2-1)/2 = 1
    extra = (abs(0 - 1) + abs(1 - (-1)) - abs(0 - (-1))) // 2
    print(f"T(0)->T(+1)->T(-1): extra term = {extra}  (expected 1)")
    # T(-1) -> T(0) -> T(1): extra = (1+1-2)/2 = 0
    extra2 = (abs(-1 - 0) + abs(0 - 1) - abs(-1 - 1)) // 2
    print(f"T(-1)->T(0)->T(+1): extra term = {extra2}  (expected 0)")