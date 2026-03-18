"""
functors.py
-----------
Hard-coded A-infinity functor data.

Each functor is an AInfinityData instance built from three tables:
  beta0 : Generator -> ChainComplex
  beta1 : (src_gen, tgt_gen, map_index) -> ChainMap   (degree 0)
  beta2 : (src_gen, mid_gen, tgt_gen, idx1, idx2) -> ChainMap  (degree -1)

Currently defined:
  BETA_PLUS   : the beta+ functor

Naming conventions
------------------
Inside each builder function we name local complexes after their generator
for readability, then assemble them into an AInfinityData at the end.

All map indices follow the convention from chain_complex.py:
  MapKey = (source_generator: int, target_generator: int, map_index: int)
"""

from chain_complex import (
    AInfinityData,
    ChainComplex,
    ChainMap,
    GradedObject,
    MapCoeff,
)


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

def _trivial_complex(gen: int, degree: int = 0) -> ChainComplex:
    """Single generator concentrated at `degree`, zero differential."""
    obj: GradedObject = {degree: [gen]}
    diff = ChainMap(source=obj, target=obj, shift=-1)
    return ChainComplex(objects=obj, differential=diff)


def _make_chain_map(
    source: ChainComplex,
    target: ChainComplex,
    shift: int,
    entries: list[tuple[int, int, int, MapCoeff]],
) -> ChainMap:
    """
    Build a ChainMap from a list of (src_deg, src_pos, tgt_pos, MapCoeff).
    Zero MapCoeff entries are silently ignored.
    """
    cm = ChainMap(source=source.objects, target=target.objects, shift=shift)
    for src_deg, src_pos, tgt_pos, mc in entries:
        if mc:
            cm.set(src_deg, src_pos, tgt_pos, mc)
    return cm


# ---------------------------------------------------------------------------
# beta+
# ---------------------------------------------------------------------------
#
# Generators:  T(-1), T(0), T(1)
#
# beta0:
#   T(-1)  ->  T(-1)                          (trivial, degree 0)
#   T(0)   ->  [T(-1) ⊕ T(1)] -> T(0)
#                deg 0: T(-1) at pos 0, T(1) at pos 1
#                deg-1: T(0)  at pos 0
#                differential: d(T(-1),0) = f(T(-1)->T(0), 0)
#                              d(T(1), 0) = f(T(1) ->T(0), 0)
#   T(1)   ->  T(1)                           (trivial, degree 0)
#
# beta1  (degree-0 chain maps between the beta0 images):
#   T(i)->T(i) index j   :  same map between outputs, index j
#   T(-1)->T(1) index 0  :  f(T(-1)->T(1), 0)  (trivial complexes, direct)
#   T(1)->T(-1) index 0  :  f(T(1)->T(-1), 0)  (trivial complexes, direct)
#   T(0)->T(1)  index 0  :  T(1)[deg0] -> T(1)[deg0] index 0; rest zero
#   T(0)->T(-1) index 0  :  T(-1)[deg0] -> T(-1)[deg0] index 0; rest zero
#   T(1)->T(0)  index 0  :  T(1)[deg0] -> T(-1)[deg0] index 0
#                           T(1)[deg0] -> T(1) [deg0] index 1
#   T(-1)->T(0) index 0  :  T(-1)[deg0] -> T(-1)[deg0] index 1
#                           T(-1)[deg0] -> T(1) [deg0] index 0
#
# beta2  (degree-(-1) chain maps):
#   T(0)->T(1)->T(-1)   :  T(0)[deg-1] -> T(-1)[deg0] index 0
#                          i.e. src_deg=0 (shift -1 means deg-1 of source maps
#                          to deg-1-1=-... wait: src complex has generators at
#                          deg 0 and deg -1. shift=-1 means src_deg maps to
#                          tgt at src_deg-1. We want T(0) generator (deg -1 in
#                          beta0(T(0))) to map to T(-1) generator (deg 0 in
#                          beta0(T(-1))). With shift=-1: src_deg=1 maps to
#                          tgt_deg=0. But T(0) sits at deg -1 in beta0(T(0)),
#                          not deg 1. So we use src_deg=0: maps to tgt_deg=-1,
#                          but T(-1) is at deg 0. Contradiction.
#
#          Resolution: beta2 is a chain map of degree +1 from beta0(T(0)) to
#          beta0(T(∓1)), i.e. it raises degree by 1. In our framework we encode
#          this as shift=+1. Then src_deg=-1 (where T(0) lives in beta0(T(0)))
#          maps to tgt_deg=0 (where T(∓1) lives). ✓
#
#   T(0)->T(-1)->T(0)   :  beta0(T(0))[deg-1] -> beta0(T(1))[deg 0] index 0  (shift +1)
#   T(0)->T(1)->T(0)    :  beta0(T(0))[deg-1] -> beta0(T(-1))[deg 0] index 0 (shift +1)
#   T(0)->T(1)->T(-1) and T(0)->T(-1)->T(1) covered above.
#   All others: zero.

def _build_beta_plus() -> AInfinityData:

    # ------------------------------------------------------------------
    # beta0 images
    # ------------------------------------------------------------------

    b0_Tm1 = _trivial_complex(-1, degree=0)   # T(-1) at deg 0
    b0_T1  = _trivial_complex( 1, degree=0)   # T(1)  at deg 0

    # beta0(T(0)): deg 0 has [T(-1), T(1)], deg -1 has [T(0)]
    b0_T0_obj: GradedObject = {0: [-1, 1], -1: [0]}
    b0_T0_diff = ChainMap(source=b0_T0_obj, target=b0_T0_obj, shift=-1)
    # d at src_deg=0:
    #   pos 0 (T(-1)) -> pos 0 (T(0) at deg-1):  f(T(-1)->T(0), 0)
    #   pos 1 (T(1))  -> pos 0 (T(0) at deg-1):  f(T(1) ->T(0), 0)
    b0_T0_diff.set(0, 0, 0, {(-1,  0, 0): 1})
    b0_T0_diff.set(0, 1, 0, {( 1,  0, 0): 1})
    b0_T0 = ChainComplex(objects=b0_T0_obj, differential=b0_T0_diff)

    mu1 = {-1: b0_Tm1, 0: b0_T0, 1: b0_T1}

    # ------------------------------------------------------------------
    # beta1 entries  (degree-0 chain maps)
    # ------------------------------------------------------------------
    # Key: (src_gen, tgt_gen, map_index)

    mu1_maps: dict = {}

    # T(i)->T(i) index j : same map, index j
    # We store these as factory entries; apply_functor will look them up.
    # For the three self-maps on trivial complexes:
    for gen in (-1, 1):
        cx = mu1[gen]
        for j in range(20):   # store enough; extend if needed
            cm = _make_chain_map(cx, cx, shift=0, entries=[
                (0, 0, 0, {(gen, gen, j): 1})
            ])
            mu1_maps[(gen, gen, j)] = cm

    # T(0)->T(0) index j: map on b0_T0
    # deg 0: each pos maps to itself with index j
    # deg -1: T(0) maps to T(0) with index j
    for j in range(20):
        cm = _make_chain_map(b0_T0, b0_T0, shift=0, entries=[
            (0,  0, 0, {(-1, -1, j): 1}),   # T(-1) pos -> T(-1) pos
            (0,  1, 1, {( 1,  1, j): 1}),   # T(1)  pos -> T(1)  pos
            (-1, 0, 0, {( 0,  0, j): 1}),   # T(0)  pos -> T(0)  pos
        ])
        mu1_maps[(0, 0, j)] = cm

    # T(-1)->T(1) index 0
    cm_m1_to_1 = _make_chain_map(b0_Tm1, b0_T1, shift=0, entries=[
        (0, 0, 0, {(-1, 1, 0): 1})
    ])
    mu1_maps[(-1, 1, 0)] = cm_m1_to_1

    # T(1)->T(-1) index 0
    cm_1_to_m1 = _make_chain_map(b0_T1, b0_Tm1, shift=0, entries=[
        (0, 0, 0, {(1, -1, 0): 1})
    ])
    mu1_maps[(1, -1, 0)] = cm_1_to_m1

    # T(0)->T(1) index 0: T(1)[deg0,pos1 in b0_T0] -> T(1)[deg0] index 0; rest zero
    # source: b0_T0 (deg 0: pos0=T(-1), pos1=T(1); deg-1: pos0=T(0))
    # target: b0_T1 (deg 0: pos0=T(1))
    # The T(1) component of b0_T0 is at pos 1, deg 0
    cm_0_to_1 = _make_chain_map(b0_T0, b0_T1, shift=0, entries=[
        (0, 1, 0, {(1, 1, 0): 1}),   # T(1)->T(1) index 0
        # all others zero
    ])
    mu1_maps[(0, 1, 0)] = cm_0_to_1

    # T(0)->T(-1) index 0: T(-1)[deg0,pos0 in b0_T0] -> T(-1)[deg0] index 0; rest zero
    cm_0_to_m1 = _make_chain_map(b0_T0, b0_Tm1, shift=0, entries=[
        (0, 0, 0, {(-1, -1, 0): 1}),  # T(-1)->T(-1) index 0
        # all others zero
    ])
    mu1_maps[(0, -1, 0)] = cm_0_to_m1

    # T(1)->T(0) index 0:
    #   T(1)[deg0] -> T(-1)[deg0, pos0 in b0_T0] index 0
    #   T(1)[deg0] -> T(1) [deg0, pos1 in b0_T0] index 1
    # source: b0_T1 (deg 0: pos0=T(1))
    # target: b0_T0 (deg 0: pos0=T(-1), pos1=T(1))
    cm_1_to_0 = _make_chain_map(b0_T1, b0_T0, shift=0, entries=[
        (0, 0, 0, {(1, -1, 0): 1}),   # T(1)->T(-1) index 0
        (0, 0, 1, {(1,  1, 1): 1}),   # T(1)->T(1)  index 1
    ])
    mu1_maps[(1, 0, 0)] = cm_1_to_0

    # T(-1)->T(0) index 0:
    #   T(-1)[deg0] -> T(-1)[deg0, pos0 in b0_T0] index 1
    #   T(-1)[deg0] -> T(1) [deg0, pos1 in b0_T0] index 0
    cm_m1_to_0 = _make_chain_map(b0_Tm1, b0_T0, shift=0, entries=[
        (0, 0, 0, {(-1, -1, 1): 1}),  # T(-1)->T(-1) index 1
        (0, 0, 1, {(-1,  1, 0): 1}),  # T(-1)->T(1)  index 0
    ])
    mu1_maps[(-1, 0, 0)] = cm_m1_to_0

    # ------------------------------------------------------------------
    # beta2 entries  (degree +1 chain maps, i.e. shift=+1)
    # Key: (src_gen, mid_gen, tgt_gen, idx1, idx2)
    #
    # All nonzero cases involve T(0) as source. The map goes from
    # beta0(T(0)) to beta0(T(tgt)), landing:
    #   src at deg -1 (T(0) generator) -> tgt at deg 0  (shift +1 confirmed)
    # ------------------------------------------------------------------

    mu2: dict = {}

    # T(0)->T(1)->T(-1): additional map T(0)[deg-1] -> T(-1)[deg0] index 0
    # Composition index: _composition_index(0, 1, -1, 0, 0)
    #   extra = (|0-1| + |1-(-1)| - |0-(-1)|) / 2 = (1+2-1)/2 = 1
    #   composed_idx = 0 + 0 + 1 = 1
    # Key: (src=0, tgt=-1, composed_idx=1)
    cm_mu2_T0_T1_Tm1 = _make_chain_map(b0_T0, b0_Tm1, shift=1, entries=[
        (-1, 0, 0, {(0, -1, 0): 1})   # T(0) at deg-1 -> T(-1) at deg 0
    ])
    mu2[(0, -1, 1)] = cm_mu2_T0_T1_Tm1

    # T(0)->T(-1)->T(1): additional map T(0)[deg-1] -> T(1)[deg0] index 0
    # _composition_index(0, -1, 1, 0, 0):
    #   extra = (|0-(-1)| + |(-1)-1| - |0-1|) / 2 = (1+2-1)/2 = 1
    #   composed_idx = 1
    # Key: (src=0, tgt=1, composed_idx=1)
    cm_mu2_T0_Tm1_T1 = _make_chain_map(b0_T0, b0_T1, shift=1, entries=[
        (-1, 0, 0, {(0, 1, 0): 1})    # T(0) at deg-1 -> T(1) at deg 0
    ])
    mu2[(0, 1, 1)] = cm_mu2_T0_Tm1_T1

    # T(0)->T(-1)->T(0): additional map beta0(T(0))[deg-1] -> beta0(T(0)) index 0
    # _composition_index(0, -1, 0, 0, 0):
    #   extra = (1 + 1 - 0) / 2 = 1
    #   composed_idx = 1
    # The target is b0_T0; the map lands in the T(1) component at deg 0 (pos 1)
    # "gives additional morphism T0->T1 index 0" means the output lands in T(1)
    # Key: (src=0, tgt=0 via T(-1), composed_idx=1) -- we need to distinguish
    # this from T(0)->T(1)->T(0) below. We key mu2 by (src_gen, tgt_gen, composed_idx)
    # but two paths can give the same key if composed_idx coincides. Here:
    # T(0)->T(-1)->T(0): composed_idx=1, tgt=0
    # T(0)->T(1)->T(0):  composed_idx=1, tgt=0  (same key!)
    # We must ADD them (they contribute to the same homotopy component).
    # We do this by building the map with both contributions and storing once.
    # _composition_index(0, 1, 0, 0, 0):
    #   extra = (1 + 1 - 0) / 2 = 1  -> composed_idx = 1  (same)
    # So key (0, 0, 1) gets contributions from BOTH paths.
    # T(0)->T(-1)->T(0) contributes: T(0)[deg-1] -> T(1)[deg0, pos1] index 0
    # T(0)->T(1) ->T(0) contributes: T(0)[deg-1] -> T(-1)[deg0, pos0] index 0
    cm_mu2_T0_x_T0 = _make_chain_map(b0_T0, b0_T0, shift=1, entries=[
        (-1, 0, 1, {(0,  1, 0): 1}),  # T0->T(-1)->T0: lands in T(1) pos, idx 0
        (-1, 0, 0, {(0, -1, 0): 1}),  # T0->T(1) ->T0: lands in T(-1) pos, idx 0
    ])
    mu2[(0, 0, 1)] = cm_mu2_T0_x_T0

    # ------------------------------------------------------------------
    # Assemble
    # ------------------------------------------------------------------
    return AInfinityData(mu1=mu1, mu1_maps=mu1_maps, mu2=mu2)


# ---------------------------------------------------------------------------
# beta-
# ---------------------------------------------------------------------------
#
# beta0:
#   T(-1)  ->  T(-1)                          (trivial, degree 0)
#   T(0)   ->  T(0) -> [T(-1) ⊕ T(1)]
#                deg  1: T(0)  at pos 0
#                deg  0: T(-1) at pos 0, T(1) at pos 1
#                differential: d(T(0), deg1) = f(T(0)->T(-1), 0) at pos 0
#                                              f(T(0)->T(1),  0) at pos 1
#   T(1)   ->  T(1)                           (trivial, degree 0)
#
# beta1:
#   T(i)->T(i) index j        : same map, index j  (all generators)
#   T(-1)->T(1) index 0       : f(T(-1)->T(1), 0)  direct
#   T(1)->T(-1) index 0       : f(T(1)->T(-1), 0)  direct
#   T(0)->T(1)  index 0       : sum -> T(1):  T(-1)[pos0] -> T(1) idx 0
#                                              T(1) [pos1] -> T(1) idx 1
#   T(0)->T(-1) index 0       : sum -> T(-1): T(-1)[pos0] -> T(-1) idx 1
#                                              T(1) [pos1] -> T(-1) idx 0
#   T(1)->T(0)  index 0       : T(1) -> T(1)[pos1 in sum, deg0] idx 0  (only nonzero)
#   T(-1)->T(0) index 0       : T(-1) -> T(-1)[pos0 in sum, deg0] idx 0 (only nonzero)
#
# beta2  (shift=+1 maps, same convention as beta+):
#   T(+1)->T(-1)->T(0): T(+1)[deg0] -> T(0)[deg1, pos0] index 0
#   T(-1)->T(+1)->T(0): T(-1)[deg0] -> T(0)[deg1, pos0] index 0
#     Both paths share composed_idx=1 and tgt=0, combined into key (src, 0, 1).
#     src=+1 key: (+1, 0, 1)   src=-1 key: (-1, 0, 1)
#
#   T(0)->T(-1)->T(0): sum T(1)[pos1,deg0]  -> T(0)[deg1] idx 0   key (0,0,1) via T(-1)
#   T(0)->T(1)->T(0):  sum T(-1)[pos0,deg0] -> T(0)[deg1] idx 0   key (0,0,1) via T(1)
#     Both contribute to key (0, 0, 1), combined into one map.

def _build_beta_minus() -> AInfinityData:

    # ------------------------------------------------------------------
    # beta0 images
    # ------------------------------------------------------------------
    b0_Tm1 = _trivial_complex(-1, degree=0)
    b0_T1  = _trivial_complex( 1, degree=0)

    # beta0(T(0)): deg 1 has [T(0)], deg 0 has [T(-1), T(1)]
    b0_T0_obj: GradedObject = {1: [0], 0: [-1, 1]}
    b0_T0_diff = ChainMap(source=b0_T0_obj, target=b0_T0_obj, shift=-1)
    # d at src_deg=1:
    #   pos 0 (T(0)) -> pos 0 (T(-1) at deg 0):  f(T(0)->T(-1), 0)
    #   pos 0 (T(0)) -> pos 1 (T(1)  at deg 0):  f(T(0)->T(1),  0)
    b0_T0_diff.set(1, 0, 0, {(0, -1, 0): 1})
    b0_T0_diff.set(1, 0, 1, {(0,  1, 0): 1})
    b0_T0 = ChainComplex(objects=b0_T0_obj, differential=b0_T0_diff)

    mu1 = {-1: b0_Tm1, 0: b0_T0, 1: b0_T1}

    # ------------------------------------------------------------------
    # beta1 entries
    # ------------------------------------------------------------------
    mu1_maps: dict = {}

    # T(i)->T(i) index j — self maps on trivial complexes
    for gen in (-1, 1):
        cx = mu1[gen]
        for j in range(20):
            cm = _make_chain_map(cx, cx, shift=0, entries=[
                (0, 0, 0, {(gen, gen, j): 1})
            ])
            mu1_maps[(gen, gen, j)] = cm

    # T(0)->T(0) index j — self maps on b0_T0
    # deg 1: T(0) -> T(0) index j
    # deg 0: T(-1)->T(-1) index j, T(1)->T(1) index j
    for j in range(20):
        cm = _make_chain_map(b0_T0, b0_T0, shift=0, entries=[
            (1, 0, 0, {(0,  0, j): 1}),   # T(0) at deg1 -> T(0) at deg1
            (0, 0, 0, {(-1,-1, j): 1}),   # T(-1) pos0   -> T(-1) pos0
            (0, 1, 1, {( 1, 1, j): 1}),   # T(1)  pos1   -> T(1)  pos1
        ])
        mu1_maps[(0, 0, j)] = cm

    # T(-1)->T(1) index 0
    mu1_maps[(-1, 1, 0)] = _make_chain_map(b0_Tm1, b0_T1, shift=0, entries=[
        (0, 0, 0, {(-1, 1, 0): 1})
    ])

    # T(1)->T(-1) index 0
    mu1_maps[(1, -1, 0)] = _make_chain_map(b0_T1, b0_Tm1, shift=0, entries=[
        (0, 0, 0, {(1, -1, 0): 1})
    ])

    # T(0)->T(1) index 0:
    # source: b0_T0 sum part (deg 0): pos0=T(-1), pos1=T(1)
    # target: b0_T1 (deg 0): pos0=T(1)
    # T(-1)[pos0] -> T(1)[pos0] idx 0
    # T(1) [pos1] -> T(1)[pos0] idx 1
    mu1_maps[(0, 1, 0)] = _make_chain_map(b0_T0, b0_T1, shift=0, entries=[
        (0, 0, 0, {(-1, 1, 0): 1}),   # T(-1) -> T(1) idx 0
        (0, 1, 0, {( 1, 1, 1): 1}),   # T(1)  -> T(1) idx 1
    ])

    # T(0)->T(-1) index 0:
    # T(-1)[pos0] -> T(-1) idx 1
    # T(1) [pos1] -> T(-1) idx 0
    mu1_maps[(0, -1, 0)] = _make_chain_map(b0_T0, b0_Tm1, shift=0, entries=[
        (0, 0, 0, {(-1, -1, 1): 1}),  # T(-1) -> T(-1) idx 1
        (0, 1, 0, {( 1, -1, 0): 1}),  # T(1)  -> T(-1) idx 0
    ])

    # T(1)->T(0) index 0:
    # source: b0_T1 (deg 0): pos0=T(1)
    # target: b0_T0 sum part (deg 0): pos1=T(1)
    # only nonzero: T(1)[pos0] -> T(1)[pos1] idx 0
    mu1_maps[(1, 0, 0)] = _make_chain_map(b0_T1, b0_T0, shift=0, entries=[
        (0, 0, 1, {(1, 1, 0): 1}),    # T(1) -> T(1)[pos1] idx 0
    ])

    # T(-1)->T(0) index 0:
    # only nonzero: T(-1)[pos0] -> T(-1)[pos0] idx 0
    mu1_maps[(-1, 0, 0)] = _make_chain_map(b0_Tm1, b0_T0, shift=0, entries=[
        (0, 0, 0, {(-1, -1, 0): 1}),  # T(-1) -> T(-1)[pos0] idx 0
    ])

    # ------------------------------------------------------------------
    # beta2 entries  (shift=+1)
    #
    # T(+1)->T(-1)->T(0): composed_idx = _composition_index(1,-1,0,0,0)
    #   extra = (|1-(-1)| + |(-1)-0| - |1-0|) / 2 = (2+1-1)/2 = 1  -> idx=1
    #   key: (1, 0, 1)
    #   map: T(1)[deg0] -> T(0)[deg1, pos0] idx 0
    #   shift=+1: src int_deg=0 -> tgt int_deg=1  ✓  (T(0) is at deg1 in b0_T0)
    #
    # T(-1)->T(+1)->T(0): composed_idx = _composition_index(-1,1,0,0,0)
    #   extra = (1+1-1)/2 = ... wait: (|-1-1| + |1-0| - |-1-0|)/2 = (2+1-1)/2 = 1
    #   key: (-1, 0, 1)
    #   map: T(-1)[deg0] -> T(0)[deg1, pos0] idx 0
    #
    # T(0)->T(-1)->T(0): composed_idx = _composition_index(0,-1,0,0,0)
    #   extra = (1+1-0)/2 = 1  -> idx=1   key: (0, 0, 1)
    #   source: sum T(1)[pos1, deg0] of b0_T0  (int_deg=0, pos=1)
    #   target: T(0)[deg1, pos0]               (int_deg=1, pos=0)
    #   shift=+1: int_deg 0 -> int_deg 1  ✓
    #
    # T(0)->T(1)->T(0): same composed_idx=1, same key (0,0,1)
    #   source: sum T(-1)[pos0, deg0] of b0_T0
    #   target: T(0)[deg1, pos0]
    #   Combined with above into one map at key (0,0,1).
    # ------------------------------------------------------------------
    mu2: dict = {}

    mu2[(1, 0, 1)] = _make_chain_map(b0_T1, b0_T0, shift=1, entries=[
        (0, 0, 0, {(1, 0, 0): 1})     # T(1)[deg0] -> T(0)[deg1, pos0] idx 0
    ])

    mu2[(-1, 0, 1)] = _make_chain_map(b0_Tm1, b0_T0, shift=1, entries=[
        (0, 0, 0, {(-1, 0, 0): 1})    # T(-1)[deg0] -> T(0)[deg1, pos0] idx 0
    ])

    # Combined T(0)->T(±1)->T(0) contributions
    mu2[(0, 0, 1)] = _make_chain_map(b0_T0, b0_T0, shift=1, entries=[
        (0, 1, 0, {(1,  0, 0): 1}),   # T(0)->T(-1)->T(0): T(1)[pos1]  -> T(0)[pos0]
        (0, 0, 0, {(-1, 0, 0): 1}),   # T(0)->T(1) ->T(0): T(-1)[pos0] -> T(0)[pos0]
    ])

    return AInfinityData(mu1=mu1, mu1_maps=mu1_maps, mu2=mu2)


# ---------------------------------------------------------------------------
# Registry
# ---------------------------------------------------------------------------

BETA_PLUS  = _build_beta_plus()
BETA_MINUS = _build_beta_minus()

FUNCTORS: dict[str, AInfinityData] = {
    "beta_plus":  BETA_PLUS,
    "beta_minus": BETA_MINUS,
}