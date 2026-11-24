module

public import Mathlib
public import KLRW.KLRWCategory

/-!
# U-brane diagrams and their cubes

A U-brane diagram is a collection of non-crossing arcs ("U-branes") on a disk with labelled
marked points. Each brane can sit at its right end (state `0`) or at its left end (state `1`),
so a diagram with `k` branes gives a `k`-dimensional cube of KLRW objects: at each vertex, the
red strands of the marked points and one black strand per brane, laid out from left to right.
Each edge of the cube moves one brane's strand from its right end to its left end, and gives a
morphism of the KLRW category made of crossings.

This part also defines peelings: sequences of diagrams in which the branes on one arc are moved
("peeled") one at a time to a new arc further right, together with the maps between consecutive
stages.

## Main definitions

* `KLRW.CubeVertex m` and `KLRW.IsEdge`: vertices and edges of the `m`-dimensional cube.
* `KLRW.UBraneDiagram disk labels`: non-crossing U-branes on `disk`, with labels `labels`.
* `KLRW.KLRWStructure.ofDisk`: the KLRW structure shared by all diagrams on `disk` with labels
  `labels`.
* `KLRW.vertexObject`: the KLRW object at a vertex of the cube.
* `KLRW.edgeHom`: the morphism along an edge of the cube.
* `KLRW.PeelData` and `KLRW.PeelData.diagram`: a peeling and its stages.
* `KLRW.peelHom`: the map from stage `j` to stage `j + 1` of a peeling, at a vertex.

## Implementation notes

* Strands are named by slots `Fin n ⊕ Fin k`: red strands and branes. At each vertex every slot
  gets a sort key (`slotKey`: its section first, then its order within the section), and its
  position is the number of slots with a smaller key. This makes `layout` a bijection between
  positions and slots.
* An edge of the cube, or a stage of a peeling, changes the key of exactly one slot, so every
  other strand stays put or shifts by one; `crossesBetween` performs exactly this move.
* The labels are part of the type of a diagram, so all diagrams on the same disk with the same
  labels, in particular all stages of a peeling, live in the same KLRW category.
-/

@[expose] public section

namespace KLRW

/-! ## Cube vertices and edges -/

section CubeVertices

/-- A vertex of the `m`-dimensional cube: a choice of `0` or `1` in each direction. -/
abbrev CubeVertex (m : ℕ) : Type := Fin m → Fin 2

section IsEdgeFunctions

section

variable {m : ℕ} (v w : CubeVertex m)

/-- The vertex obtained by putting `b` in front of `v`; for example
`vcons 0 (0 1 0 1) = (0 0 1 0 1)`. -/
abbrev vcons (b : Fin 2) (v : CubeVertex m) : CubeVertex (m + 1) :=
  Fin.cons (α := fun _ => Fin 2) b v

/-- There is an edge from `v` to `w` in direction `i`: `v` is `0` there and `w` is `v` with
direction `i` set to `1`. -/
structure IsEdgeAt (i : Fin m) : Prop where
  /-- `v` is `0` in direction `i`. -/
  zero : v i = 0
  /-- `w` is `v` with direction `i` set to `1`. -/
  eq : w = Function.update v i 1

/-- Whether there is an edge in direction `i` can be decided. -/
instance (i : Fin m) : Decidable (IsEdgeAt v w i) :=
  decidable_of_iff (v i = 0 ∧ w = Function.update v i 1)
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun h => ⟨h.zero, h.eq⟩⟩

end

variable {m : ℕ} {v w : CubeVertex m}

/-- An edge has only one direction. -/
lemma IsEdgeAt.dir_unique {i j : Fin m} (hi : IsEdgeAt v w i) (hj : IsEdgeAt v w j) :
    i = j := by
  by_contra hne
  have h1 : w i = 1 := by simp [hi.eq]
  have h2 : w i = 0 := by simp [hj.eq, hne, hi.zero]
  exact absurd (h1.symm.trans h2) (by decide)

/-- Putting the same value in front of both ends of an edge gives an edge. -/
lemma IsEdgeAt.cons {i : Fin m} (b : Fin 2) (h : IsEdgeAt v w i) :
    IsEdgeAt (vcons b v) (vcons b w) i.succ := by
  obtain ⟨h0, rfl⟩ := h
  refine ⟨by simpa [vcons] using h0, ?_⟩
  funext j
  cases j using Fin.cases
  · simp [vcons, (Fin.succ_ne_zero i).symm]
  · simp [vcons, Function.update_apply]

/-- There is an edge in direction `0` from `(0, v)` to `(1, v)`. -/
lemma IsEdgeAt.dir0 (v : CubeVertex m) : IsEdgeAt (vcons 0 v) (vcons 1 v) 0 := by
  refine ⟨rfl, ?_⟩
  funext j
  cases j using Fin.cases
  · simp [vcons]
  · simp [vcons]

/-- There is an edge from `v` to `w` in some direction. -/
def IsEdge (v w : CubeVertex m) : Prop := ∃ i, IsEdgeAt v w i

/-- The direction of an edge. -/
def IsEdge.dir (h : IsEdge v w) : Fin m :=
  Fintype.choose (fun i => IsEdgeAt v w i) (by
    obtain ⟨i, hi⟩ := h
    exact ⟨i, hi, fun j hj => IsEdgeAt.dir_unique hj hi⟩)

/-- The edge goes in direction `h.dir`. -/
lemma IsEdge.dir_spec (h : IsEdge v w) : IsEdgeAt v w h.dir :=
  Fintype.choose_spec _ _

/-- If the edge goes in direction `i`, then `h.dir = i`. -/
lemma IsEdge.dir_eq {i : Fin m} (h : IsEdge v w) (hi : IsEdgeAt v w i) : h.dir = i :=
  IsEdgeAt.dir_unique h.dir_spec hi

/-- `IsEdgeAt.cons` without the direction. -/
lemma IsEdge.cons (b : Fin 2) (h : IsEdge v w) : IsEdge (vcons b v) (vcons b w) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i.succ, hi.cons b⟩

/-- `IsEdgeAt.dir0` without the direction. -/
lemma IsEdge.dir0 (v : CubeVertex m) : IsEdge (vcons 0 v) (vcons 1 v) :=
  ⟨0, IsEdgeAt.dir0 v⟩

end IsEdgeFunctions

end CubeVertices

/-! ## U-branes -/

section UBranes

variable {V : Type} [DecidableEq V] [Fintype V]
variable {n : ℕ}

/-- A disk with `n` marked points, each carrying a label in `V`. -/
abbrev MarkedDisk := Fin n → V

/-- A U-brane on a disk with `n` marked points: an arc from section `left` to section `right`.
Its label is not part of the brane; it is recorded by the diagram the brane belongs to. -/
structure UBrane (n : ℕ) where
  /-- The section where the brane starts. -/
  left : Fin (n + 1)
  /-- The section where the brane ends. -/
  right : Fin (n + 1)
  /-- The brane goes from left to right. -/
  left_lt_right : left < right
  deriving DecidableEq

/-- A diagram of `k` non-crossing U-branes on `disk`, where brane `i` carries the label
`labels i`. All diagrams with the same `disk` and `labels` have the same KLRW structure
`KLRWStructure.ofDisk Γ disk labels`, so their cubes live in the same KLRW category.

The index `i` is the identity of a brane: it fixes its label and its coordinate in the cube,
and it never changes. How branes are nested is recorded separately by `nest`, because moving
branes around (as in a peeling) changes the nesting but not the branes. -/
structure UBraneDiagram (disk : @MarkedDisk V n) {k : ℕ} (labels : Fin k → V) where
  /-- The position of each brane. -/
  branes : Fin k → UBrane n
  /-- No two branes cross. -/
  non_intersecting : ∀ i j : Fin k,
    ¬ ((branes i).left < (branes j).left ∧ (branes j).left < (branes i).right ∧
       (branes i).right < (branes j).right)
  /-- The nesting order: among branes ending in the same section, the one with smaller
  `nest` value is further inside. -/
  nest : Fin k → Fin k
  /-- Two different branes that share an end have different `nest` values, so the strands in
  each section are ordered unambiguously. -/
  nest_injective : ∀ i j : Fin k, i ≠ j →
    (branes i).left = (branes j).left ∨ (branes i).right = (branes j).right → nest i ≠ nest j

/-- The KLRW structure of a disk with `k` black strands labelled by `labels`: one black strand
per entry of `labels` and one red strand per marked point of `disk`. -/
def KLRWStructure.ofDisk {k : ℕ} (Γ : SimpleDigraph V) (disk : @MarkedDisk V n)
    (labels : Fin k → V) : KLRWStructure V where
  Γ := Γ
  blackStrands := fun v => (Finset.univ.filter (fun i : Fin k => labels i = v)).card
  redStrands := fun v => (Finset.univ.filter (fun i : Fin n => disk i = v)).card

/-- A disk with `k` labelled black strands has `n + k` strands: `n` red ones and `k` black
ones. -/
lemma KLRWStructure.numStrands_ofDisk {k : ℕ} (Γ : SimpleDigraph V) (disk : @MarkedDisk V n)
    (labels : Fin k → V) : (KLRWStructure.ofDisk Γ disk labels).numStrands = n + k := by
  simp only [KLRWStructure.numStrands, KLRWStructure.ofDisk, Finset.sum_add_distrib]
  rw [← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)),
    ← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  simp [Nat.add_comm]

/-! ### Peeling U-branes

Every brane starts on the same arc, from section `oldLeft` to section `oldRight`, nested so that
brane `0` is innermost and brane `k - 1` outermost. The branes are moved ("peeled") one at a
time, outermost first, to a new arc from `newLeft` to `newRight`, which lies to the right of
the old one. Each newly peeled brane goes around the ones peeled before it, so on the new arc
the nesting is reversed: brane `k - 1` ends up innermost. -/

section Peeling

/-- The two arcs of a peeling: the arc every brane starts on, and the arc to its right that the
branes are moved to. -/
structure PeelData (n : ℕ) where
  /-- The left end of the starting arc. -/
  oldLeft : Fin (n + 1)
  /-- The right end of the starting arc. -/
  oldRight : Fin (n + 1)
  /-- The left end of the new arc. -/
  newLeft : Fin (n + 1)
  /-- The right end of the new arc. -/
  newRight : Fin (n + 1)
  /-- The starting arc goes from left to right. -/
  oldLeft_lt_oldRight : oldLeft < oldRight
  /-- The new arc lies to the right of the starting arc. -/
  oldRight_le_newLeft : oldRight ≤ newLeft
  /-- The new arc goes from left to right. -/
  newLeft_lt_newRight : newLeft < newRight

variable (disk : @MarkedDisk V n) {k : ℕ} (labels : Fin k → V) (p : PeelData n)

/-- The brane on the starting arc. -/
def PeelData.oldBrane : UBrane n := ⟨p.oldLeft, p.oldRight, p.oldLeft_lt_oldRight⟩

/-- The brane on the new arc. -/
def PeelData.newBrane : UBrane n := ⟨p.newLeft, p.newRight, p.newLeft_lt_newRight⟩

/-- The nesting order after peeling the outermost `j` branes. Unpeeled branes, on the starting
arc, are nested by index (`0` innermost). Peeled branes, on the new arc, are nested in reverse
(`k - 1` innermost). A brane's value only changes when it is peeled, which is what makes the
other strands stay in place during a stage map. -/
def peelNest (k j : ℕ) (i : Fin k) : Fin k :=
  if h : i.val < k - j then i else ⟨k - 1 - i.val, by omega⟩

/-- The diagram after peeling the outermost `j` branes: brane `i` is on the new arc if
`k - j ≤ i` and on the starting arc otherwise. -/
def PeelData.diagram (j : ℕ) : UBraneDiagram disk labels where
  branes i := if i.val < k - j then p.oldBrane else p.newBrane
  non_intersecting i i' := by
    have h₁ := p.oldLeft_lt_oldRight
    have h₂ := p.oldRight_le_newLeft
    have h₃ := p.newLeft_lt_newRight
    simp only [PeelData.newBrane, PeelData.oldBrane]
    split_ifs <;> simp only [Fin.lt_def, Fin.le_def] at * <;> omega
  nest := peelNest k j
  nest_injective i i' hne hsec heq := by
    have h₁ := p.oldLeft_lt_oldRight
    have h₂ := p.oldRight_le_newLeft
    have h₃ := p.newLeft_lt_newRight
    apply hne
    simp only [PeelData.newBrane, PeelData.oldBrane, peelNest] at hsec heq
    split_ifs at hsec heq <;>
      simp only [Fin.ext_iff, Fin.lt_def, Fin.le_def] at * <;> omega

end Peeling

section KLRWFromUBranes

variable {disk : @MarkedDisk V n}

/-- The section of the disk where brane `b` sits: its right end in state `0`, its left end in
state `1`. -/
def braneSection (b : UBrane n) (v : Fin 2) : Fin (n + 1) :=
  if v = 0 then b.right else b.left

/-! ### The object at each vertex of the cube -/

section VertexObjects

section Layout

variable {k : ℕ} {labels : Fin k → V}

/-- The strands of a U-brane diagram: `.inl j` is the red strand of marked point `j`, and
`.inr i` is the black strand of brane `i`. -/
abbrev Slot (n k : ℕ) := Fin n ⊕ Fin k

/-- The label and color carried by each slot. It depends only on `disk` and `labels`, not on
where the branes are. -/
def slotData (disk : @MarkedDisk V n) (labels : Fin k → V) : Slot n k → StrandData V
  | .inl j => ⟨disk j, .red⟩
  | .inr i => ⟨labels i, .black⟩

omit [DecidableEq V] [Fintype V] in
/-- The data of the red strand of marked point `j`. -/
@[simp]
lemma slotData_inl (disk : @MarkedDisk V n) (labels : Fin k → V) (j : Fin n) :
    slotData disk labels (.inl j) = ⟨disk j, .red⟩ := rfl

omit [DecidableEq V] [Fintype V] in
/-- The data of the black strand of brane `i`. -/
@[simp]
lemma slotData_inr (disk : @MarkedDisk V n) (labels : Fin k → V) (i : Fin k) :
    slotData disk labels (.inr i) = ⟨labels i, .black⟩ := rfl

/-- The section of the disk a slot sits in at vertex `v`. -/
def slotSection (diag : UBraneDiagram disk labels) (v : CubeVertex k) : Slot n k → ℕ
  | .inl j => j.val + 1
  | .inr i => (braneSection (diag.branes i) (v i)).val

/-- The order of slots within a section: rank `0` for the red strand, ranks `1, …, k` for
branes at their right end (inner branes first) and ranks `k + 1, …, 2k` for branes at their
left end (outer branes first), where "inner" is measured by `diag.nest`. Not every rank is
used. -/
def slotRank (diag : UBraneDiagram disk labels) (v : CubeVertex k) : Slot n k → ℕ
  | .inl _ => 0
  | .inr i => if v i = 0 then 1 + (diag.nest i).val else 2 * k - (diag.nest i).val

omit [DecidableEq V] [Fintype V] in
/-- Every rank is below `2 * k + 1`. -/
lemma slotRank_lt (diag : UBraneDiagram disk labels) (v : CubeVertex k) (x : Slot n k) :
    slotRank diag v x < 2 * k + 1 := by
  cases x with
  | inl j => simp [slotRank]
  | inr i => simp only [slotRank]; split_ifs <;> omega

/-- A sort key for the slots at vertex `v`: laying the strands out from left to right lists the
slots in increasing order of key. -/
def slotKey (diag : UBraneDiagram disk labels) (v : CubeVertex k) (x : Slot n k) : ℕ :=
  slotSection diag v x * (2 * k + 1) + slotRank diag v x

/-- If `s₁ * m + r₁ = s₂ * m + r₂` with both remainders below `m`, then `s₁ = s₂` and `r₁ = r₂`
(like digits in base `m`). -/
lemma eq_of_mul_add_eq {s₁ s₂ r₁ r₂ m : ℕ} (h₁ : r₁ < m) (h₂ : r₂ < m)
    (h : s₁ * m + r₁ = s₂ * m + r₂) : s₁ = s₂ ∧ r₁ = r₂ := by
  rcases Nat.lt_trichotomy s₁ s₂ with hs | hs | hs
  · have := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hs)
    rw [Nat.succ_mul] at this; omega
  · subst hs; omega
  · have := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hs)
    rw [Nat.succ_mul] at this; omega

omit [DecidableEq V] [Fintype V] in
/-- No two slots have the same key. -/
lemma slotKey_injective (diag : UBraneDiagram disk labels) (v : CubeVertex k) :
    Function.Injective (slotKey diag v) := by
  intro x y h
  obtain ⟨hs, hr⟩ := eq_of_mul_add_eq (slotRank_lt diag v x) (slotRank_lt diag v y) h
  cases x with
  | inl j =>
    cases y with
    | inl j' => simp only [slotSection] at hs; exact congrArg Sum.inl (Fin.ext (by omega))
    | inr i' => simp only [slotRank] at hr; split_ifs at hr <;> omega
  | inr i =>
    cases y with
    | inl j' => simp only [slotRank] at hr; split_ifs at hr <;> omega
    | inr i' =>
      by_contra hne
      have hne' : i ≠ i' := fun h => hne (by rw [h])
      simp only [slotSection, braneSection] at hs
      simp only [slotRank] at hr
      split_ifs at hs hr <;> try omega
      · exact diag.nest_injective i i' hne' (Or.inr (Fin.ext hs)) (Fin.ext (by omega))
      · exact diag.nest_injective i i' hne' (Or.inl (Fin.ext hs)) (Fin.ext (by omega))

/-- The position of a slot at vertex `v`: the number of slots with a smaller key. -/
def slotPos (diag : UBraneDiagram disk labels) (v : CubeVertex k) (x : Slot n k) : ℕ :=
  (Finset.univ.filter (fun y => slotKey diag v y < slotKey diag v x)).card

omit [DecidableEq V] [Fintype V] in
/-- A slot with a smaller key has a smaller position. -/
lemma slotPos_lt_slotPos {diag : UBraneDiagram disk labels} {v : CubeVertex k} {x y : Slot n k}
    (h : slotKey diag v x < slotKey diag v y) : slotPos diag v x < slotPos diag v y := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨x, by simp [h], by simp⟩
  · intro z hz; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢; omega

omit [DecidableEq V] [Fintype V] in
/-- No two slots have the same position. -/
lemma slotPos_injective (diag : UBraneDiagram disk labels) (v : CubeVertex k) :
    Function.Injective (slotPos diag v) := by
  intro x y h
  by_contra hne
  have hk : slotKey diag v x ≠ slotKey diag v y := fun h' => hne (slotKey_injective diag v h')
  rcases Nat.lt_or_gt_of_ne hk with hlt | hlt
  · exact absurd h (slotPos_lt_slotPos hlt).ne
  · exact absurd h (slotPos_lt_slotPos hlt).ne'

omit [DecidableEq V] [Fintype V] in
/-- Every position is below `n + k`. -/
lemma slotPos_lt (diag : UBraneDiagram disk labels) (v : CubeVertex k) (x : Slot n k) :
    slotPos diag v x < n + k := by
  have : slotPos diag v x < (Finset.univ : Finset (Slot n k)).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
    exact ⟨x, Finset.mem_univ _, by simp⟩
  simpa using this

/-- The position of a slot, as an element of `Fin`. -/
def slotPosFin (Γ : SimpleDigraph V) (diag : UBraneDiagram disk labels) (v : CubeVertex k)
    (x : Slot n k) : Fin (KLRWStructure.ofDisk Γ disk labels).numStrands :=
  ⟨slotPos diag v x, by rw [KLRWStructure.numStrands_ofDisk]; exact slotPos_lt diag v x⟩

/-- Every position holds exactly one slot. -/
lemma slotPosFin_bijective (Γ : SimpleDigraph V) (diag : UBraneDiagram disk labels)
    (v : CubeVertex k) : Function.Bijective (slotPosFin Γ diag v) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun x y h => slotPos_injective diag v (congrArg Fin.val h), ?_⟩
  simp [KLRWStructure.numStrands_ofDisk]

/-- The layout at vertex `v`: the bijection between positions and slots. -/
def layout (Γ : SimpleDigraph V) (diag : UBraneDiagram disk labels) (v : CubeVertex k) :
    Fin (KLRWStructure.ofDisk Γ disk labels).numStrands ≃ Slot n k where
  toFun := Fintype.bijInv (slotPosFin_bijective Γ diag v)
  invFun := slotPosFin Γ diag v
  left_inv := Fintype.rightInverse_bijInv _
  right_inv := Fintype.leftInverse_bijInv _

/-- The slot at the position of `x` is `x`. -/
lemma layout_slotPosFin (Γ : SimpleDigraph V) (diag : UBraneDiagram disk labels)
    (v : CubeVertex k) (x : Slot n k) : layout Γ diag v (slotPosFin Γ diag v x) = x :=
  (layout Γ diag v).right_inv x

/-- The strand sequence at vertex `v`: position `p` carries the data of the slot laid out
there. -/
def vertexStrandSeq (Γ : SimpleDigraph V) (diag : UBraneDiagram disk labels)
    (v : CubeVertex k) : Fin (KLRWStructure.ofDisk Γ disk labels).numStrands → StrandData V :=
  fun p => slotData disk labels (layout Γ diag v p)

/-- Counting strands with a given label and color at vertex `v` is counting slots with that
label and color. -/
lemma numColor_vertexStrandSeq (Γ : SimpleDigraph V) (diag : UBraneDiagram disk labels)
    (v : CubeVertex k) (a : V) (c : StrandColor) :
    numColor (vertexStrandSeq Γ diag v) a c =
      (Finset.univ.filter (fun x : Slot n k => slotData disk labels x = ⟨a, c⟩)).card := by
  unfold numColor vertexStrandSeq
  exact Finset.card_equiv (layout Γ diag v) (by simp)

omit [Fintype V] in
/-- The slots carrying a black strand labelled `a` are exactly the indices `i` with
`labels i = a`. -/
lemma card_slot_black (labels : Fin k → V) (a : V) :
    (Finset.univ.filter (fun x : Slot n k => slotData disk labels x = ⟨a, .black⟩)).card =
      (Finset.univ.filter (fun i : Fin k => labels i = a)).card := by
  symm
  rw [← Finset.card_map ⟨Sum.inr, Sum.inr_injective⟩]
  congr 1
  ext x
  cases x <;> simp

omit [Fintype V] in
/-- The slots carrying a red strand labelled `a` are exactly the marked points labelled `a`. -/
lemma card_slot_red (labels : Fin k → V) (a : V) :
    (Finset.univ.filter (fun x : Slot n k => slotData disk labels x = ⟨a, .red⟩)).card =
      (Finset.univ.filter (fun j : Fin n => disk j = a)).card := by
  symm
  rw [← Finset.card_map ⟨Sum.inl, Sum.inl_injective⟩]
  congr 1
  ext x
  cases x <;> simp

/-- The KLRW object at vertex `v` of the cube of `diag`. -/
def vertexObject (Γ : SimpleDigraph V) (diag : UBraneDiagram disk labels) (v : CubeVertex k) :
    KLRWObject (KLRWStructure.ofDisk Γ disk labels) where
  strandSeq := vertexStrandSeq Γ diag v
  corr_num_black a := by rw [numBlack, numColor_vertexStrandSeq, card_slot_black]; rfl
  corr_num_red a := by rw [numRed, numColor_vertexStrandSeq, card_slot_red]; rfl

/-- The strand at position `p` of `vertexObject` is the data of the slot laid out there. -/
lemma vertexObject_get (Γ : SimpleDigraph V) (diag : UBraneDiagram disk labels)
    (v : CubeVertex k) (p : Fin (KLRWStructure.ofDisk Γ disk labels).numStrands) :
    (vertexObject Γ diag v).get p = slotData disk labels (layout Γ diag v p) := rfl

end Layout

/-- The KLRW object at vertex `vertex`, as an object of the KLRW category. -/
def vertexObjectWithRing {k : ℕ} {labels : Fin k → V} {S : Type*} [CommRing S] (u ℏ : S)
    (Γ : SimpleDigraph V) (diag : UBraneDiagram disk labels) (vertex : CubeVertex k) :
    KLRWObject.WithRing u ℏ (KLRWStructure.ofDisk Γ disk labels) where
  obj := vertexObject Γ diag vertex

end VertexObjects

/-! ### The morphism along each edge of the cube -/

section EdgeMorphisms

section Crossings

variable {W : Type*} [DecidableEq W] [Fintype W]

/-- The crossings `[cross b, cross (b + 1), …, cross (b + d - 1)]`, which move the strand at
position `b + d` to position `b`. -/
def crossesDown (P : KLRWStructure W) : (b d : ℕ) → b + d < P.numStrands →
    List (StrandGenOp P)
  | _, 0, _ => []
  | b, d + 1, h => .cross ⟨b, by omega⟩ :: crossesDown P (b + 1) d (by omega)

/-- The crossings `[cross (a + d - 1), …, cross (a + 1), cross a]`, which move the strand at
position `a` to position `a + d`. -/
def crossesUp (P : KLRWStructure W) (a : ℕ) : (d : ℕ) → a + d < P.numStrands →
    List (StrandGenOp P)
  | 0, _ => []
  | d + 1, h => .cross ⟨a + d, by omega⟩ :: crossesUp P a d (by omega)

/-- The crossings that move the strand at position `start` to position `ending`. -/
def crossesBetween (P : KLRWStructure W) (start ending : Fin P.numStrands) :
    List (StrandGenOp P) :=
  if h : ending.val ≤ start.val then
    crossesDown P ending.val (start.val - ending.val) (by omega)
  else
    crossesUp P start.val (ending.val - start.val) (by omega)

/-- Where the strand at position `q` ends up when the strand at position `a` moves to position
`b` and the strands in between shift over by one to make room. -/
def movePos (a b q : ℕ) : ℕ :=
  if q = a then b
  else if b ≤ q ∧ q < a then q + 1
  else if a < q ∧ q ≤ b then q - 1
  else q

/-- The strand at position `r` after a crossing is the strand at position `adjSwap i r`
before it. -/
lemma KLRWObject.get_afterCross {P : KLRWStructure W} (M : KLRWObject P)
    (i : Fin (P.numStrands - 1))
    (r : Fin P.numStrands) : (M.afterCross i).get r = M.get (adjSwap i r) := rfl

/-- After `crossesDown`, the strand that was at position `q` is at `movePos (b + d) b q`. -/
lemma strandGenSeqEnd_crossesDown_get {P : KLRWStructure W} (M : KLRWObject P) :
    ∀ (b d : ℕ) (h : b + d < P.numStrands) (q r : Fin P.numStrands),
      r.val = movePos (b + d) b q.val →
      (strandGenSeqEnd M (crossesDown P b d h)).get r = M.get q := by
  intro b d
  induction d generalizing b with
  | zero =>
    intro h q r hr
    simp only [movePos, Nat.add_zero] at hr
    have : r = q := by apply Fin.ext; split_ifs at hr <;> omega
    subst this
    rfl
  | succ d ih =>
    intro h q r hr
    simp only [crossesDown, cross_strandGenSeqEnd, KLRWObject.get_afterCross]
    apply ih
    rw [adjSwap_val]
    simp only [movePos] at hr ⊢
    split_ifs at hr ⊢ <;> omega

/-- After `crossesUp`, the strand that was at position `q` is at `movePos a (a + d) q`. -/
lemma strandGenSeqEnd_crossesUp_get {P : KLRWStructure W} (M : KLRWObject P) (a : ℕ) :
    ∀ (d : ℕ) (h : a + d < P.numStrands) (q r : Fin P.numStrands),
      r.val = movePos a (a + d) q.val →
      (strandGenSeqEnd M (crossesUp P a d h)).get r = M.get q := by
  intro d
  induction d with
  | zero =>
    intro h q r hr
    simp only [movePos, Nat.add_zero] at hr
    have : r = q := by apply Fin.ext; split_ifs at hr <;> omega
    subst this
    rfl
  | succ d ih =>
    intro h q r hr
    simp only [crossesUp, cross_strandGenSeqEnd, KLRWObject.get_afterCross]
    apply ih
    rw [adjSwap_val]
    simp only [movePos] at hr ⊢
    split_ifs at hr ⊢ <;> omega

/-- After `crossesBetween start ending`, the strand that was at position `q` is at
`movePos start ending q`. -/
lemma strandGenSeqEnd_crossesBetween_get {P : KLRWStructure W} (M : KLRWObject P)
    (start ending q r : Fin P.numStrands) (hr : r.val = movePos start ending q) :
    (strandGenSeqEnd M (crossesBetween P start ending)).get r = M.get q := by
  unfold crossesBetween
  split_ifs with h
  · apply strandGenSeqEnd_crossesDown_get
    rwa [Nat.add_sub_cancel' h]
  · apply strandGenSeqEnd_crossesUp_get
    rwa [Nat.add_sub_cancel' (by omega)]

end Crossings

/-! #### Counting elements of a `Finset` below a threshold -/

section CardFilter

variable {α : Type*}

/-- The elements with key below `t` are the non `z` elements with key below `t`, plus `z` if its
key is below `t`. -/
lemma card_filter_key_lt [Fintype α] [DecidableEq α] (key : α → ℕ) (z : α) (t : ℕ) :
    (Finset.univ.filter (fun y => key y < t)).card =
      ((Finset.univ.erase z).filter (fun y => key y < t)).card +
        if key z < t then 1 else 0 := by
  rw [Finset.filter_erase]
  split_ifs with hz
  · have hmem : z ∈ Finset.univ.filter (fun y => key y < t) := by simp [hz]
    rw [Finset.card_erase_of_mem hmem]
    have := Finset.card_pos.2 ⟨z, hmem⟩
    omega
  · rw [Finset.erase_eq_of_notMem (by simp [hz])]
    simp

/-- Raising the threshold `t` does not decrease the number of keys below it. -/
lemma card_filter_key_mono (key : α → ℕ) (s : Finset α) {t t' : ℕ} (h : t ≤ t') :
    (s.filter (fun y => key y < t)).card ≤ (s.filter (fun y => key y < t')).card :=
  Finset.card_le_card (Finset.monotone_filter_right _ (fun _ hy => by omega))

/-- If some key lies in `[t, t')`, then strictly more keys are below `t'` than below `t`. -/
lemma card_filter_key_strict (key : α → ℕ) (s : Finset α) {t t' : ℕ} {x : α} (hx : x ∈ s)
    (h₁ : t ≤ key x) (h₂ : key x < t') :
    (s.filter (fun y => key y < t)).card < (s.filter (fun y => key y < t')).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset
    (Finset.monotone_filter_right _ (fun _ hy => by omega))]
  exact ⟨x, by simp [hx, h₂], by simp; omega⟩

/-- Positions after moving one element. Order the elements of `α` by two injective keys `K`
and `K'` that agree on every element except `z`. Then the position of `x` under `K'` is its
position under `K`, adjusted as `movePos` says for `z` moving from its old position to its new
one. -/
lemma card_filter_key_lt_eq_movePos [Fintype α] [DecidableEq α] {K K' : α → ℕ}
    (hK : Function.Injective K)
    (hK' : Function.Injective K') {z : α} (hKK' : ∀ y, y ≠ z → K' y = K y) (x : α) :
    (Finset.univ.filter (fun y => K' y < K' x)).card =
      movePos (Finset.univ.filter (fun y => K y < K z)).card
        (Finset.univ.filter (fun y => K' y < K' z)).card
        (Finset.univ.filter (fun y => K y < K x)).card := by
  by_cases hx : x = z
  · subst hx; simp [movePos]
  have hzx : z ≠ x := fun h => hx h.symm
  have hv : ∀ t, (Finset.univ.filter (fun y => K y < t)).card =
      ((Finset.univ.erase z).filter (fun y => K y < t)).card + if K z < t then 1 else 0 :=
    fun t => card_filter_key_lt _ _ t
  have hw : ∀ t, (Finset.univ.filter (fun y => K' y < t)).card =
      ((Finset.univ.erase z).filter (fun y => K y < t)).card + if K' z < t then 1 else 0 := by
    intro t
    rw [card_filter_key_lt _ z t]
    congr 2
    apply Finset.filter_congr
    intro y hy
    rw [hKK' y (Finset.ne_of_mem_erase hy)]
  have hxkey : K' x = K x := hKK' x hx
  have hA : K z ≠ K x := fun h => hzx (hK h)
  have hB : K' z ≠ K x := by rw [← hxkey]; exact fun h => hzx (hK' h)
  have hxs : x ∈ Finset.univ.erase z := by simp [hx]
  simp only [hv, hw, hxkey, lt_irrefl, ite_false, Nat.add_zero]
  rcases Nat.lt_or_gt_of_ne hA with hA' | hA' <;> rcases Nat.lt_or_gt_of_ne hB with hB' | hB'
  · have h1 := card_filter_key_mono K (Finset.univ.erase z) hA'.le
    have h2 := card_filter_key_mono K (Finset.univ.erase z) hB'.le
    simp only [movePos, hA', hB', ite_true]; split_ifs <;> omega
  · have h1 := card_filter_key_mono K (Finset.univ.erase z) hA'.le
    have h2 := card_filter_key_strict K _ hxs le_rfl hB'
    simp only [movePos, hA', ite_true, Nat.not_lt.2 hB'.le, ite_false]; split_ifs <;> omega
  · have h1 := card_filter_key_strict K _ hxs le_rfl hA'
    have h2 := card_filter_key_mono K (Finset.univ.erase z) hB'.le
    simp only [movePos, hB', ite_true, Nat.not_lt.2 hA'.le, ite_false]; split_ifs <;> omega
  · have h1 := card_filter_key_strict K _ hxs le_rfl hA'
    have h2 := card_filter_key_strict K _ hxs le_rfl hB'
    simp only [movePos, Nat.not_lt.2 hA'.le, Nat.not_lt.2 hB'.le, ite_false]; split_ifs <;> omega

end CardFilter

section Edge

variable {k : ℕ} {labels : Fin k → V}

omit [DecidableEq V] [Fintype V] in
/-- If `v` and `w` differ only in direction `i`, every slot other than brane `i` has the same
key at `v` and at `w`. -/
lemma slotKey_eq_of_ne (diag : UBraneDiagram disk labels) {v w : CubeVertex k} {i : Fin k}
    (hvw : ∀ j, j ≠ i → w j = v j) (y : Slot n k) (hy : y ≠ .inr i) :
    slotKey diag w y = slotKey diag v y := by
  cases y with
  | inl j => rfl
  | inr j =>
    have hj : j ≠ i := fun h => hy (by rw [h])
    simp [slotKey, slotSection, slotRank, hvw j hj]

/-- The crossings for the edge `v → w` in direction `i`: they move the strand of brane `i` from
its position at `v` to its position at `w`. -/
def edgeOps (Γ : SimpleDigraph V) (diag : UBraneDiagram disk labels) (v w : CubeVertex k)
    (i : Fin k) : List (StrandGenOp (KLRWStructure.ofDisk Γ disk labels)) :=
  crossesBetween _ (slotPosFin Γ diag v (.inr i)) (slotPosFin Γ diag w (.inr i))

/-- If the keys of `diag` at `v` and of `diag'` at `v'` agree on every slot except `z`, then the
crossings moving `z` from its position in the first layout to its position in the second turn
the first object into the second. Edges of the cube and stages of a peeling are both of this
form. -/
lemma strandGenSeqEnd_crossesBetween_slotPosFin (Γ : SimpleDigraph V)
    (diag diag' : UBraneDiagram disk labels) (v v' : CubeVertex k) (z : Slot n k)
    (hkey : ∀ y, y ≠ z → slotKey diag' v' y = slotKey diag v y) :
    strandGenSeqEnd (vertexObject Γ diag v)
        (crossesBetween _ (slotPosFin Γ diag v z) (slotPosFin Γ diag' v' z)) =
      vertexObject Γ diag' v' := by
  apply KLRWObject.ext_get
  intro r
  set x := layout Γ diag' v' r
  have hr : r = slotPosFin Γ diag' v' x := ((layout Γ diag' v').left_inv r).symm
  rw [strandGenSeqEnd_crossesBetween_get _ _ _ (slotPosFin Γ diag v x) r ?_,
    vertexObject_get, vertexObject_get, layout_slotPosFin]
  rw [hr]
  exact card_filter_key_lt_eq_movePos (slotKey_injective diag v) (slotKey_injective diag' v') hkey x

/-- If `v` and `w` differ only in direction `i`, the crossings `edgeOps` turn the object at `v`
into the object at `w`. -/
lemma strandGenSeqEnd_edgeOps (Γ : SimpleDigraph V) (diag : UBraneDiagram disk labels)
    (v w : CubeVertex k) (i : Fin k) (hvw : ∀ j, j ≠ i → w j = v j) :
    strandGenSeqEnd (vertexObject Γ diag v) (edgeOps Γ diag v w i) = vertexObject Γ diag w :=
  strandGenSeqEnd_crossesBetween_slotPosFin Γ diag diag v w (.inr i) (slotKey_eq_of_ne diag hvw)

end Edge

/-- The crossings of an edge turn the object at its start into the object at its end. -/
lemma strandGenSeqEnd_edge {k : ℕ} {labels : Fin k → V} (Γ : SimpleDigraph V)
    (diag : UBraneDiagram disk labels) {v w : CubeVertex k} (h : IsEdge v w) :
    strandGenSeqEnd (vertexObject Γ diag v) (edgeOps Γ diag v w h.dir) =
      vertexObject Γ diag w :=
  strandGenSeqEnd_edgeOps Γ diag v w h.dir
    (fun j hj => by rw [h.dir_spec.eq, Function.update_of_ne hj])

/-- The morphism of the KLRW category along an edge `v → w` of the cube. -/
def edgeHom {S : Type} [CommRing S] (u ℏ : S) {k : ℕ} {labels : Fin k → V}
    (Γ : SimpleDigraph V) (diag : UBraneDiagram disk labels) (v w : CubeVertex k)
    (h : IsEdge v w) : vertexObjectWithRing u ℏ Γ diag v ⟶ vertexObjectWithRing u ℏ Γ diag w :=
  KLRWObject.WithRing.homOfOps (edgeOps Γ diag v w h.dir) (strandGenSeqEnd_edge Γ diag h)

end EdgeMorphisms

/-! ### The maps between consecutive stages of a peeling

Going from stage `j` to stage `j + 1` moves one brane, `peeledBrane k j`, from the starting arc
to the new arc. At each vertex `v`, the stage map moves that brane's strand from its position at
stage `j` to its position at stage `j + 1`, staying at the same end: a strand at the left end of
the starting arc goes to the left end of the new arc, and a strand at the right end to the right
end. All other strands keep their place relative to each other. -/

section PeelMaps

/-- The brane moved from stage `j` to stage `j + 1`: the outermost brane still on the starting
arc. -/
def peeledBrane (k j : ℕ) (hj : j < k) : Fin k := ⟨k - j - 1, by omega⟩

variable {S : Type} [CommRing S] (u ℏ : S) (Γ : SimpleDigraph V)
variable (disk : @MarkedDisk V n) {k : ℕ} (labels : Fin k → V) (p : PeelData n)

omit [DecidableEq V] [Fintype V] in
/-- Every strand other than the moved brane has the same key at stage `j` and at stage
`j + 1`. -/
lemma PeelData.slotKey_diagram_succ (j : ℕ) (hj : j < k) (v : CubeVertex k) (y : Slot n k)
    (hy : y ≠ .inr (peeledBrane k j hj)) :
    slotKey (p.diagram disk labels (j + 1)) v y = slotKey (p.diagram disk labels j) v y := by
  cases y with
  | inl j' => rfl
  | inr i =>
    have hi : i.val ≠ k - j - 1 := fun h => hy (congrArg Sum.inr (Fin.ext h))
    simp only [slotKey, slotSection, slotRank, PeelData.diagram, peelNest]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- The crossings of the stage map at vertex `v`: they move the strand of the newly peeled brane
from its position at stage `j` to its position at stage `j + 1`. -/
def peelOps (j : ℕ) (hj : j < k) (v : CubeVertex k) :
    List (StrandGenOp (KLRWStructure.ofDisk Γ disk labels)) :=
  crossesBetween _ (slotPosFin Γ (p.diagram disk labels j) v (.inr (peeledBrane k j hj)))
    (slotPosFin Γ (p.diagram disk labels (j + 1)) v (.inr (peeledBrane k j hj)))

/-- The crossings `peelOps` turn the object at vertex `v` of stage `j` into the object at
vertex `v` of stage `j + 1`. -/
lemma strandGenSeqEnd_peelOps (j : ℕ) (hj : j < k) (v : CubeVertex k) :
    strandGenSeqEnd (vertexObject Γ (p.diagram disk labels j) v) (peelOps Γ disk labels p j hj v) =
      vertexObject Γ (p.diagram disk labels (j + 1)) v :=
  strandGenSeqEnd_crossesBetween_slotPosFin Γ _ _ v v _ (p.slotKey_diagram_succ disk labels j hj v)

/-- The stage map at vertex `v`, as a morphism of the KLRW category. -/
def peelHom (j : ℕ) (hj : j < k) (v : CubeVertex k) :
    vertexObjectWithRing u ℏ Γ (p.diagram disk labels j) v ⟶
      vertexObjectWithRing u ℏ Γ (p.diagram disk labels (j + 1)) v :=
  KLRWObject.WithRing.homOfOps (peelOps Γ disk labels p j hj v)
    (strandGenSeqEnd_peelOps Γ disk labels p j hj v)

end PeelMaps
end KLRWFromUBranes
end UBranes
end KLRW
