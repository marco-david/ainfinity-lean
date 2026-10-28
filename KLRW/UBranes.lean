module
public import Mathlib
public import KLRW.KLRWAlgebra
public import KLRW.KLRWCategory
@[expose] public section

namespace KLRW
section CubeVertices

abbrev CubeVertex (m : ℕ) : Type := Fin m → Fin 2

section

variable {k : Nat} (vertex : CubeVertex k)

/- updateVertex allows you to change the ith element of a vertex to b. -/
def updateVertex (i : Fin k) (b : Fin 2) : CubeVertex k :=
  Function.update vertex i b
/- movedIndices returns all the positions a vertex has 1. -/
def movedIndices : Finset (Fin k) :=
  Finset.univ.filter (fun i => vertex i = 1)

end


/- ------------------------------------
   Things you can do with CubeVertex k
   ------------------------------------ -/

section IsEdgeFunctions

section
variable {m : ℕ} (v w : CubeVertex m)

/- Add b in front of vertex. (For example, vcons 0 (0 1 0 1) = (0 0 1 0 1). )-/
abbrev vcons (b : Fin 2) (v : CubeVertex m) : CubeVertex (m + 1) :=
  Fin.cons (α := fun _ => Fin 2) b v

/- Check if there is an edge between vertices v and w at the ith slot. -/
structure IsEdgeAt (i : Fin m) : Prop where
  zero : v i = 0
  eq : w = Function.update v i 1

/- Shows IsEdgeAt is decidable, so Lean can check the result of zero and eq of IsEdgeAt. -/
instance (i : Fin m) : Decidable (IsEdgeAt v w i) :=
  decidable_of_iff (v i = 0 ∧ w = Function.update v i 1)
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun h => ⟨h.zero, h.eq⟩⟩

end


variable {m : ℕ} {v w : CubeVertex m}

/- Shows i is unique in IsEdgeAt (IsEdgeAt v w i and IsEdgeAt v w j both true implies i = j). -/
lemma IsEdgeAt.dir_unique {i j : Fin m} (hi : IsEdgeAt v w i)
    (hj : IsEdgeAt v w j) : i = j := by
  by_contra hne
  have h1 : w i = 1 := by simp [hi.eq]
  have h2 : w i = 0 := by simp [hj.eq, hne, hi.zero]
  exact absurd (h1.symm.trans h2) (by decide)

/- Adding a value to front of two vertices that have an edge between them results in two new
   vertices that also have an edge between them. -/
lemma IsEdgeAt.cons {i : Fin m} (b : Fin 2) (h : IsEdgeAt v w i) :
    IsEdgeAt (vcons b v) (vcons b w) i.succ := by
  obtain ⟨h0, rfl⟩ := h
  refine ⟨by simpa [vcons] using h0, ?_⟩
  funext j
  cases j using Fin.cases
  · simp [vcons, (Fin.succ_ne_zero i).symm]
  · simp [vcons, Function.update_apply]

/- Returns a proof that says there is an edge in direction 0 from (0, v) to (1, v). -/
lemma IsEdgeAt.dir0 (v : CubeVertex m) : IsEdgeAt (vcons 0 v) (vcons 1 v) 0 := by
  refine ⟨rfl, ?_⟩
  funext j
  cases j using Fin.cases
  · simp [vcons]
  · simp [vcons]

/- Checks if there is an edge between 2 vertices. -/
def IsEdge (v w : CubeVertex m) : Prop := ∃ i, IsEdgeAt v w i

/- Calculates which direction an edge between two vertices goes. -/
def IsEdge.dir (h : IsEdge v w) : Fin m :=
  Fintype.choose (fun i => IsEdgeAt v w i) (by
    obtain ⟨i, hi⟩ := h
    exact ⟨i, hi, fun j hj => IsEdgeAt.dir_unique hj hi⟩)

/- Proves IsEdge.dir does calculate the right direction. -/
lemma IsEdge.dir_spec (h : IsEdge v w) : IsEdgeAt v w h.dir :=
  Fintype.choose_spec _ _

/- Another check, shows the calculated h.dir is the same as i if you have IsEdgeAt i by
   uniqueness. -/
lemma IsEdge.dir_eq {i : Fin m} (h : IsEdge v w) (hi : IsEdgeAt v w i) :
    h.dir = i :=
  IsEdgeAt.dir_unique h.dir_spec hi

/- IsEdgeAt.cons without the i attached. -/
lemma IsEdge.cons (b : Fin 2) (h : IsEdge v w) :
    IsEdge (vcons b v) (vcons b w) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i.succ, hi.cons b⟩

/- IsEdgeAt.dir0 without the i attached. -/
lemma IsEdge.dir0 (v : CubeVertex m) : IsEdge (vcons 0 v) (vcons 1 v) :=
  ⟨0, IsEdgeAt.dir0 v⟩

end IsEdgeFunctions

end CubeVertices


section UBranes

variable {V : Type} [DecidableEq V] [Fintype V]
variable {n : Nat}

abbrev MarkedDisk := Fin n → V

/- Structure for a UBrane, includes the start and end as well as label. -/
structure UBrane (disk : @MarkedDisk V n) where
  label : V
  left : Fin (n+1)
  right : Fin (n+1)
  left_lt_right : left < right
  deriving DecidableEq

/- Describes an ordered diagram with multiple UBranes. -/
structure UBraneDiagram (disk : @MarkedDisk V n) (k : Nat) where
  branes : Fin k → UBrane disk
  non_intersecting : ∀ i j : Fin k,
    ¬ ((branes i).left < (branes j).left ∧ (branes j).left < (branes i).right ∧
       (branes i).right < (branes j).right)

section KLRWFromUBranes

variable {disk : @MarkedDisk V n}

/- UBraneKLRWStruct builds a KLRWStructure from a UBraneDiagram.  -/
def UBraneKLRWStruct {k : Nat} (Γ : SimpleDigraph V) (diag : UBraneDiagram disk k) : KLRWStructure V where
  Γ := Γ
  BlackStrands := fun v => (Finset.univ.filter (fun i : Fin k => (diag.branes i).label = v)).card
  RedStrands := fun v => (Finset.univ.filter (fun i : Fin n => disk i = v)).card

/- braneSection gets the section number for brane i given the state of the ith position of a vertex. -/
def braneSection (b : UBrane disk) (v : Fin 2) : Fin (n + 1) :=
  if v = 0 then b.right else b.left

/- braneStrandData returns the associated StrandData of any given uBrane. -/
def braneStrandData (b : UBrane disk) : StrandData V :=
  ⟨b.label, .black⟩


section VertexObjects
section Layout
 
variable {k : Nat}
 
/- Proof that the total number of strands of the KLRWStruct built from a Ubrane diagram is the 
   same as adding n and k (the number of red strands + the number of black strands.) -/
lemma totalStrands_UBraneKLRWStruct (Γ : SimpleDigraph V) (diag : UBraneDiagram disk k) :
    totalStrands (UBraneKLRWStruct Γ diag) = n + k := by
  simp only [totalStrands, UBraneKLRWStruct, Finset.sum_add_distrib]
  rw [← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)),
    ← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  simp [Nat.add_comm]
 
/-- Each slot represents a strand. .inl j is the j-th red strand, and .inr i is the black strand
    coming from brane i. -/
abbrev Slot (n k : ℕ) := Fin n ⊕ Fin k
 
/- slotData returns the strand data (label and color) carried by each slot. -/
def slotData (diag : UBraneDiagram disk k) : Slot n k → StrandData V
  | .inl j => ⟨disk j, .red⟩
  | .inr i => ⟨(diag.branes i).label, .black⟩
 
/- slotSection returns which section a slot sits in at vertex. -/
def slotSection (diag : UBraneDiagram disk k) (v : CubeVertex k) : Slot n k → ℕ
  | .inl j => j.val + 1
  | .inr i => (braneSection (diag.branes i) (v i)).val
 
/- slotRank returns rank 0 for the red strand, then associates the branes at their right end in
   increasing index (ranks 1 ... k) and branes at their left end in decreasing index
   (ranks k + 1 ... 2k). Not all ranks have an associated slot. -/
def slotRank (v : CubeVertex k) : Slot n k → ℕ
  | .inl _ => 0
  | .inr i => if v i = 0 then 1 + i.val else 2 * k - i.val
 
 /- slotRank is always smaller than 2k + 1. -/
lemma slotRank_lt (v : CubeVertex k) (x : Slot n k) : slotRank v x < 2 * k + 1 := by
  cases x with
  | inl j => simp [slotRank]
  | inr i => simp only [slotRank]; split_ifs <;> omega
 
/-- slotKey returns a key for each slot so that when the associated strands to the slots are laid out left to right in the right order, they have increasing keys. -/
def slotKey (diag : UBraneDiagram disk k) (v : CubeVertex k) (x : Slot n k) : ℕ :=
  slotSection diag v x * (2 * k + 1) + slotRank v x
 
/- If s₁·m + r₁ = s₂·m + r₂ with both remainders below m, then the quotients and remainders are equal (like digits in base m). -/
lemma eq_of_mul_add_eq {s₁ s₂ r₁ r₂ m : ℕ} (h₁ : r₁ < m) (h₂ : r₂ < m)
    (h : s₁ * m + r₁ = s₂ * m + r₂) : s₁ = s₂ ∧ r₁ = r₂ := by
  rcases Nat.lt_trichotomy s₁ s₂ with hs | hs | hs
  · have := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hs)
    rw [Nat.succ_mul] at this; omega
  · subst hs; omega
  · have := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hs)
    rw [Nat.succ_mul] at this; omega
 
/- This shows slotKey is an injective function. No two slots have the same key.-/
lemma slotKey_injective (diag : UBraneDiagram disk k) (v : CubeVertex k) :
    Function.Injective (slotKey diag v) := by
  intro x y h
  obtain ⟨hs, hr⟩ := eq_of_mul_add_eq (slotRank_lt v x) (slotRank_lt v y) h
  cases x with
  | inl j =>
    cases y with
    | inl j' => simp only [slotSection] at hs; exact congrArg Sum.inl (Fin.ext (by omega))
    | inr i' => simp only [slotRank] at hr; split_ifs at hr <;> omega
  | inr i =>
    cases y with
    | inl j' => simp only [slotRank] at hr; split_ifs at hr <;> omega
    | inr i' =>
      simp only [slotRank] at hr
      congr 1; apply Fin.ext
      split_ifs at hr <;> omega
 
/- This returns the position of a slot at vertex v. It's calculated by counting the number of
   slots with a smaller key. -/
def slotPos (diag : UBraneDiagram disk k) (v : CubeVertex k) (x : Slot n k) : ℕ :=
  (Finset.univ.filter (fun y => slotKey diag v y < slotKey diag v x)).card
 
/- Proof that if the key of one slot is smaller than the other, then the position of it is 
   smaller than the other.-/
lemma slotPos_lt_slotPos {diag : UBraneDiagram disk k} {v : CubeVertex k} {x y : Slot n k}
    (h : slotKey diag v x < slotKey diag v y) : slotPos diag v x < slotPos diag v y := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨x, by simp [h], by simp⟩
  · intro z hz; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢; omega
 
/- Proof that slotPos is also an injective function. -/
lemma slotPos_injective (diag : UBraneDiagram disk k) (v : CubeVertex k) :
    Function.Injective (slotPos diag v) := by
  intro x y h
  by_contra hne
  have hk : slotKey diag v x ≠ slotKey diag v y := fun h' => hne (slotKey_injective diag v h')
  rcases Nat.lt_or_gt_of_ne hk with hlt | hlt
  · exact absurd h (slotPos_lt_slotPos hlt).ne
  · exact absurd h (slotPos_lt_slotPos hlt).ne'

/- All slot positions are smaller than n + k. -/
lemma slotPos_lt (diag : UBraneDiagram disk k) (v : CubeVertex k) (x : Slot n k) :
    slotPos diag v x < n + k := by
  have : slotPos diag v x < (Finset.univ : Finset (Slot n k)).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
    exact ⟨x, Finset.mem_univ _, by simp⟩
  simpa using this
 
/- slotPosFin is the position of a slot as a Fin value. -/
def slotPosFin (Γ : SimpleDigraph V) (diag : UBraneDiagram disk k) (v : CubeVertex k)
    (x : Slot n k) : Fin (totalStrands (UBraneKLRWStruct Γ diag)) :=
  ⟨slotPos diag v x, by rw [totalStrands_UBraneKLRWStruct]; exact slotPos_lt diag v x⟩
 
/- Proof that slotPosFin is bijective. -/
lemma slotPosFin_bijective (Γ : SimpleDigraph V) (diag : UBraneDiagram disk k)
    (v : CubeVertex k) : Function.Bijective (slotPosFin Γ diag v) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun x y h => slotPos_injective diag v (congrArg Fin.val h), ?_⟩
  simp [totalStrands_UBraneKLRWStruct]
 
/- layout at vertex v is the bijection between positions and slots. -/
def layout (Γ : SimpleDigraph V) (diag : UBraneDiagram disk k) (v : CubeVertex k) :
    Fin (totalStrands (UBraneKLRWStruct Γ diag)) ≃ Slot n k where
  toFun := Fintype.bijInv (slotPosFin_bijective Γ diag v)
  invFun := slotPosFin Γ diag v
  left_inv := Fintype.rightInverse_bijInv _
  right_inv := Fintype.leftInverse_bijInv _
 
/- Proof going from slot to position back to slot is the same as taking the id of slot. -/
lemma layout_slotPosFin (Γ : SimpleDigraph V) (diag : UBraneDiagram disk k) (v : CubeVertex k)
    (x : Slot n k) : layout Γ diag v (slotPosFin Γ diag v x) = x :=
  (layout Γ diag v).right_inv x
 
lemma numColor_ofFn {m : ℕ} (g : Fin m → StrandData V) (a : V) (c : StrandColor) :
    numColor (Vector.ofFn g) a c = (Finset.univ.filter (fun p => g p = ⟨a, c⟩)).card := by
  unfold numColor
  rw [Vector.toList_ofFn, List.ofFn_eq_map, List.filter_map, List.length_map,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _), List.toFinset_filter,
    List.toFinset_finRange]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp, Bool.and_eq_true,
    beq_iff_eq]
  generalize g p = s
  cases s
  simp

/- vertexStrandSeq inserts slotData of the strand with ith position into the ith entry of a vector. -/
def vertexStrandSeq (Γ : SimpleDigraph V) (diag : UBraneDiagram disk k) (v : CubeVertex k) :
    Vector (StrandData V) (totalStrands (UBraneKLRWStruct Γ diag)) :=
  Vector.ofFn (fun p => slotData diag (layout Γ diag v p))

/- Proof that the number of strands with a given label and color matches the cardinality of slots with the associated label and color. -/
lemma numColor_vertexStrandSeq (Γ : SimpleDigraph V) (diag : UBraneDiagram disk k)
    (v : CubeVertex k) (a : V) (c : StrandColor) :
    numColor (vertexStrandSeq Γ diag v) a c =
      (Finset.univ.filter (fun x : Slot n k => slotData diag x = ⟨a, c⟩)).card := by
  rw [vertexStrandSeq, numColor_ofFn]
  exact Finset.card_equiv (layout Γ diag v) (by simp)
 
/- Proof that the slots carrying a black strand labeled a are exactly the branes labeled a,
   so the two counts are equal. -/
lemma card_slot_black (diag : UBraneDiagram disk k) (a : V) :
    (Finset.univ.filter (fun x : Slot n k => slotData diag x = ⟨a, .black⟩)).card =
      (Finset.univ.filter (fun i : Fin k => (diag.branes i).label = a)).card := by
  symm
  rw [← Finset.card_map ⟨Sum.inr, Sum.inr_injective⟩]
  congr 1
  ext x
  cases x <;> simp [slotData]

/- Proof that the slots carrying a red strand labeled a are exactly the red points labeled a,
   so the two counts are equal. -/
lemma card_slot_red (diag : UBraneDiagram disk k) (a : V) :
    (Finset.univ.filter (fun x : Slot n k => slotData diag x = ⟨a, .red⟩)).card =
      (Finset.univ.filter (fun j : Fin n => disk j = a)).card := by
  symm
  rw [← Finset.card_map ⟨Sum.inl, Sum.inl_injective⟩]
  congr 1
  ext x
  cases x <;> simp [slotData]

/- Building the actual vertexObject using proofs we wrote earlier. -/
def vertexObject (Γ : SimpleDigraph V) (diag : UBraneDiagram disk k) (v : CubeVertex k) :
    KLRWObject (UBraneKLRWStruct Γ diag) where
  strandSeq := vertexStrandSeq Γ diag v
  corr_num_black a := by rw [numBlack, numColor_vertexStrandSeq, card_slot_black]; rfl
  corr_num_red a := by rw [numRed, numColor_vertexStrandSeq, card_slot_red]; rfl

/- Proof that the strand at position p is the data of the slot at p.-/
lemma vertexObject_get (Γ : SimpleDigraph V) (diag : UBraneDiagram disk k) (v : CubeVertex k)
    (p : Fin (totalStrands (UBraneKLRWStruct Γ diag))) :
    (vertexObject Γ diag v).get p = slotData diag (layout Γ diag v p) := by
  simp [vertexObject, vertexStrandSeq, KLRWObject.get, Vector.get, Vector.ofFn]
 
end Layout

/- vertexObject.WithRing adds a ring to vertexObject, making it a KLRWObject.WithRing. -/
def vertexObject.WithRing {k : Nat} (R : Type) [CommRing R]
    (Γ : SimpleDigraph V) (diag : UBraneDiagram disk k) (vertex : CubeVertex k) :
    KLRWObject.WithRing R (UBraneKLRWStruct Γ diag) where
  obj := vertexObject Γ diag vertex
 
end VertexObjects



section EdgeMorphisms
section Crossings
 
variable {W : Type*} [DecidableEq W] [Fintype W]

/- crossesDown is the list [cross b, cross (b + 1), …, cross (b + d - 1)], which is the list of 
   StrandGenOp needed to move a strand originally at b + d to b by that sequence of crosses. -/
def crossesDown (P : KLRWStructure W) : (b d : ℕ) → b + d < totalStrands P →
    List (StrandGenOp P)
  | _, 0, _ => []
  | b, d + 1, h => .cross ⟨b, by omega⟩ :: crossesDown P (b + 1) d (by omega)
 
/- crossesUp is the list [cross (a + d - 1), …, cross (a + 1), cross a], which is the list of 
   StrandGenOp needed to move a strand originally at a to a + d by that sequence of crosses. -/
def crossesUp (P : KLRWStructure W) (a : ℕ) : (d : ℕ) → a + d < totalStrands P →
    List (StrandGenOp P)
  | 0, _ => []
  | d + 1, h => .cross ⟨a + d, by omega⟩ :: crossesUp P a d (by omega)
 
/- crossesBetween returns the list of crossings that move the strand at position start to position ending. -/
def crossesBetween (P : KLRWStructure W) (start ending : Fin (totalStrands P)) :
    List (StrandGenOp P) :=
  if h : ending.val ≤ start.val then
    crossesDown P ending.val (start.val - ending.val) (by omega)
  else
    crossesUp P start.val (ending.val - start.val) (by omega)
 
/- movePos returns where the strand at position q ends up when the strand at position a is moved 
   to position b and everything in between shifts over by one to make room. -/
def movePos (a b q : ℕ) : ℕ :=
  if q = a then b
  else if b ≤ q ∧ q < a then q + 1
  else if a < q ∧ q ≤ b then q - 1
  else q

/- Proof that adjSwap index outputs act as expected numerically (positions i and i + 1 are swapped, and every other position stays the same). -/
lemma adjSwap_val {m : ℕ} (i : Fin (m - 1)) (r : Fin m) :
    (adjSwap i r).val =
      if r.val = i.val then i.val + 1 else if r.val = i.val + 1 then i.val else r.val := by
  simp only [adjSwap, Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> simp_all

/- Proof that the strand at position r after a crossing is the same as getting the strand at 
   position adjSwap i r in M. -/
lemma afterCross_get {P : KLRWStructure W} (M : KLRWObject P) (i : Fin (totalStrands P - 1))
    (r : Fin (totalStrands P)) : (afterCross M i).get r = M.get (adjSwap i r) := by
  simp [KLRWObject.get, Vector.get, Vector.ofFn]
 
/- Proof that after crossesDown, the strand that was at position q is now at movePos (b + d) b q. -/
lemma strandGenSeqEnd_crossesDown_get {P : KLRWStructure W} (M : KLRWObject P) :
    ∀ (b d : ℕ) (h : b + d < totalStrands P) (q r : Fin (totalStrands P)),
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
    simp only [crossesDown, cross_strandGenSeqEnd, afterCross_get]
    apply ih
    rw [adjSwap_val]
    simp only [movePos] at hr ⊢
    split_ifs at hr ⊢ <;> omega
 
/- Proof that after crossesUp, the strand that was at position q is now at movePos a (a + d) q. -/
lemma strandGenSeqEnd_crossesUp_get {P : KLRWStructure W} (M : KLRWObject P) (a : ℕ) :
    ∀ (d : ℕ) (h : a + d < totalStrands P) (q r : Fin (totalStrands P)),
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
    simp only [crossesUp, cross_strandGenSeqEnd, afterCross_get]
    apply ih
    rw [adjSwap_val]
    simp only [movePos] at hr ⊢
    split_ifs at hr ⊢ <;> omega
 
/- Proof that after crossesBetween start ending, the strand that was at position q is now at
   movePos start ending q. -/
lemma strandGenSeqEnd_crossesBetween_get {P : KLRWStructure W} (M : KLRWObject P)
    (start ending q r : Fin (totalStrands P)) (hr : r.val = movePos start ending q) :
    (strandGenSeqEnd M (crossesBetween P start ending)).get r = M.get q := by
  unfold crossesBetween
  split_ifs with h
  · apply strandGenSeqEnd_crossesDown_get
    rwa [Nat.add_sub_cancel' h]
  · apply strandGenSeqEnd_crossesUp_get
    rwa [Nat.add_sub_cancel' (by omega)]
 
/- Proof that two KLRW objects are equal if they have the same strand at every position. -/
lemma KLRWObject.ext_get {P : KLRWStructure W} {X Y : KLRWObject P}
    (h : ∀ p, X.get p = Y.get p) : X = Y := by
  apply KLRWObject.ext
  apply Vector.ext
  intro i hi
  exact h ⟨i, hi⟩

end Crossings


section Edge

variable {k : Nat}

/- Proof that the number of slots with key below t equals the number of slots other than z with key
   below t, plus 1 if z's key is also below t -/
lemma card_filter_key_lt (key : Slot n k → ℕ) (z : Slot n k) (t : ℕ) :
    (Finset.univ.filter (fun y => key y < t)).card =
      ((Finset.univ.erase z).filter (fun y => key y < t)).card + if key z < t then 1 else 0 := by
  rw [Finset.filter_erase]
  split_ifs with hz
  · have hmem : z ∈ Finset.univ.filter (fun y => key y < t) := by simp [hz]
    rw [Finset.card_erase_of_mem hmem]
    have := Finset.card_pos.2 ⟨z, hmem⟩
    omega
  · rw [Finset.erase_eq_of_notMem (by simp [hz])]
    simp

/- Proof that increasing the threshold t won't decrease the number of keys smaller than that threshold. -/
lemma card_filter_key_mono (key : Slot n k → ℕ) (s : Finset (Slot n k)) {t t' : ℕ}
    (h : t ≤ t') : (s.filter (fun y => key y < t)).card ≤ (s.filter (fun y => key y < t')).card :=
  Finset.card_le_card (Finset.monotone_filter_right _ (fun _ hy => by omega))

/- Proof that if there is a key between t and t', then the number of keys smaller than t is strictly smaller than the number of keys smaller than t'. -/
lemma card_filter_key_strict (key : Slot n k → ℕ) (s : Finset (Slot n k)) {t t' : ℕ}
    {x : Slot n k} (hx : x ∈ s) (h₁ : t ≤ key x) (h₂ : key x < t') :
    (s.filter (fun y => key y < t)).card < (s.filter (fun y => key y < t')).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset
    (Finset.monotone_filter_right _ (fun _ hy => by omega))]
  exact ⟨x, by simp [hx, h₂], by simp; omega⟩
 
/- If vertices v and w only differ at brane i, then every slot other than brane i has
   the same key at v and w. -/
lemma slotKey_eq_of_ne (diag : UBraneDiagram disk k) {v w : CubeVertex k} {i : Fin k}
    (hvw : ∀ j, j ≠ i → w j = v j) (y : Slot n k) (hy : y ≠ .inr i) :
    slotKey diag w y = slotKey diag v y := by
  cases y with
  | inl j => rfl
  | inr j =>
    have hj : j ≠ i := fun h => hy (by rw [h])
    simp [slotKey, slotSection, slotRank, hvw j hj]
 
/- Proves that going from v to w moves brane i from its old position to its new position, and every 
   other strand moves exactly as movePos says. -/
lemma slotPos_edge (diag : UBraneDiagram disk k) {v w : CubeVertex k} {i : Fin k}
    (hvw : ∀ j, j ≠ i → w j = v j) (x : Slot n k) :
    slotPos diag w x =
      movePos (slotPos diag v (.inr i)) (slotPos diag w (.inr i)) (slotPos diag v x) := by
  by_cases hx : x = .inr i
  · subst hx; simp [movePos]
  have hzx : (Sum.inr i : Slot n k) ≠ x := fun h => hx h.symm
  have hv : ∀ t, (Finset.univ.filter (fun y => slotKey diag v y < t)).card =
      ((Finset.univ.erase (.inr i)).filter (fun y => slotKey diag v y < t)).card +
        if slotKey diag v (.inr i) < t then 1 else 0 :=
    fun t => card_filter_key_lt _ _ t
  have hw : ∀ t, (Finset.univ.filter (fun y => slotKey diag w y < t)).card =
      ((Finset.univ.erase (.inr i)).filter (fun y => slotKey diag v y < t)).card +
        if slotKey diag w (.inr i) < t then 1 else 0 := by
    intro t
    rw [card_filter_key_lt _ (.inr i) t]
    congr 2
    apply Finset.filter_congr
    intro y hy
    rw [slotKey_eq_of_ne diag hvw y (Finset.ne_of_mem_erase hy)]
  have hxkey : slotKey diag w x = slotKey diag v x := slotKey_eq_of_ne diag hvw x hx
  have hA : slotKey diag v (.inr i) ≠ slotKey diag v x :=
    fun h => hzx (slotKey_injective diag v h)
  have hB : slotKey diag w (.inr i) ≠ slotKey diag v x := by
    rw [← hxkey]; exact fun h => hzx (slotKey_injective diag w h)
  have hxs : x ∈ Finset.univ.erase (.inr i) := by simp [hx]
  simp only [slotPos, hv, hw, hxkey, lt_irrefl, if_false, Nat.add_zero]
  rcases Nat.lt_or_gt_of_ne hA with hA' | hA' <;> rcases Nat.lt_or_gt_of_ne hB with hB' | hB'
  · have h1 := card_filter_key_mono (slotKey diag v) (Finset.univ.erase (.inr i)) hA'.le
    have h2 := card_filter_key_mono (slotKey diag v) (Finset.univ.erase (.inr i)) hB'.le
    simp only [movePos, hA', hB', if_true]; split_ifs <;> omega
  · have h1 := card_filter_key_mono (slotKey diag v) (Finset.univ.erase (.inr i)) hA'.le
    have h2 := card_filter_key_strict (slotKey diag v) _ hxs le_rfl hB'
    simp only [movePos, hA', if_true, Nat.not_lt.2 hB'.le, if_false]; split_ifs <;> omega
  · have h1 := card_filter_key_strict (slotKey diag v) _ hxs le_rfl hA'
    have h2 := card_filter_key_mono (slotKey diag v) (Finset.univ.erase (.inr i)) hB'.le
    simp only [movePos, hB', if_true, Nat.not_lt.2 hA'.le, if_false]; split_ifs <;> omega
  · have h1 := card_filter_key_strict (slotKey diag v) _ hxs le_rfl hA'
    have h2 := card_filter_key_strict (slotKey diag v) _ hxs le_rfl hB'
    simp only [movePos, Nat.not_lt.2 hA'.le, Nat.not_lt.2 hB'.le, if_false]; split_ifs <;> omega
 
/- edgeOps is the list of crossings for the edge v → w in direction i. (It returns the StrandGenOp list that moves brane i's strand from where it is at v to where it is at w.) -/
def edgeOps (Γ : SimpleDigraph V) (diag : UBraneDiagram disk k) (v w : CubeVertex k)
    (i : Fin k) : List (StrandGenOp (UBraneKLRWStruct Γ diag)) :=
  crossesBetween _ (slotPosFin Γ diag v (.inr i)) (slotPosFin Γ diag w (.inr i))
 
/- Proof that the crossings really do turn the object at v into the object at w if they only differ in the ith direction. -/
lemma strandGenSeqEnd_edgeOps (Γ : SimpleDigraph V) (diag : UBraneDiagram disk k)
    (v w : CubeVertex k) (i : Fin k) (hvw : ∀ j, j ≠ i → w j = v j) :
    strandGenSeqEnd (vertexObject Γ diag v) (edgeOps Γ diag v w i) = vertexObject Γ diag w := by
  apply KLRWObject.ext_get
  intro r
  set x := layout Γ diag w r
  have hr : r = slotPosFin Γ diag w x := ((layout Γ diag w).left_inv r).symm
  rw [edgeOps, strandGenSeqEnd_crossesBetween_get _ _ _ (slotPosFin Γ diag v x) r ?_,
    vertexObject_get, vertexObject_get, layout_slotPosFin]
  rw [hr]
  exact slotPos_edge diag hvw x
 
end Edge


/- Proof that the edge's crossings turn the object at v into the object at w. -/
lemma strandGenSeqEnd_edge {k : Nat} (Γ : SimpleDigraph V)
    (diag : UBraneDiagram disk k) {v w : CubeVertex k} (h : IsEdge v w) :
    strandGenSeqEnd (vertexObject Γ diag v) (edgeOps Γ diag v w h.dir) =
      vertexObject Γ diag w :=
  strandGenSeqEnd_edgeOps Γ diag v w h.dir
    (fun j hj => by rw [h.dir_spec.eq, Function.update_of_ne hj])
 
/- edgeHom builds a morphism from one vertex to another (if there is an edge from v to w). -/
noncomputable def edgeHom {k : Nat} (R : Type) [CommRing R]
    (Γ : SimpleDigraph V) (diag : UBraneDiagram disk k) (v w : CubeVertex k) (h : IsEdge v w) :
    vertexObject.WithRing R Γ diag v ⟶ vertexObject.WithRing R Γ diag w :=
  (⟨(KLRWRel R (UBraneKLRWStruct Γ diag)).mk'
      (strandGenSeq (vertexObject Γ diag v) (edgeOps Γ diag v w h.dir)),
    strandGenSeq_mem_KLRWHom_of_eq (R := R) _ _ _ (strandGenSeqEnd_edge Γ diag h)⟩ :
    ↥(KLRWHom R (vertexObject Γ diag v) (vertexObject Γ diag w)))
 

end EdgeMorphisms
end KLRWFromUBranes
end UBranes
end KLRW
