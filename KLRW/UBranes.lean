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
  non_intersecting : sorry  -- optional, but we might want to require a proof that the U branes, once superimposed onto the same 2D picture, do not self-intersect


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

variable {k : ℕ} (R : Type) [CommRing R] (Γ : SimpleDigraph V)
variable (diag : UBraneDiagram disk k) (vertex : CubeVertex k)


/- branesInSection returns an ordered list of the indices of branes in a given section of a specific vertex. -/
def branesInSection (sec : Fin (n + 1)) : List (Fin k) :=

  let rightBranes := (List.finRange k).filter fun i =>
    vertex i = 0 ∧ braneSection (diag.branes i) 0 = sec

  let leftBranes := ((List.finRange k).filter fun i =>
    vertex i = 1 ∧ braneSection (diag.branes i) 1 = sec).reverse

  rightBranes ++ leftBranes

/- sectionStrands gets all black strands in a given section, ordered right-ascending then left-descending. -/
def sectionStrands (sec : Fin (n + 1)) : List (StrandData V) :=
  (branesInSection diag vertex sec).map
    (fun i => ⟨(diag.branes i).label, .black⟩)

/- vertexStrands builds the full strand sequence for a given vertex. -/
def vertexStrands : List (StrandData V) :=
  List.flatMap (fun sec =>
    let blacks := sectionStrands diag vertex sec
    if h : sec.val > 0 then
      (⟨disk ⟨sec.val - 1, by omega⟩, .red⟩ : StrandData V) :: blacks
    else
      blacks)
  (List.finRange (n + 1))


/- vertexStrandSeq proves vertexStrands can be turned into a vector of the expected length. -/
def vertexStrandSeq :
    Vector (StrandData V) (totalStrands (UBraneKLRWStruct Γ diag)) :=
  ⟨(vertexStrands diag vertex).toArray,
   by sorry⟩


/- vertexObject turns vertexStrandSeq into a KLRWObject. -/
def vertexObject :
    KLRWObject (UBraneKLRWStruct Γ diag) where
  strandSeq := vertexStrandSeq Γ diag vertex
  corr_num_black := sorry
  corr_num_red := sorry

/- vertexObject.WithRing adds a ring to vertexObject, making it a KLRWObject.WithRing. -/
def vertexObject.WithRing :
    KLRWObject.WithRing R (UBraneKLRWStruct Γ diag) where
  obj := vertexObject Γ diag vertex


end VertexObjects


section EdgeMorphisms

variable {k : Nat} (R : Type) [CommRing R] (Γ : SimpleDigraph V)
variable (diag : UBraneDiagram disk k) (vertex : CubeVertex k)

/- sectionSize returns the number of black strands + 1 red strand if sec > 0 in any given section of a vertex. -/
def sectionSize (sec : Fin (n + 1)) : Nat :=
  (sectionStrands diag vertex sec).length + if sec.val > 0 then 1 else 0

/- strandsBeforeSection returns the total number of strands before any given section. -/
def strandsBeforeSection (sec : Fin (n + 1)) : Nat :=
  (Finset.Iio sec).sum (fun s => sectionSize diag vertex s)

/- strandPosition returns the index of the strand generated by the given U-brane at a vertex. -/
def strandPosition (i : Fin k) : Nat :=
  let sec := braneSection (diag.branes i) (vertex i)
  let before := strandsBeforeSection diag vertex sec
  let sameSection := branesInSection diag vertex sec
  before + List.idxOf i sameSection

/- crossesBetween returns a list of StrandGenOp that describes what crossings are needed to move
   a strand from position start to position end. -/
def crossesBetween (start ending : Fin (n + k)) :
    List (StrandGenOp (UBraneKLRWStruct Γ diag)) :=
  if h : start.val = ending.val then []
  else if h : ending.val < start.val then
    (List.range (start.val - ending.val)).map
      (fun j => .cross ⟨ending.val + j, by sorry⟩)
  else
    (List.range (ending.val - start.val)).map
      (fun j => .cross ⟨ending.val - 1 - j, by sorry⟩)


/- edgeHom builds a morphism from one vertex to another (if they only differ by 1 value). -/
noncomputable def edgeHom (v w : CubeVertex k) (h : IsEdge v w) :
    vertexObject.WithRing R Γ diag v ⟶ vertexObject.WithRing R Γ diag w := by
  let i := h.dir
  let M := vertexObject Γ diag v
  let N := vertexObject Γ diag w

  let start := (⟨strandPosition diag v i, by sorry⟩ : Fin (n + k))
  let ending := (⟨strandPosition diag w i, by sorry⟩ : Fin (n + k))
  let ops := crossesBetween Γ diag start ending
  have h_end : strandGenSeqEnd M ops = N := by sorry

  exact ⟨(KLRWRel R (UBraneKLRWStruct Γ diag)).mk' (strandGenSeq M ops),
    strandGenSeq_mem_KLRWHom_of_eq (R := R) M N ops h_end⟩

end EdgeMorphisms
end KLRWFromUBranes
end UBranes
end KLRW
