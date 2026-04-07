module

public import Mathlib
public import AInfinity.Grading
public import AInfinity.Stasheff

@[expose] public section

open CategoryTheory Finset AInfinityTheory

noncomputable section

namespace AInfinityCategoryTheory

universe u v w
variable {β : Type v} [Grading β]

structure AInfinityCategoryStruct (R : Type u) [CommRing R] where
  Obj : Type w
  Hom : Obj → Obj → GradedRModule (β := β) (R := R)

namespace AInfinityCategoryStruct

variable {R : Type u} [CommRing R]

structure Chain (C : AInfinityCategoryStruct (β := β) R) where
  n : ℕ+
  obj : Fin (n + 1) → C.Obj
  deg : Fin n → β

namespace Chain

variable {C : AInfinityCategoryStruct (β := β) R}

def source (ch : C.Chain) : C.Obj := ch.obj 0

def target (ch : C.Chain) : C.Obj := ch.obj (Fin.last ch.n)

def operationTarget (ch : C.Chain) : ModuleCat R :=
  C.Hom ch.source ch.target (operationTargetDeg ch.deg)

def link (ch : C.Chain) (i : Fin ch.n) : ModuleCat R :=
  C.Hom (ch.obj (Fin.castSucc i)) (ch.obj ((Fin.castSucc i) + 1)) (ch.deg i)

end Chain

end AInfinityCategoryStruct

/-- Helper: the inner object string. -/
def stasheffObjIn
    {n : ℕ}
    {Obj : Type w}
    (obj : Fin (n + 1) → Obj)
    (r s : ℕ)
    (hr : r + s ≤ n) : Fin (s + 1) → Obj :=
  fun i => obj ⟨r + i.val, by omega⟩

/-- Helper: the outer object string obtained by collapsing the inner block. -/
def stasheffObjOut
    {n : ℕ}
    {Obj : Type w}
    (obj : Fin (n + 1) → Obj)
    (r s : ℕ)
    (hr : r + s ≤ n) : Fin ((n + 1 - s) + 1) → Obj :=
  fun i =>
    if h1 : i.val ≤ r then
      obj ⟨i.val, by omega⟩
    else
      obj ⟨i.val + s - 1, by omega⟩

structure AInfinityPreCategory (R : Type u) [CommRing R]
    extends AInfinityCategoryStruct (β := β) R where
  m : (ch : toAInfinityCategoryStruct.Chain) →
      MultilinearMap R
        (fun i : Fin ch.n => ch.link i)
        ch.operationTarget

namespace AInfinityPreCategory

variable {R : Type u} [CommRing R]

/-- Generic Stasheff term construction for an A∞-category-style operation. -/
def categoryStasheffTerm
    {R : Type u}
    [CommRing R]
    {C : AInfinityCategoryStruct (β := β) R}
    (m : (ch : C.Chain) →
      MultilinearMap R
        (fun i : Fin ch.n => ch.link i)
        ch.operationTarget)
    (ch : C.Chain)
    (x : ∀ i : Fin ch.n, ch.link i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ ch.n) :
    C.Hom ch.source ch.target (stasheffTargetDeg ch.deg) := by
  let degIn := stasheffDegIn ch.deg r s hr
  let objIn := stasheffObjIn ch.obj r s hr
  let innerch : C.Chain := ⟨⟨s, hs⟩, objIn, degIn⟩

  have test (i : Fin innerch.n) : r + i.val < ch.n := by
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt r) hr
  have test2 (i : Fin innerch.n) : innerch.link i = ch.link ⟨r + i.val, test i⟩ := by
    sorry

  let xIn : ∀ i : Fin innerch.n, innerch.link i := fun i => by
    rw [test2 i]
    exact x ⟨r + i.val, test i⟩

  let inner := m innerch xIn
  let outerN := ch.n + 1 - s
  let degOut := stasheffDegOut ch.deg r s hr
  let objOut := stasheffObjOut ch.obj r s hr
  let outerch : C.Chain := ⟨⟨outerN, by omega⟩, objOut, degOut⟩

  have xOut_link_lt (i : Fin outerN) (h1 : i.val < r) :
      outerch.link i = ch.link ⟨i.val, by omega⟩ := by
    sorry

  have xOut_link_eq (i : Fin outerN) (h2 : i.val = r) :
      outerch.link i = innerch.operationTarget := by
    sorry

  have xOut_link_gt (i : Fin outerN) (h1 : ¬ i.val < r) (h2 : ¬ i.val = r) :
      outerch.link i = ch.link ⟨i.val + s - 1, by omega⟩ := by
    sorry

  let xOut : ∀ i : Fin outerN, outerch.link i := fun i => by
    by_cases h1 : i.val < r
    · exact (xOut_link_lt i h1) ▸ x ⟨i.val, by omega⟩
    · by_cases h2 : i.val = r
      · exact (xOut_link_eq i h2) ▸ inner
      · exact (xOut_link_gt i h1 h2) ▸ x ⟨i.val + s - 1, by omega⟩

  let outer := m outerch xOut
  have hdeg : outerch.operationTarget = C.Hom ch.source ch.target (stasheffTargetDeg ch.deg) := by
    convert congr_arg _ (stasheffDegOut_sum ch.deg r s hr) using 1
    congr! 1
    simp +decide [AInfinityCategoryStruct.Chain.target]
    simp +decide [outerch, Fin.last, objOut, stasheffObjOut]
    grind
  exact hdeg ▸ outer

/-- The `(r,s)` summand in the arity-`n` Stasheff relation. -/
def stasheffTerm
  {β : Type v} [Grading β]
  {R : Type u} [CommRing R]
  (X : AInfinityPreCategory (β := β) R)
  (ch : X.Chain)
  (x : ∀ i : Fin ch.n, ch.link i)
  (r s : ℕ)
  (hs : 1 ≤ s)
  (hr : r + s ≤ ch.n) :
  X.Hom ch.source ch.target (stasheffTargetDeg ch.deg) :=
  categoryStasheffTerm
    (C := X.toAInfinityCategoryStruct)
    X.m ch x r s hs hr

end AInfinityPreCategory

end AInfinityCategoryTheory
