/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import AInfinity.ComposableMultilinearMap
public import AInfinity.FunctorComposition.Signs

/-! # Marked composites of composable multilinear maps

Let Φ be a composable multilinear map over `g` and `ψ`, and let `F`, with `s = 1`, and `D`, with
`s = 2`, be composable multilinear maps over the same `f` and `φ`. This file defines the composite
Φ ∘ (F | D) (`ComposableMultilinearMap.compMarked`) over `g ∘ f` and `ψ ∘ φ`. It is given by the
sum defining Φ ∘ F (`ComposableMultilinearMap.comp`), with one of the k inputs F_{i_j}(…) of Φₖ
replaced by D_{i_j}(…), summed over j, with the Koszul sign of the inputs after the j-th block.

The composite Φ ∘ (F | D) is the derivative of `F ↦ Φ ∘ F` at `F` in the direction `D`, and is
linear in Φ and in `D`. On bar constructions, `D` determines a coderivation along the map determined
by `F`, and Φ ∘ (F | D) is Φ applied after it.

For an A∞-functor `F`, the left-hand side of its A∞-functor equation is F ∘ (𝟙 | m), for the
identity 𝟙 and the operations m of the source (see
`AInfinity.FunctorComposition.FunctorEquation`). The rules relating Φ ∘ F and Φ ∘ (F | D) are in
`AInfinity.FunctorComposition.Assoc`.

## Main definitions

* `AInfinityTheory.ComposableMultilinearMap.pick`: the choice between an unmarked map `F` and a
  marked map `D`.
* `AInfinityTheory.ComposableMultilinearMap.compMarked`: the composite Φ ∘ (F | D).

## Main results

* `AInfinityTheory.ComposableMultilinearMap.compMarked_map_v_apply`: the value of Φ ∘ (F | D), as
  a signed sum of terms.

## Implementation notes

A term of Φ ∘ (F | D) with marked block `m` is the term `compTerm` for the choice
`fun l ↦ pick F D (decide (l = m))`: the choice between `F` and `D` is made by a Boolean, so that
statements about it are proved by cases on the Boolean and no cast between the degrees of `F` and
`D` is needed.

The marked map `D` has `s = 2`, i.e. reduced degree one, as the operations of an A∞-category have.
This is the only case that the A∞-functor equations need, and the sign of `compMarked` is the
Koszul sign for a map of odd reduced degree. The degree `u` of Φ ∘ (F | D) is an argument, with a
proof of `s + 1 = u`, so that a composite G ∘ (F | D), of degree `1 + 1`, is again a marked map.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

open GradedLinearQuiver

variable {n : ℕ}

namespace ComposableMultilinearMap

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}
  [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj'] [GradedLinearQuiver β'' R Obj'']
  {f : Obj → Obj'} {φ : β →+ᵍ β'} {g : Obj' → Obj''} {ψ : β' →+ᵍ β''} {s t u : ℤ}

/-! ### Marked choices -/

/-- The choice between an unmarked composable multilinear map `F` with `s = 1` and a marked one
`D` with `s = 2`, together with its degree. -/
def pick (F : ComposableMultilinearMap R f φ 1) (D : ComposableMultilinearMap R f φ 2)
    (b : Bool) : Σ u : ℤ, ComposableMultilinearMap R f φ u :=
  bif b then ⟨2, D⟩ else ⟨1, F⟩

@[simp]
lemma pick_false (F : ComposableMultilinearMap R f φ 1) (D : ComposableMultilinearMap R f φ 2) :
    pick F D false = ⟨1, F⟩ :=
  rfl

@[simp]
lemma pick_true (F : ComposableMultilinearMap R f φ 1) (D : ComposableMultilinearMap R f φ 2) :
    pick F D true = ⟨2, D⟩ :=
  rfl

lemma pick_fst_sub_one (F : ComposableMultilinearMap R f φ 1)
    (D : ComposableMultilinearMap R f φ 2) (b : Bool) :
    (pick F D b).1 - 1 = bif b then 1 else 0 := by
  cases b <;> rfl

/-! ### The composite Φ ∘ (F | D) -/

section CompMarked

variable (Φ : ComposableMultilinearMap R g ψ s) (F : ComposableMultilinearMap R f φ 1)
  (D : ComposableMultilinearMap R f φ 2)

lemma sum_pick_fst_sub_one {k : ℕ} (m : Fin k) :
    ∑ l : Fin k, ((pick F D (decide (l = m))).1 - 1) = 1 := by
  simp [pick_fst_sub_one]

/-- A term of Φ ∘ (F | D) has the degree of a map of degree one more than Φ. -/
lemma compMarked_deg (deg : Fin n → β) (c : Composition n) (m : Fin c.length) (hu : s + 1 = u)
    {j : β} (hj : targetDeg u deg = j) :
    ψ (targetDeg s fun l ↦
      φ (targetDeg (pick F D (decide (l = m))).1 fun i ↦ deg (c.embedding l i))) = (ψ.comp φ) j :=
  degMap_targetDeg_degMap_targetDeg_embedding φ ψ deg c _
    (by rw [sum_pick_fst_sub_one, hu]) hj

/-- The composite Φ ∘ (F | D) of a composable multilinear map Φ with a composable multilinear
map `F` with `s = 1`, with one input replaced by `D` with `s = 2`. Its component of arity n is
the sum, over all compositions i₁ + ⋯ + iₖ = n and all blocks `m`, of Φₖ applied to the values of
`F` on the blocks other than `m` and to the value of `D` on the block `m`, with the Koszul sign
of the inputs after the block `m`. It is the derivative of `F ↦ Φ ∘ F` at `F` in the direction
`D`, and is linear in Φ and in `D`. Its degree `u` is one more than the degree `s` of Φ. -/
def compMarked (hu : s + 1 = u) : ComposableMultilinearMap R (fun X ↦ g (f X)) (ψ.comp φ) u where
  map X := .mk fun deg j hj ↦ ∑ c : Composition _, ∑ m : Fin c.length,
    tailSign deg (c.sizeUpTo (m + 1)) •
      Φ.compTermMultilinearMap X deg c (fun l ↦ pick F D (decide (l = m))) ((ψ.comp φ) j)
        (compMarked_deg F D deg c m hu hj)

variable {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))
  [NeZero n] {j : β}

/-- The value of the component of arity n of Φ ∘ (F | D): the signed sum, over all compositions
`c` of `n` and all blocks `m` of `c`, of Φ applied to the values of `F` on the blocks of `c`
other than `m` and the value of `D` on the block `m`. -/
lemma compMarked_map_v_apply (hu : s + 1 = u) (hj : targetDeg u deg = j) :
    ((Φ.compMarked F D hu).map X).v deg j hj a =
      ∑ c : Composition n, ∑ m : Fin c.length, tailSign deg (c.sizeUpTo (m + 1)) •
        Φ.compTerm a c (fun l ↦ pick F D (decide (l = m))) ((ψ.comp φ) j)
          (compMarked_deg F D deg c m hu hj) :=
  (sum_apply Finset.univ (fun c : Composition n ↦ ∑ m : Fin c.length,
    tailSign deg (c.sizeUpTo (m + 1)) • Φ.compTermMultilinearMap X deg c
      (fun l ↦ pick F D (decide (l = m))) ((ψ.comp φ) j) (compMarked_deg F D deg c m hu hj))
    a).trans (Finset.sum_congr rfl fun c _ ↦ sum_apply Finset.univ (fun m : Fin c.length ↦
      tailSign deg (c.sizeUpTo (m + 1)) • Φ.compTermMultilinearMap X deg c
        (fun l ↦ pick F D (decide (l = m))) ((ψ.comp φ) j) (compMarked_deg F D deg c m hu hj)) a)

end CompMarked

end ComposableMultilinearMap

end AInfinityTheory
