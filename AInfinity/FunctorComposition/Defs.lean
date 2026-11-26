/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import AInfinity.AInfinityFunctor
public import AInfinity.ComposableMultilinearMap
public import AInfinity.FunctorComposition.Signs

/-! # Composition of composable multilinear maps

Let Φ be a composable multilinear map over `g` and `ψ`, and let `F`, with `s = 1`, and `D`, with
`s = 2`, be composable multilinear maps over the same `f` and `φ`. This file defines two
composites over `g ∘ f` and `ψ ∘ φ`:

* Φ ∘ F (`ComposableMultilinearMap.comp`), with components
  $$(\Phi \circ F)_n(a_1, \dots, a_n) = \sum_{k \ge 1} \sum_{i_1 + \dots + i_k = n}
    \Phi_k(F_{i_1}(a_1, \dots, a_{i_1}), \dots, F_{i_k}(a_{n-i_k+1}, \dots, a_n));$$
* Φ ∘ (F | D) (`ComposableMultilinearMap.compMarked`), given by the same sum with one of the k
  inputs F_{i_j}(…) of Φₖ replaced by D_{i_j}(…), summed over j, with the Koszul sign of the
  inputs after the j-th block.

The composite Φ ∘ F is linear in Φ, and polynomial in `F`: its term Φₖ(F, …, F) is k-linear. The
composite Φ ∘ (F | D) is the derivative of `F ↦ Φ ∘ F` at `F` in the direction `D`, and is linear
in Φ and in `D`. On bar constructions, `D` determines a coderivation along the map determined by
`F`, and Φ ∘ (F | D) is Φ applied after it.

For the operations m' of an A∞-category, m' ∘ F is the right-hand side of the A∞-functor equation
of `F`. Its left-hand side is F ∘ (𝟙 | m), for the identity 𝟙 and the operations m of the source
(see `AInfinity.FunctorComposition.StasheffSum`). The rules relating the two composites are in
`AInfinity.FunctorComposition.Assoc`.

## Main definitions

* `MultilinearMap.compComposition`: the composite of a multilinear map in k variables with k
  multilinear maps, one on each block of a composition of `n`.
* `AInfinityTheory.ComposableMultilinearMap.blockMap`: the value of a composable multilinear map
  on a block of a composition.
* `AInfinityTheory.ComposableMultilinearMap.applyBlocks`: a composable multilinear map applied to
  a composable string of morphisms along a composition.
* `AInfinityTheory.ComposableMultilinearMap.pick`: the choice between an unmarked map `F` and a
  marked map `D`.
* `AInfinityTheory.ComposableMultilinearMap.compTerm`: the term Φₖ(P₁(…), …, Pₖ(…)) of a
  composite, for a composition into k blocks and a choice `P` of a map for each block.
* `AInfinityTheory.ComposableMultilinearMap.comp`: the composite Φ ∘ F.
* `AInfinityTheory.ComposableMultilinearMap.compMarked`: the composite Φ ∘ (F | D).

## Main results

* `AInfinityTheory.ComposableMultilinearMap.comp_map_v_apply`,
  `AInfinityTheory.ComposableMultilinearMap.compMarked_map_v_apply`: the values of the two
  composites, as sums of terms.

## Implementation notes

A term of either composite is described by a composition `c` of `n` and a choice
`P : Fin c.length → Σ u : ℤ, ComposableMultilinearMap R f φ u` of a composable multilinear map,
together with its degree, for each block of `c`. For Φ ∘ F the choice is constant. For
Φ ∘ (F | D) with marked block `m` it is `fun l ↦ pick F D (decide (l = m))`: the choice between
`F` and `D` is made by a Boolean, so that statements about it are proved by cases on the Boolean
and no cast between the degrees of `F` and `D` is needed.

Terms are defined in any degree `d` equal to their degree, with a proof of the equality as an
argument, as for `stasheffTerm`. Every definition that transports along equalities of objects or
degrees is stated so that the endpoints of `homCongr` are syntactically those of its type. Then
`simp` removes the transport from under `GradedLinearQuiver.Total.of`, and two descriptions of a
term are compared with `ComposableMultilinearMap.total_map_congr`.

The marked map `D` has `s = 2`, i.e. reduced degree one, as the operations of an A∞-category have.
This is the only case that the A∞-functor equations need, and the sign of `compMarked` is the
Koszul sign for a map of odd reduced degree. The degree `u` of Φ ∘ (F | D) is an argument, with a
proof of `s + 1 = u`, so that a composite G ∘ (F | D), of degree `1 + 1`, is again a marked map.
-/

@[expose] public section

noncomputable section

/-! ### Multilinear maps composed along a composition -/

namespace MultilinearMap

variable {R : Type*} [Semiring R] {n : ℕ} (c : Composition n)
variable {M : Fin n → Type*} {N : Fin c.length → Type*} {P : Type*}
variable [∀ i, AddCommMonoid (M i)] [∀ l, AddCommMonoid (N l)] [AddCommMonoid P]
variable [∀ i, Module R (M i)] [∀ l, Module R (N l)] [Module R P]

/-- The composite of a multilinear map `g` in k variables with k multilinear maps `f l`, one on
each block of a composition `c` of `n` into k blocks: the multilinear map in n variables
`x ↦ g (f 0 (x on block 0), …, f (k - 1) (x on block k - 1))`. -/
def compComposition (g : MultilinearMap R N P)
    (f : ∀ l, MultilinearMap R (fun j ↦ M (c.embedding l j)) (N l)) : MultilinearMap R M P :=
  (domDomCongrLinearEquiv' R ℕ M P c.blocksFinEquiv.symm).symm (g.compMultilinearMap f)

@[simp]
theorem compComposition_apply (g : MultilinearMap R N P)
    (f : ∀ l, MultilinearMap R (fun j ↦ M (c.embedding l j)) (N l)) (x : ∀ i, M i) :
    compComposition c g f x = g fun l ↦ f l fun j ↦ x (c.embedding l j) :=
  rfl

end MultilinearMap

namespace AInfinityTheory

open GradedLinearQuiver AInfinityCategoryStruct

variable {n : ℕ}

/-! ### Degrees -/

section Degrees

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] (φ : β →+ᵍ β') (ψ : β' →+ᵍ β'') (deg : Fin n → β)

/-- Applying maps of degrees (σ₁ - i₁) · 1, …, (σₖ - iₖ) · 1 to the blocks of a composition
c = (i₁, …, iₖ) of `n`, and then a map of degree (s - k) · 1 to their values, has the degree of
a map of degree (s + ∑ₗ (σₗ - 1) - n) · 1. -/
lemma targetDeg_targetDeg_embedding_of_sum (s : ℤ) (c : Composition n) (σ : Fin c.length → ℤ) :
    targetDeg s (fun l ↦ targetDeg (σ l) fun j ↦ deg (c.embedding l j)) =
      targetDeg (s + ∑ l, (σ l - 1)) deg := by
  simp only [targetDeg, Finset.sum_add_distrib, c.sum_sum_apply_embedding, add_assoc,
    ← Finset.sum_smul, ← add_smul, c.sum_sub_blocksFun_add s σ]

/-- `targetDeg_targetDeg_embedding_of_sum` translated along homomorphisms of gradings. -/
lemma degMap_targetDeg_degMap_targetDeg_embedding {s u : ℤ} (c : Composition n)
    (σ : Fin c.length → ℤ) (hσ : s + ∑ l, (σ l - 1) = u) {j : β} (hj : targetDeg u deg = j) :
    ψ (targetDeg s fun l ↦ φ (targetDeg (σ l) fun i ↦ deg (c.embedding l i))) = (ψ.comp φ) j :=
  congrArg ψ ((targetDeg_map φ s _).trans (congrArg φ
    ((targetDeg_targetDeg_embedding_of_sum deg s c σ).trans (hσ ▸ hj))))

end Degrees

namespace ComposableMultilinearMap

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}
  [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj'] [GradedLinearQuiver β'' R Obj'']
  {f : Obj → Obj'} {φ : β →+ᵍ β'} {g : Obj' → Obj''} {ψ : β' →+ᵍ β''} {s t u : ℤ}

/-! ### The value of a composable multilinear map on a block of a composition -/

section Block

variable (D : ComposableMultilinearMap R f φ t) (X : Fin (n + 1) → Obj) (deg : Fin n → β)
  (c : Composition n) (l : Fin c.length)

/-- The component of arity iₗ of `D` on the `l`-th block of a composition c = (i₁, …, iₖ) of `n`,
as a multilinear map into the hom space of the `l`-th input of an outer map of arity k.
Evaluated on composable inputs, it is `blockMap`. -/
def blockMultilinearMap :
    MultilinearMap R (fun j ↦ ComposableHom β R X (c.embedding l j) (deg (c.embedding l j)))
      (ComposableHom β' R (fun k ↦ f (X (c.boundary k))) l
        (φ (targetDeg t fun j ↦ deg (c.embedding l j)))) :=
  (homCongr R (congrArg f (compositionBlockObj_zero X c l))
    (congrArg f (compositionBlockObj_last X c l)) rfl).toLinearMap.compMultilinearMap
    ((D.map (compositionBlockObj X c l)).v (fun j ↦ deg (c.embedding l j)) _ rfl)

variable {X deg}

/-- The value of the component of arity iₗ of `D` on the `l`-th block of a composition
c = (i₁, …, iₖ) of `n`, as the `l`-th input of an outer map of arity k. -/
def blockMap (D : ComposableMultilinearMap R f φ t)
    (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (c : Composition n) (l : Fin c.length) :
    ComposableHom β' R (fun k ↦ f (X (c.boundary k))) l
      (φ (targetDeg t fun j ↦ deg (c.embedding l j))) :=
  homCongr R (congrArg f (compositionBlockObj_zero X c l))
    (congrArg f (compositionBlockObj_last X c l)) rfl
    ((D.map (compositionBlockObj X c l)).v (fun j ↦ deg (c.embedding l j)) _ rfl
      fun j ↦ a (c.embedding l j))

@[simp]
lemma blockMultilinearMap_apply (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) :
    D.blockMultilinearMap X deg c l (fun j ↦ a (c.embedding l j)) = D.blockMap a c l :=
  rfl

end Block

/-! ### A composable multilinear map applied along a composition -/

section ApplyBlocks

variable (Φ : ComposableMultilinearMap R g ψ s) (f) (X : Fin (n + 1) → Obj) [NeZero n]
  (c : Composition n)

/-- The component of arity k of Φ applied to a composable string `B` of k morphisms between the
objects `f (X (c.boundary k))`, for a composition `c` of `n` into k blocks: a morphism from
`g (f X₀)` to `g (f Xₙ)`, in any degree `d` equal to its degree. -/
def applyBlocks {ε : Fin c.length → β'}
    (B : ∀ l, ComposableHom β' R (fun k ↦ f (X (c.boundary k))) l (ε l)) (d : β'')
    (hd : ψ (targetDeg s ε) = d) : (g (f (X 0)) →ᵍ[R] g (f (X (Fin.last n)))) d :=
  homCongr R (congrArg (fun k ↦ g (f (X k))) c.boundary_zero)
    (congrArg (fun k ↦ g (f (X k))) c.boundary_last) hd
    ((Φ.map fun k ↦ f (X (c.boundary k))).v ε _ rfl B)

end ApplyBlocks

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

section CompTerm

variable (Φ : ComposableMultilinearMap R g ψ s) [NeZero n] (X : Fin (n + 1) → Obj)
  (deg : Fin n → β) (c : Composition n)
  (P : Fin c.length → Σ u : ℤ, ComposableMultilinearMap R f φ u) (d : β'')
  (hd : ψ (targetDeg s fun l ↦ φ (targetDeg (P l).1 fun j ↦ deg (c.embedding l j))) = d)

/-- The term indexed by a composition c = (i₁, …, iₖ) of `n` of a composite: the multilinear map
(a₁, …, aₙ) ↦ Φₖ(P₁(a₁, …, a_{i₁}), …, Pₖ(a_{n-iₖ+1}, …, aₙ)),
for a choice `P` of a composable multilinear map for each block of `c`. -/
def compTermMultilinearMap :
    MultilinearMap R (fun i ↦ ComposableHom β R X i (deg i))
      ((g (f (X 0)) →ᵍ[R] g (f (X (Fin.last n)))) d) :=
  (homCongr R (congrArg (fun k ↦ g (f (X k))) c.boundary_zero)
    (congrArg (fun k ↦ g (f (X k))) c.boundary_last) hd).toLinearMap.compMultilinearMap
    (MultilinearMap.compComposition c
      ((Φ.map fun k ↦ f (X (c.boundary k))).v
        (fun l ↦ φ (targetDeg (P l).1 fun j ↦ deg (c.embedding l j))) _ rfl)
      fun l ↦ (P l).2.blockMultilinearMap X deg c l)

variable {X deg}

/-- The value Φₖ(P₁(a₁, …, a_{i₁}), …, Pₖ(a_{n-iₖ+1}, …, aₙ)) of the term indexed by a
composition c = (i₁, …, iₖ) of `n` of a composite, for a choice `P` of a composable multilinear
map for each block of `c`. -/
def compTerm (Φ : ComposableMultilinearMap R g ψ s)
    (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (c : Composition n)
    (P : Fin c.length → Σ u : ℤ, ComposableMultilinearMap R f φ u) (d : β'')
    (hd : ψ (targetDeg s fun l ↦ φ (targetDeg (P l).1 fun j ↦ deg (c.embedding l j))) = d) :
    (g (f (X 0)) →ᵍ[R] g (f (X (Fin.last n)))) d :=
  Φ.applyBlocks f X c (fun l ↦ (P l).2.blockMap a c l) d hd

@[simp]
lemma compTermMultilinearMap_apply (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) :
    Φ.compTermMultilinearMap X deg c P d hd a = Φ.compTerm a c P d hd :=
  rfl

end CompTerm

/-! ### The composites Φ ∘ F and Φ ∘ (F | D) -/

section Comp

variable (Φ : ComposableMultilinearMap R g ψ s) (F : ComposableMultilinearMap R f φ 1)
  (D : ComposableMultilinearMap R f φ 2)

omit [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj'] in
/-- A term of Φ ∘ F has the degree of Φ. -/
lemma comp_deg (φ : β →+ᵍ β') (ψ : β' →+ᵍ β'') (deg : Fin n → β) (c : Composition n) {j : β}
    (hj : targetDeg s deg = j) :
    ψ (targetDeg s fun l ↦ φ (targetDeg 1 fun i ↦ deg (c.embedding l i))) = (ψ.comp φ) j :=
  degMap_targetDeg_degMap_targetDeg_embedding φ ψ deg c _ (by simp) hj

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

/-- The composite Φ ∘ F of a composable multilinear map Φ with a composable multilinear map `F`
with `s = 1`, written in Mathlib's order. Its component of arity n is the sum, over all
compositions i₁ + ⋯ + iₖ = n, of Φₖ applied to the values of F_{i₁}, …, F_{iₖ}. It has the same
degree `s` as Φ, and is linear in Φ only. -/
protected def comp : ComposableMultilinearMap R (fun X ↦ g (f X)) (ψ.comp φ) s where
  map X := .mk fun deg j hj ↦ ∑ c : Composition _,
    Φ.compTermMultilinearMap X deg c (fun _ ↦ ⟨1, F⟩) ((ψ.comp φ) j) (comp_deg φ ψ deg c hj)

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

/-- The value of the component of arity n of Φ ∘ F: the sum, over all compositions `c` of `n`, of
Φ applied to the values of `F` on the blocks of `c`. -/
lemma comp_map_v_apply (hj : targetDeg s deg = j) :
    ((Φ.comp F).map X).v deg j hj a =
      ∑ c : Composition n, Φ.compTerm a c (fun _ ↦ ⟨1, F⟩) ((ψ.comp φ) j)
        (comp_deg φ ψ deg c hj) :=
  sum_apply Finset.univ (fun c ↦ Φ.compTermMultilinearMap X deg c (fun _ ↦ ⟨1, F⟩)
    ((ψ.comp φ) j) (comp_deg φ ψ deg c hj)) a

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

end Comp

end ComposableMultilinearMap

end AInfinityTheory
