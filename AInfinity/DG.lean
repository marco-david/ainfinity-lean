/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import AInfinity.AInfinityCategory
public import AInfinity.MultilinearMap
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

/-! # DG categories as `A∞`-category structures

A DG category over a commutative ring `R` is a category enriched over cochain complexes of
`R`-modules. The monoidal structure on `CochainComplex (ModuleCat R) ℤ` used for the enrichment
is Mathlib's `HomologicalComplex.monoidalCategory`: the tensor product is the total complex with
the Koszul sign `d(a ⊗ b) = da ⊗ b + (-1)^|a| a ⊗ db`.

The goal of this file is to regard a DG category as an `A∞`-category: the graded hom spaces
are the components of the hom complexes, `m₁` is the differential, `m₂` is the composition, and
all higher compositions vanish.

## Main definitions

* `AInfinityTheory.DGCategory R C`: a DG category structure on `C` over `R`.
* `AInfinityTheory.DGCategory.gradedLinearQuiver`: the graded hom spaces of a DG category.
* `AInfinityTheory.DGCategory.compBilin`: a homogeneous component of the enriched composition,
  as a bilinear map.
* `AInfinityTheory.DGCategory.differential`: the signed differential.
* `AInfinityTheory.DGCategory.m₁`: the signed differential as a graded multilinear map in one
  variable, the arity-one `A∞` operation.
* `AInfinityTheory.DGCategory.composition`: the signed composition.
* `AInfinityTheory.DGCategory.m₂`: the signed composition as a graded multilinear map in two
  variables, the arity-two `A∞` operation.
* `AInfinityTheory.DGCategory.aInfinityCategoryStruct`: the `A∞`-category structure with
  operations `m₁` and `m₂`, and vanishing higher compositions.

## Implementation notes

We use Seidel's sign convention, written in the path order of this repository: for
`a : X₀ → X₁` of degree `p` and `b : X₁ → X₂` of degree `q`,
`m₁(a) = (-1)^p da` and `m₂(a, b) = (-1)^q a ≫ b`. With these signs the Stasheff identities of
`AInfinity.Stasheff` follow from `d² = 0`, the Leibniz rule and associativity of composition.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace AInfinityTheory

universe u w

variable (R : Type u) [CommRing R] (C : Type w)

/-- A DG category over `R`: a category enriched over cochain complexes of `R`-modules, with the
monoidal structure given by the tensor product of complexes. -/
abbrev DGCategory := EnrichedCategory (CochainComplex (ModuleCat R) ℤ) C

namespace DGCategory

open GradedLinearQuiver

variable {R C} [DGCategory R C]

local notation "V" => CochainComplex (ModuleCat R) ℤ

/-- The graded hom spaces of a DG category: the morphisms of degree `i` from `X` to `Y` are the
degree-`i` component of the hom complex `X ⟶[V] Y`. -/
instance gradedLinearQuiver : GradedLinearQuiver ℤ R C where
  Hom X Y i := (X ⟶[V] Y).X i

/-- The component of the enriched composition on morphisms of degrees `p` and `q`, as a bilinear
map into the degree-`i` component of the hom complex, where `p + q = i`. -/
noncomputable def compBilin (X Y Z : C) (p q i : ℤ) (h : p + q = i) :
    (X ⟶[V] Y).X p →ₗ[R] (Y ⟶[V] Z).X q →ₗ[R] (X ⟶[V] Z).X i :=
  (TensorProduct.mk R _ _).compr₂
    (((eComp V X Y Z).f i).hom ∘ₗ
      (HomologicalComplex.ιTensorObj (X ⟶[V] Y) (Y ⟶[V] Z) p q i h).hom)

/-- The bilinear composition evaluates the enriched composition on the corresponding summand of
the tensor product of hom complexes. -/
@[simp]
lemma compBilin_apply (X Y Z : C) (p q i : ℤ) (h : p + q = i) (a : (X ⟶[V] Y).X p)
    (b : (Y ⟶[V] Z).X q) :
    compBilin X Y Z p q i h a b =
      (eComp V X Y Z).f i
        (HomologicalComplex.ιTensorObj (X ⟶[V] Y) (Y ⟶[V] Z) p q i h (a ⊗ₜ b)) :=
  rfl

/-- The differential of a DG category, with Seidel's sign: a morphism `a : X → Y` of degree `p`
is sent to `(-1)^p da`, where `d` is the differential of the hom complex `X ⟶[V] Y`. As for
`HomologicalComplex.d`, it is defined for all degrees `p` and `q`, and vanishes unless
`q = p + 1`. -/
def differential (X Y : C) (p q : ℤ) : (X →ᵍ[R] Y) p →ₗ[R] (X →ᵍ[R] Y) q :=
  p.negOnePow • ((X ⟶[V] Y).d p q).hom

/-- The differential is the differential of the hom complex, twisted by the sign `(-1)^p`. -/
@[simp]
lemma differential_apply (X Y : C) (p q : ℤ) (a : (X →ᵍ[R] Y) p) :
    differential X Y p q a = p.negOnePow • (X ⟶[V] Y).d p q a :=
  rfl

/-- The differential vanishes between degrees that are not consecutive. -/
lemma differential_eq_zero (X Y : C) {p q : ℤ} (h : p + 1 ≠ q) :
    differential (R := R) X Y p q = 0 := by
  rw [differential, HomologicalComplex.shape _ _ _ h, ModuleCat.hom_zero, smul_zero]

/-- The differential squares to zero. This is the arity-one Stasheff identity. -/
lemma differential_differential (X Y : C) (p q r : ℤ) (a : (X →ᵍ[R] Y) p) :
    differential X Y q r (differential X Y p q a) = 0 := by
  simp only [differential_apply, Units.smul_def, map_zsmul, ← ModuleCat.comp_apply,
    HomologicalComplex.d_comp_d, ModuleCat.hom_zero, LinearMap.zero_apply, smul_zero]

/-- The composition of a DG category, with Seidel's sign: morphisms `a : X → Y` of degree `p`
and `b : Y → Z` of degree `q` are sent to `(-1)^q a ≫ b`, where `a ≫ b` is the enriched
composition `compBilin`. -/
noncomputable def composition (X Y Z : C) (p q i : ℤ) (h : p + q = i) :
    (X →ᵍ[R] Y) p →ₗ[R] (Y →ᵍ[R] Z) q →ₗ[R] (X →ᵍ[R] Z) i :=
  q.negOnePow • compBilin X Y Z p q i h

/-- The composition is the enriched composition, twisted by the sign `(-1)^q`. -/
@[simp]
lemma composition_apply (X Y Z : C) (p q i : ℤ) (h : p + q = i) (a : (X →ᵍ[R] Y) p)
    (b : (Y →ᵍ[R] Z) q) :
    composition X Y Z p q i h a b = q.negOnePow • compBilin X Y Z p q i h a b :=
  rfl

/-- The arity-one `A∞` operation of a DG category: the signed differential `differential`,
regarded as a graded multilinear map in one variable. -/
def m₁ (X : Fin (1 + 1) → C) : AInfinityOperation ℤ R X :=
  .ofGradedLinearMap (.mk fun p q _ ↦ differential (X 0) (X 1) p q)

@[simp]
lemma m₁_v_apply (X : Fin (1 + 1) → C) (deg : Fin 1 → ℤ) (i : ℤ)
    (h : (∑ k, deg k) + shift (2 - ((1 : ℕ) : ℤ)) = i)
    (x : ∀ k, ComposableHom ℤ R X k (deg k)) :
    (m₁ X).v deg i h x = differential (X 0) (X 1) (deg 0) i (x 0) :=
  rfl

/-- The arity-two `A∞` operation of a DG category: the signed composition `composition`,
regarded as a graded multilinear map in two variables. -/
noncomputable def m₂ (X : Fin (2 + 1) → C) : AInfinityOperation ℤ R X :=
  .ofBilinear fun p q i h ↦ composition (X 0) (X 1) (X 2) p q i h

@[simp]
lemma m₂_v_apply (X : Fin (2 + 1) → C) (deg : Fin 2 → ℤ) (i : ℤ)
    (h : (∑ k, deg k) + shift (2 - ((2 : ℕ) : ℤ)) = i)
    (x : ∀ k, ComposableHom ℤ R X k (deg k)) :
    (m₂ X).v deg i h x =
      composition (X 0) (X 1) (X 2) (deg 0) (deg 1) i
        (by simpa [Fin.sum_univ_two] using h) (x 0) (x 1) :=
  rfl

/-- The `A∞`-category structure of a DG category: `m₁` is the signed differential, `m₂` is the
signed composition, and the higher compositions `mₙ` for `n ≥ 3` vanish. -/
noncomputable instance aInfinityCategoryStruct : AInfinityCategoryStruct ℤ R C where
  toGradedLinearQuiver := gradedLinearQuiver
  m := AInfinityOperation.ofArityLeTwo m₁ m₂

@[simp]
lemma m_one (X : Fin (1 + 1) → C) : AInfinityCategoryStruct.m (β := ℤ) (R := R) X = m₁ X :=
  rfl

@[simp]
lemma m_two (X : Fin (2 + 1) → C) : AInfinityCategoryStruct.m (β := ℤ) (R := R) X = m₂ X :=
  rfl

lemma m_eq_zero {n : ℕ} [NeZero n] (h₁ : n ≠ 1) (h₂ : n ≠ 2) (X : Fin (n + 1) → C) :
    AInfinityCategoryStruct.m (β := ℤ) (R := R) X = 0 :=
  AInfinityOperation.ofArityLeTwo_eq_zero _ _ h₁ h₂ X

end DGCategory

end AInfinityTheory
