/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import AInfinity.ArityLeTwo
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

/-! # DG categories as A∞-categories

A DG category over a commutative ring `R` is a category enriched over cochain complexes of
`R`-modules. The monoidal structure on `CochainComplex (ModuleCat R) ℤ` used for the enrichment
is Mathlib's `HomologicalComplex.monoidalCategory`: the tensor product is the total complex with
the Koszul sign d(a ⊗ b) = da ⊗ b + (-1)^|a| a ⊗ db.

We regard a DG category as an A∞-category: the graded hom spaces are the components of the
hom complexes, m₁ is the differential, m₂ is the composition, and all higher compositions
vanish.

## Main definitions

* `AInfinityTheory.DGCategory R C`: a DG category structure on `C` over `R`.
* `AInfinityTheory.DGCategory.gradedLinearQuiver`: the graded hom spaces of a DG category.
* `AInfinityTheory.DGCategory.compBilin`: a homogeneous component of the enriched composition,
  as a bilinear map.
* `AInfinityTheory.DGCategory.differential`: the signed differential.
* `AInfinityTheory.DGCategory.gradedDifferential`: the signed differential as a graded linear
  map of degree `1`, the arity-one A∞ operation.
* `AInfinityTheory.DGCategory.composition`: the signed composition, the arity-two A∞
  operation.
* `AInfinityTheory.DGCategory.aInfinityCategory`: the A∞-category with m₁ the signed
  differential, m₂ the signed composition and vanishing higher compositions, built with
  `AInfinityCategory.ofArityLeTwo`.

## Main results

* `HomologicalComplex.ιTensorObj_d`: the differential of a tensor product of complexes on a
  summand, d(a ⊗ b) = da ⊗ b + ε(p) a ⊗ db.
* `HomologicalComplex.ιTensorObj_whiskerRight_ιTensorObj_associator_hom_f`: the associator of
  complexes on a summand of the triple tensor product.
* `AInfinityTheory.DGCategory.d_compBilin`: the Leibniz rule for the enriched composition.
* `AInfinityTheory.DGCategory.compBilin_assoc`: associativity of the enriched composition on
  homogeneous morphisms.
* `AInfinityTheory.DGCategory.differential_differential`: the signed differential squares to
  zero.
* `AInfinityTheory.DGCategory.differential_composition`: the signed differential is a
  derivation of the signed composition.
* `AInfinityTheory.DGCategory.composition_composition`: the signed composition is associative
  up to sign.

## Implementation notes

We use Seidel's sign convention, written in the path order of this repository: for morphisms
a from X₀ to X₁ of degree p and b from X₁ to X₂ of degree q, m₁(a) = (-1)^p da and
m₂(a, b) = (-1)^q b ∘ a, where b ∘ a is the enriched composition `compBilin`. With these
signs the Stasheff identities of `AInfinity.Stasheff` follow from d² = 0, the Leibniz rule and
associativity of composition.

Mathlib's monoidal structure on homological complexes is obtained by transport along
`Monoidal.induced`, and its summand inclusions `HomologicalComplex.ιTensorObj` are built from
total complexes of bicomplexes. Mathlib's API for these inclusions is stated in terms of
`mapBifunctor` and graded objects, which agree with `⊗`, `◁`, `▷` and `α_` only up to unfolding
definitions, so rewriting with it requires `erw`. The `HomologicalComplex` section at the start of
this file restates the lemmas we need in terms of the monoidal structure. These lemmas live in
Mathlib's `HomologicalComplex` namespace rather than `AInfinityTheory`, since they are candidates
for upstreaming to `Mathlib.Algebra.Homology.Monoidal`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns]
  [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I]

/-- The differential of a tensor product of homological complexes, on the summand of degree
(i₁, i₂): d(a ⊗ b) = da ⊗ b + ε(i₁) a ⊗ db, where ε is the sign of the complex shape. -/
lemma ιTensorObj_d (K L : HomologicalComplex C c) {i₁ i₁' i₂ i₂' j j' : I} (h : i₁ + i₂ = j)
    (hK : c.Rel i₁ i₁') (hL : c.Rel i₂ i₂') (h₁ : i₁' + i₂ = j') (h₂ : i₁ + i₂' = j') :
    ιTensorObj K L i₁ i₂ j h ≫ (K ⊗ L).d j j' =
      (K.d i₁ i₁' ▷ L.X i₂) ≫ ιTensorObj K L i₁' i₂ j' h₁ +
        c.ε i₁ • ((K.X i₁ ◁ L.d i₂ i₂') ≫ ιTensorObj K L i₁ i₂' j' h₂) := by
  change ιMapBifunctor K L (curriedTensor C) c i₁ i₂ j h ≫
    (mapBifunctor K L (curriedTensor C) c).d j j' = _
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq _ _ _ _ hK _ _ h₁, mapBifunctor.d₂_eq _ _ _ _ _ hL _ h₂]
  simp only [ComplexShape.ε₁, ComplexShape.ε₂, TotalComplexShape.ε₁, TotalComplexShape.ε₂,
    one_smul]
  rfl

@[reassoc]
lemma ιTensorObj_whiskerLeft_f (K : HomologicalComplex C c) {L L' : HomologicalComplex C c}
    (g : L ⟶ L') (i₁ i₂ j : I) (h : i₁ + i₂ = j) :
    ιTensorObj K L i₁ i₂ j h ≫ (K ◁ g).f j = (K.X i₁ ◁ g.f i₂) ≫ ιTensorObj K L' i₁ i₂ j h := by
  -- `K ◁ g` is `tensorHom (𝟙 K) g` by definition of the monoidal structure, but only after
  -- unfolding the instance, which `simp` no longer does when matching `ι_mapBifunctorMap`.
  change ιTensorObj K L i₁ i₂ j h ≫ (tensorHom (𝟙 K) g).f j = _
  simp

@[reassoc]
lemma ιTensorObj_whiskerRight_f {K K' : HomologicalComplex C c} (f : K ⟶ K')
    (L : HomologicalComplex C c) (i₁ i₂ j : I) (h : i₁ + i₂ = j) :
    ιTensorObj K L i₁ i₂ j h ≫ (f ▷ L).f j = (f.f i₁ ▷ L.X i₂) ≫ ιTensorObj K' L i₁ i₂ j h := by
  change ιTensorObj K L i₁ i₂ j h ≫ (tensorHom f (𝟙 L)).f j = _
  simp

/-- The associator of homological complexes on the summand of degree (i₁, i₂, i₃) of the triple
tensor product: it is the associator of `C` followed by the inclusion of the summand. -/
@[reassoc]
lemma ιTensorObj_whiskerRight_ιTensorObj_associator_hom_f (K₁ K₂ K₃ : HomologicalComplex C c)
    {i₁ i₂ i₃ i₁₂ i₂₃ j : I} (h₁₂ : i₁ + i₂ = i₁₂) (h₂₃ : i₂ + i₃ = i₂₃) (h : i₁₂ + i₃ = j)
    (h' : i₁ + i₂₃ = j) :
    (ιTensorObj K₁ K₂ i₁ i₂ i₁₂ h₁₂ ▷ K₃.X i₃) ≫ ιTensorObj (K₁ ⊗ K₂) K₃ i₁₂ i₃ j h ≫
      (α_ K₁ K₂ K₃).hom.f j =
    (α_ _ _ _).hom ≫ (K₁.X i₁ ◁ ιTensorObj K₂ K₃ i₂ i₃ i₂₃ h₂₃) ≫
      ιTensorObj K₁ (K₂ ⊗ K₃) i₁ i₂₃ j h' := by
  subst h₁₂ h₂₃
  rw [← Category.assoc]
  exact GradedObject.Monoidal.ιTensorObj₃'_associator_hom K₁.X K₂.X K₃.X i₁ i₂ i₃ j h

end HomologicalComplex

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

@[simp]
lemma compBilin_apply (X Y Z : C) (p q i : ℤ) (h : p + q = i) (a : (X ⟶[V] Y).X p)
    (b : (Y ⟶[V] Z).X q) :
    compBilin X Y Z p q i h a b =
      (eComp V X Y Z).f i
        (HomologicalComplex.ιTensorObj (X ⟶[V] Y) (Y ⟶[V] Z) p q i h (a ⊗ₜ b)) :=
  rfl

/-- The enriched composition satisfies the Leibniz rule
d(b ∘ a) = b ∘ da + (-1)^p db ∘ a, where a has degree p. The degrees are
arbitrary, subject to the equations relating them. -/
lemma d_compBilin (X Y Z : C) {p q i p' q' i' : ℤ} (h : p + q = i) (hp : p + 1 = p')
    (hq : q + 1 = q') (h₁ : p' + q = i') (h₂ : p + q' = i') (a : (X ⟶[V] Y).X p)
    (b : (Y ⟶[V] Z).X q) :
    (X ⟶[V] Z).d i i' (compBilin X Y Z p q i h a b) =
      compBilin X Y Z p' q i' h₁ ((X ⟶[V] Y).d p p' a) b +
        p.negOnePow • compBilin X Y Z p q' i' h₂ a ((Y ⟶[V] Z).d q q' b) := by
  subst hp hq
  simp only [compBilin_apply]
  rw [← ModuleCat.comp_apply, (eComp V X Y Z).comm, ← ModuleCat.comp_apply, ← Category.assoc,
    HomologicalComplex.ιTensorObj_d _ _ h rfl rfl h₁ h₂]
  simp [ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply]

open HomologicalComplex in
/-- Associativity of the enriched composition, restricted to the summand of degree (p, q, r)
of the triple tensor product of hom complexes. -/
lemma ιTensorObj_eComp_assoc (W X Y Z : C) {p q r e e' d : ℤ} (h : p + q = e)
    (h' : q + r = e') (h₁ : e + r = d) (h₂ : p + e' = d) :
    (ιTensorObj (W ⟶[V] X) (X ⟶[V] Y) p q e h ▷ _) ≫ ((eComp V W X Y).f e ▷ _) ≫
      ιTensorObj (W ⟶[V] Y) (Y ⟶[V] Z) e r d h₁ ≫ (eComp V W Y Z).f d =
    (α_ _ _ _).hom ≫ (_ ◁ ιTensorObj (X ⟶[V] Y) (Y ⟶[V] Z) q r e' h') ≫
      (_ ◁ (eComp V X Y Z).f e') ≫ ιTensorObj (W ⟶[V] X) (X ⟶[V] Z) p e' d h₂ ≫
        (eComp V W X Z).f d := by
  rw [← ιTensorObj_whiskerRight_f_assoc, ← comp_f, ← e_assoc' V W X Y Z,
    ← ιTensorObj_whiskerLeft_f_assoc, comp_f, comp_f,
    ιTensorObj_whiskerRight_ιTensorObj_associator_hom_f_assoc _ _ _ h h' h₁ h₂]

/-- The enriched composition is associative on homogeneous morphisms:
c ∘ (b ∘ a) = (c ∘ b) ∘ a. The degrees are arbitrary, subject to the
equations relating them. -/
lemma compBilin_assoc (W X Y Z : C) {p q r e e' d : ℤ} (h : p + q = e) (h' : q + r = e')
    (h₁ : e + r = d) (h₂ : p + e' = d) (a : (W ⟶[V] X).X p) (b : (X ⟶[V] Y).X q)
    (c : (Y ⟶[V] Z).X r) :
    compBilin W Y Z e r d h₁ (compBilin W X Y p q e h a b) c =
      compBilin W X Z p e' d h₂ a (compBilin X Y Z q r e' h' b c) :=
  congr($(ιTensorObj_eComp_assoc W X Y Z h h' h₁ h₂) ((a ⊗ₜ b) ⊗ₜ c))

/-- The differential of a DG category, with Seidel's sign: a morphism a from X to Y of degree
p is sent to (-1)^p da, where d is the differential of the hom complex `X ⟶[V] Y`. As for
`HomologicalComplex.d`, it is defined for all degrees `p` and `q`, and vanishes unless
`q = p + 1`. -/
def differential (X Y : C) (p q : ℤ) : (X →ᵍ[R] Y) p →ₗ[R] (X →ᵍ[R] Y) q :=
  p.negOnePow • ((X ⟶[V] Y).d p q).hom

@[simp]
lemma differential_apply (X Y : C) (p q : ℤ) (a : (X →ᵍ[R] Y) p) :
    differential X Y p q a = p.negOnePow • (X ⟶[V] Y).d p q a :=
  rfl

lemma differential_eq_zero (X Y : C) {p q : ℤ} (h : p + 1 ≠ q) :
    differential (R := R) X Y p q = 0 := by
  rw [differential, HomologicalComplex.shape _ _ _ h, ModuleCat.hom_zero, smul_zero]

/-- The differential squares to zero. This is the arity-one Stasheff identity. -/
lemma differential_differential (X Y : C) (p q r : ℤ) (a : (X →ᵍ[R] Y) p) :
    differential X Y q r (differential X Y p q a) = 0 := by
  simp only [differential_apply, Units.smul_def, map_zsmul, ← ModuleCat.comp_apply,
    HomologicalComplex.d_comp_d, ModuleCat.hom_zero, LinearMap.zero_apply, smul_zero]

/-- The composition of a DG category, with Seidel's sign: morphisms a from X to Y of degree p
and b from Y to Z of degree q are sent to (-1)^q b ∘ a, where b ∘ a is the enriched
composition `compBilin`. -/
noncomputable def composition (X Y Z : C) (p q i : ℤ) (h : p + q = i) :
    (X →ᵍ[R] Y) p →ₗ[R] (Y →ᵍ[R] Z) q →ₗ[R] (X →ᵍ[R] Z) i :=
  q.negOnePow • compBilin X Y Z p q i h

@[simp]
lemma composition_apply (X Y Z : C) (p q i : ℤ) (h : p + q = i) (a : (X →ᵍ[R] Y) p)
    (b : (Y →ᵍ[R] Z) q) :
    composition X Y Z p q i h a b = q.negOnePow • compBilin X Y Z p q i h a b :=
  rfl

/-- The signed differential is a derivation of the signed composition, with Seidel's signs:
m₁(m₂(a, b)) = (-1)^q m₂(m₁(a), b) - m₂(a, m₁(b)), where b has degree q. The
degrees are arbitrary, subject to the equations relating them. -/
lemma differential_composition (X Y Z : C) {p q e p' q' d : ℤ} (h : p + q = e)
    (hp : p + 1 = p') (hq : q + 1 = q') (he : e + 1 = d)
    (a : (X →ᵍ[R] Y) p) (b : (Y →ᵍ[R] Z) q) :
    differential X Z e d (composition X Y Z p q e h a b) =
      q.negOnePow • composition X Y Z p' q d (hp ▸ he ▸ h ▸ add_right_comm p 1 q)
        (differential X Y p p' a) b -
        composition X Y Z p q' d (hq ▸ he ▸ h ▸ (add_assoc p q 1).symm) a
          (differential Y Z q q' b) := by
  subst h hp hq he
  simp only [differential_apply, composition_apply, Units.smul_def, map_zsmul,
    LinearMap.smul_apply, d_compBilin X Y Z rfl rfl rfl (add_right_comm _ _ _)
      (add_assoc _ _ _).symm]
  rw [Int.negOnePow_add, Int.negOnePow_succ]
  rcases Int.units_eq_one_or p.negOnePow with hp | hp <;>
    rcases Int.units_eq_one_or q.negOnePow with hq | hq <;>
    simp only [hp, hq, Units.val_one, Units.val_neg, one_smul, neg_smul, mul_one, mul_neg,
      neg_neg, smul_add, smul_neg] <;> abel

/-- The signed composition is associative up to Seidel's sign:
m₂(m₂(a, b), c) = (-1)^r m₂(a, m₂(b, c)), where c has degree r. The degrees are arbitrary,
subject to the equations relating them. -/
lemma composition_composition (W X Y Z : C) {p q r e e' d : ℤ} (h : p + q = e)
    (h' : q + r = e') (h₁ : e + r = d) (a : (W →ᵍ[R] X) p) (b : (X →ᵍ[R] Y) q)
    (c : (Y →ᵍ[R] Z) r) :
    composition W Y Z e r d h₁ (composition W X Y p q e h a b) c =
      r.negOnePow • composition W X Z p e' d (h' ▸ h₁ ▸ h ▸ (add_assoc p q r).symm) a
        (composition X Y Z q r e' h' b c) := by
  subst h h' h₁
  simp only [composition_apply, Units.smul_def, map_zsmul, LinearMap.smul_apply, smul_smul,
    compBilin_assoc W X Y Z rfl rfl rfl (add_assoc _ _ _).symm, Int.negOnePow_add]
  rcases Int.units_eq_one_or q.negOnePow with hq | hq <;>
    rcases Int.units_eq_one_or r.negOnePow with hr | hr <;> simp [hq, hr]

variable (R) in
/-- The signed differential of a DG category as a graded linear map of degree `1`: the
arity-one A∞ operation. -/
def gradedDifferential (X Y : C) : GradedLinearMap R (X →ᵍ[R, ℤ] Y) (X →ᵍ[R] Y) degOne :=
  .mk fun p q _ ↦ differential X Y p q

@[simp]
lemma gradedDifferential_v (X Y : C) (p q : ℤ) (h : p + degOne = q) :
    (gradedDifferential R X Y).v p q h = differential X Y p q :=
  rfl

/-- The Koszul sign (-1)^‖a‖ of an input a of degree n, where ‖a‖ = n - 1, is
-(-1)^n. -/
lemma toMul_sign_sub_degOne (n : ℤ) : (sign (n - degOne)).toMul = -n.negOnePow := by
  change (n - 1).negOnePow = _
  rw [Int.negOnePow_sub, Int.negOnePow_one, mul_neg, mul_one]

/-- A DG category is an A∞-category: m₁ is the signed differential, m₂ is the signed
composition, and the higher compositions mₙ for n ≥ 3 vanish. The Stasheff identities in
arities 1, 2 and 3 are d² = 0, the Leibniz rule and associativity of composition. -/
noncomputable instance aInfinityCategory : AInfinityCategory ℤ R C :=
  .ofArityLeTwo (gradedDifferential R) composition
    (fun X Y _ _ _ _ _ a ↦ differential_differential X Y _ _ _ a)
    (fun X Y Z _ _ _ _ _ _ h hp hq he a b ↦ by
      simp only [gradedDifferential_v]
      rw [differential_composition X Y Z h hp hq he, toMul_sign_sub_degOne,
        Units.neg_smul]
      abel)
    (fun W X Y Z _ _ _ _ _ _ h h' h₁ a b c ↦ by
      rw [composition_composition W X Y Z h h' h₁, toMul_sign_sub_degOne, Units.neg_smul,
        smul_smul, Int.units_mul_self, one_smul, neg_add_cancel])

end DGCategory

end AInfinityTheory
