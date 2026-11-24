/-
Copyright (c) 2026 Jason Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Dong, Marco David
-/
module

public import AInfinity.ArityLeTwo
public import ComputableCochainComplex.FinCochain

/-! # Bounded cochain complexes as an A∞-category

Bounded cochain complexes in an `R`-linear category `V` form a DG category, whose hom complex
from `X` to `Y` is the complex of cochains `FinCochain X Y`. We regard it as an A∞-category with
grading `ℤ`: the morphisms of degree `n` are the cochains of degree `n`, m₁ is the differential
δ of the hom complex, m₂ is the composition of cochains with a sign, and all higher compositions
vanish.

## Main definitions

* `BoundedCochainComplex.gradedLinearQuiver`: the graded hom spaces `FinCochain X Y n`.
* `BoundedCochainComplex.gradedDifferential`: the differential δ as a graded linear map of
  degree `1`, the arity-one A∞ operation.
* `BoundedCochainComplex.composition`: the signed composition, the arity-two A∞ operation.
* `BoundedCochainComplex.aInfinityCategory`: the A∞-category with these operations, built with
  `AInfinityCategory.ofArityLeTwo`.

## Implementation notes

For cochains a from `X` to `Y` of degree p and b from `Y` to `Z` of degree q, the operations are
m₁(a) = δa and m₂(a, b) = (-1)^q a ≫ b, where δ and the composition a ≫ b are
`FinCochain.δ` and `FinCochain.comp`, which agree with those of Mathlib's
`CochainComplex.HomComplex`, written in diagrammatic order. Mathlib's differential
satisfies the Leibniz rule δ(a ≫ b) = a ≫ δb + (-1)^q δa ≫ b, which differs from the Leibniz
rule d(a ≫ b) = da ≫ b + (-1)^p a ≫ db of `AInfinityTheory.DGCategory` by the sign (-1)^p on
the differential. With this sign, Seidel's convention m₁(a) = (-1)^p da of
`AInfinityTheory.DGCategory` becomes m₁ = δ, so the operations above agree with those of the
DG category of bounded complexes.

The three Stasheff identities that `AInfinityCategory.ofArityLeTwo` asks for follow from
`FinCochain.δ_δ`, `FinCochain.δ_comp` and `FinCochain.comp_assoc`, up to the signs above.

We do not obtain this A∞-category from a `AInfinityTheory.DGCategory` structure on bounded
complexes. That structure is an enrichment in Mathlib's monoidal category of complexes of
`R`-modules, whose tensor product is built from noncomputably chosen coproducts, so the inherited
operations would be noncomputable, whereas the operations here compute on `FinCochain`. Moreover
`AInfinityTheory.DGCategory.aInfinityCategory` is an instance for every DG category, so a DG
structure on bounded complexes would come with a second A∞ instance, not definitionally equal to
this one.

## References

* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Zurich Lectures in Advanced
  Mathematics, European Mathematical Society, 2008.
-/

@[expose] public section

namespace BoundedCochainComplex

open CategoryTheory Limits AInfinityTheory GradedLinearQuiver

variable {V : Type*} [Category V] [HasZeroObject V] [Preadditive V]
variable (R : Type*) [CommRing R] [Linear R V]

/-- The graded hom spaces of bounded cochain complexes: the morphisms of degree `n` from `X` to
`Y` are the cochains `FinCochain X Y n` of degree `n`. -/
instance gradedLinearQuiver : GradedLinearQuiver ℤ R (BoundedCochainComplex V) where
  Hom X Y n := FinCochain X Y n

/-- The differential δ of the hom complexes of bounded cochain complexes, as a graded linear map
of degree `1`: the arity-one A∞ operation. -/
def gradedDifferential (X Y : BoundedCochainComplex V) :
    GradedLinearMap R (X →ᵍ[R, ℤ] Y) (X →ᵍ[R] Y) degOne :=
  .mk fun p q _ ↦ FinCochain.δLinear R X Y p q

/-- The composition of bounded cochain complexes with Seidel's sign: cochains a from `X` to `Y`
of degree `p` and b from `Y` to `Z` of degree `q` are sent to (-1)^q a ≫ b, in degree `i`, where
`p + q = i`. This is the arity-two A∞ operation. -/
def composition (X Y Z : BoundedCochainComplex V) (p q i : ℤ) (h : p + q = i) :
    (X →ᵍ[R] Y) p →ₗ[R] (Y →ᵍ[R] Z) q →ₗ[R] (X →ᵍ[R] Z) i :=
  q.negOnePow • FinCochain.compBilin R X Y Z p q i h

variable {R}

@[simp]
lemma gradedDifferential_v_apply {X Y : BoundedCochainComplex V} {p q : ℤ} (h : p + degOne = q)
    (a : (X →ᵍ[R] Y) p) : (gradedDifferential R X Y).v p q h a = FinCochain.δ p q a :=
  rfl

@[simp]
lemma composition_apply {X Y Z : BoundedCochainComplex V} {p q i : ℤ} (h : p + q = i)
    (a : (X →ᵍ[R] Y) p) (b : (Y →ᵍ[R] Z) q) :
    composition R X Y Z p q i h a b = q.negOnePow • a.comp b h :=
  rfl

/-- The differential squares to zero. This is the arity-one Stasheff identity. -/
lemma gradedDifferential_v_gradedDifferential_v (X Y : BoundedCochainComplex V) {p q r : ℤ}
    (hpq : p + degOne = q) (hqr : q + degOne = r) (a : (X →ᵍ[R] Y) p) :
    (gradedDifferential R X Y).v q r hqr ((gradedDifferential R X Y).v p q hpq a) = 0 :=
  FinCochain.δ_δ p q r a

/-- The differential is a derivation of the signed composition: the arity-two Stasheff
identity. The degrees are arbitrary, subject to the equations relating them. -/
lemma composition_leibniz (X Y Z : BoundedCochainComplex V) {p q e p' q' d : ℤ} (h : p + q = e)
    (hp : p + degOne = p') (hq : q + degOne = q') (he : e + degOne = d) (h₁ : p' + q = d)
    (h₂ : p + q' = d) (a : (X →ᵍ[R] Y) p) (b : (Y →ᵍ[R] Z) q) :
    (sign (q - degOne)).toMul •
        composition R X Y Z p' q d h₁ ((gradedDifferential R X Y).v p p' hp a) b +
      composition R X Y Z p q' d h₂ a ((gradedDifferential R Y Z).v q q' hq b) +
      (gradedDifferential R X Z).v e d he (composition R X Y Z p q e h a b) = 0 := by
  subst hq
  simp only [composition_apply, gradedDifferential_v_apply, FinCochain.δ_units_smul,
    FinCochain.δ_comp a b h p' (q + degOne) d he hp rfl, toMul_sign_sub_degOne, toMul_sign_int,
    show (q + degOne).negOnePow = -q.negOnePow from Int.negOnePow_succ q, smul_add, smul_smul,
    neg_mul, Int.units_mul_self, Units.neg_smul, one_smul]
  abel

/-- The signed composition is associative up to the Koszul sign: the arity-three Stasheff
identity. The degrees are arbitrary, subject to the equations relating them. -/
lemma composition_assoc (W X Y Z : BoundedCochainComplex V) {p q r e e' d : ℤ} (h : p + q = e)
    (h' : q + r = e') (h₁ : e + r = d) (h₂ : p + e' = d) (a : (W →ᵍ[R] X) p)
    (b : (X →ᵍ[R] Y) q) (c : (Y →ᵍ[R] Z) r) :
    (sign (r - degOne)).toMul • composition R W Y Z e r d h₁ (composition R W X Y p q e h a b) c +
      composition R W X Z p e' d h₂ a (composition R X Y Z q r e' h' b c) = 0 := by
  subst h'
  simp only [composition_apply, FinCochain.units_smul_comp, FinCochain.comp_units_smul,
    FinCochain.comp_assoc a b c h rfl (show p + q + r = d by omega), toMul_sign_sub_degOne,
    toMul_sign_int, Int.negOnePow_add]
  rcases Int.units_eq_one_or q.negOnePow with hq | hq <;>
    rcases Int.units_eq_one_or r.negOnePow with hr | hr <;> simp [hq, hr]

/-- Bounded cochain complexes form an A∞-category with grading `ℤ`: m₁ is the differential δ of
the hom complexes, m₂ is the signed composition (-1)^q a ≫ b, and the higher compositions mₙ for
n ≥ 3 vanish. The Stasheff identities in arities 1, 2 and 3 are δ² = 0, the Leibniz rule and
associativity of composition. -/
instance aInfinityCategory : AInfinityCategory ℤ R (BoundedCochainComplex V) :=
  .ofArityLeTwo (gradedDifferential R) (composition R) gradedDifferential_v_gradedDifferential_v
    (fun X Y Z _ _ _ _ _ _ h hp hq he a b ↦ composition_leibniz X Y Z h hp hq he _ _ a b)
    (fun W X Y Z _ _ _ _ _ _ h h' h₁ a b c ↦ composition_assoc W X Y Z h h' h₁ _ a b c)

end BoundedCochainComplex
