import Mathlib
import AInfinity.AdditiveCompletion

open CategoryTheory Limits

/-!
# Bounded Cochain Complexes

A computable version of `CochainComplex` backed by `List`, analogous to
`CMat_` vs `Mat_`. Objects are stored as a finite list with an explicit
starting cohomological degree.
-/


structure BoundedCochainComplex (V : Type*) [Category V] [HasZeroObject V] [Preadditive V]
    extends CochainComplex V ℤ where
  support : Finset ℤ
  not_isZero_iff_mem_support : ∀ i : ℤ, ¬ IsZero (X i) ↔ i ∈ support

def BoundedCochainComplex.length {V : Type*} [Category V] [HasZeroObject V] [Preadditive V]
    (c : BoundedCochainComplex V) : ℤ :=
  if h : c.support.Nonempty then c.support.max' h - c.support.min' h else 0

def BoundedCochainComplex.mkOfBounded {V : Type*} [Category V] [HasZeroObject V] [Preadditive V]
    [DecidablePred (IsZero : V → Prop)]
    (c : CochainComplex V ℤ) {supersetOfSupport : Finset ℤ}
    (h : ∀ i : ℤ, ¬ IsZero (c.X i) → i ∈ supersetOfSupport)
    : BoundedCochainComplex V where
  X := c.X
  d := c.d
  support := {i ∈ supersetOfSupport | ¬ IsZero (c.X i)}
  not_isZero_iff_mem_support := by
    sorry

theorem BoundedCochainComplex.mkOfBounded_eq
    {V : Type*} [Category V] [HasZeroObject V] [Preadditive V]
    [DecidablePred (IsZero : V → Prop)] (c : CochainComplex V ℤ)
    {s₁ s₂ : Finset ℤ}
    (h₁ : ∀ i : ℤ, ¬ IsZero (c.X i) → i ∈ s₁)
    (h₂ : ∀ i : ℤ, ¬ IsZero (c.X i) → i ∈ s₂)
  : BoundedCochainComplex.mkOfBounded c h₁ = BoundedCochainComplex.mkOfBounded c h₂ := by
  sorry

namespace BoundedCochainComplex

variable {V : Type*} [Category V] [HasZeroObject V] [Preadditive V]

instance : Category (BoundedCochainComplex V) where
  Hom A B := sorry
  id A := sorry
  comp := sorry
instance : Preadditive (BoundedCochainComple V) := sorry

def BoundedCochainComplex.embed : BoundedCochainComplex V ⥤ CochainComplex V ℤ := sorry

instance : Functor.Faithful (BoundedCochainComplex.embed (V := V)) := sorry
instance : Functor.Full (BoundedCochainComplex.embed (V := V)) := sorry

variable {R : Type*} [CommRing R] [Linear R V] in
instance : Linear R (BoundedCochainComplex V) := sorry

end BoundedCochainComplex
