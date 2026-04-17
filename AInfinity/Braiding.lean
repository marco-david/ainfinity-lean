module

public import Mathlib
public import AInfinity.KLRW
public import AInfinity.AdditiveCompletion

@[expose] public section

open CategoryTheory AInfinityTheory

universe u v w
variable {R : Type u} [CommRing R] [CharP R 2] [DecidableEq R] {n : ℕ}

structure BraidingFunctorData where
  gen₀ : KLRWCategory n R → CochainComplex (CMat_ (KLRWCategory n R)) ℤ
  gen₁ : {A B : KLRWCategory n R} → (A ⟶ B) → (gen₀ A ⟶ gen₀ B)
  gen₂ : {A B C : KLRWCategory n R} → (A ⟶ B) → (B ⟶ C) → (gen₀ A ⟶ gen₀ C)

def BraidingFunctorData.add₀ (A : CMat_ (KLRWCategory n R))
  : CochainComplex (CMat_ (KLRWCategory n R)) ℤ := sorry

def BraidingFunctorData.add₁ {A B : CMat_ (KLRWCategory n R)} (f : A ⟶ B)
  : add₀ A ⟶ add₀ B := sorry

def BraidingFunctorData.add₂ {A B C : CMat_ (KLRWCategory n R)} (f : A ⟶ B) (g : B ⟶ C)
  : add₀ A ⟶ add₀ B := sorry

def BraidingFunctorData.full₀ (A : CochainComplex (CMat_ (KLRWCategory n R)) ℤ)
  : CochainComplex (CMat_ (KLRWCategory n R)) ℤ := sorry

def BraidingFunctorData.full₁ {A B : CochainComplex (CMat_ (KLRWCategory n R)) ℤ} (f : A ⟶ B)
  : full₀ A ⟶ full₀ B := sorry

def BraidingFunctorData.full₂ {A B C : CochainComplex (CMat_ (KLRWCategory n R)) ℤ}
  (f : A ⟶ B) (g : B ⟶ C) : full₀ A ⟶ full₀ C := sorry
