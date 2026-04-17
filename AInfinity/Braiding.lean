module

public import Mathlib
public import AInfinity.KLRW
public import AInfinity.AdditiveCompletion

@[expose] public section

open CategoryTheory AInfinityTheory

universe u v w
variable {R : Type u} [CommRing R] [CharP R 2] [DecidableEq R] {n : ℕ}

structure BraidingFunctorData (R : Type u) [CommRing R] [CharP R 2] [DecidableEq R] (n : ℕ) where
  gen₀ : KLRWCategory n R → CochainComplex (CMat_ (KLRWCategory n R)) ℤ
  gen₁ : {A B : KLRWCategory n R} → (A ⟶ B) → (gen₀ A ⟶ gen₀ B)
  gen₂ : {A B C : KLRWCategory n R} → (A ⟶ B) → (B ⟶ C) → (gen₀ A ⟶ gen₀ C)

namespace BraidingFunctorData

variable (β : BraidingFunctorData R n)

def add₀ (A : CMat_ (KLRWCategory n R))
  : CochainComplex (CMat_ (KLRWCategory n R)) ℤ :=
  let _ := β -- To get β to become a parameter of this until we actually implement it
  sorry

def add₁ {A B : CMat_ (KLRWCategory n R)} (f : A ⟶ B)
  : β.add₀ A ⟶ β.add₀ B := sorry

def add₂ {A B C : CMat_ (KLRWCategory n R)} (f : A ⟶ B) (g : B ⟶ C)
  : β.add₀ A ⟶ β.add₀ B := sorry

def full₀ (A : CochainComplex (CMat_ (KLRWCategory n R)) ℤ)
  : CochainComplex (CMat_ (KLRWCategory n R)) ℤ :=
  let _ := β -- To get β to become a parameter of this until we actually implement it
  sorry

def full₁ {A B : CochainComplex (CMat_ (KLRWCategory n R)) ℤ} (f : A ⟶ B)
  : β.full₀ A ⟶ β.full₀ B := sorry

def full₂ {A B C : CochainComplex (CMat_ (KLRWCategory n R)) ℤ}
  (f : A ⟶ B) (g : B ⟶ C) : β.full₀ A ⟶ β.full₀ C := sorry
