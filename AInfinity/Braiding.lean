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
  gen₂ : {A B C : KLRWCategory n R} → (A ⟶ B) → (B ⟶ C) → ∀ (i : ℤ), (gen₀ A).X i → (gen₀ B).X (i - 1)
  -- invoke shift functor from boundedcochaincomplexes

  --SFₙ axioms. Note:
  --KLRW is a preadditive category, so its Hom-space is
  --all degree 0. Then only μ₂ is nonzero (it is composition).
  --Tw(Add(KLRW)) is a dg-category, so it has μ₁ = d, μ₂ = composition,
  --and no higher terms.
  SF₂ : ∀ {A B C : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (i : ℤ),
    (gen₁ (f ≫ g)).f i + (gen₁ f ≫ gen₁ g).f i
      = gen₂ f g i ≫ (gen₀ C).d (i - 1) i
        + (gen₀ A).d i (i + 1) ≫ gen₂ f g (i + 1)
  SF₃ : ∀ {A B C D : KLRWCategory n R}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (i : ℤ),
    gen₂ (f ≫ g) h i + gen₂ f (g ≫ h) i
      = (gen₁ f).f i ≫ gen₂ g h i
        + gen₂ f g i ≫ (gen₁ h).f (i - 1)
  SF₄ : ∀ {A B C D E : KLRWCategory n R}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E) (i : ℤ),
    gen₂ f g i ≫ gen₂ h k (i - 1) = 0
namespace BraidingFunctorData

variable (β : BraidingFunctorData R n)

def add₀ (A : CMat_ (KLRWCategory n R))
  : CochainComplex (CMat_ (KLRWCategory n R)) ℤ :=
  -- Idea: Use CochainComplex.singleFunctor
  let _ := β -- To get β to become a parameter of this until we actually implement it
  sorry

def add₁ {A B : CMat_ (KLRWCategory n R)} (f : A ⟶ B)
  -- Idea: Use the action of CochainComplex.singleFunctor on maps
  : β.add₀ A ⟶ β.add₀ B := sorry

def add₂ {A B C : CMat_ (KLRWCategory n R)} (f : A ⟶ B) (g : B ⟶ C)
  : β.add₀ A ⟶ β.add₀ C := sorry

def full₀ (A : CochainComplex (CMat_ (KLRWCategory n R)) ℤ)
  : CochainComplex (CMat_ (KLRWCategory n R)) ℤ :=
  let _ := β -- To get β to become a parameter of this until we actually implement it
  sorry

def full₁ {A B : CochainComplex (CMat_ (KLRWCategory n R)) ℤ} (f : A ⟶ B)
  : β.full₀ A ⟶ β.full₀ B := sorry

def full₂ {A B C : CochainComplex (CMat_ (KLRWCategory n R)) ℤ}
  (f : A ⟶ B) (g : B ⟶ C) : β.full₀ A ⟶ β.full₀ C := sorry


def PositiveTranspositionBraidingData (k : Fin (n + 1)) : BraidingFunctorData R n where
  gen₀ := fun A =>
    if specialPosition then
      specialCaseObj A k
    else
      generalCaseObj A
  gen₁ := fun f =>
    if specialPosition then
      specialCaseMor f k
    else
      generalCaseMor f
  gen₂ := fun f g i x =>
    sorry -- gen_2 does not seem to be defined as the correct type

where
  specialPosition (A : KLRWCategory n R) (k : ℕ): bool :=
    A.positioning = k
  specialCaseObj (A : KLRWCategory n R) (k : ℕ) :=
  { X := fun i =>
      match i with
      | 0 => sorry -- T_k-1 + T_k+1
      | 1 => sorry -- T_k in add
      | _ => sorry -- zero
    d := myDifferentials -- indexed by 1
    d_comp_d := sorry }
  generalCaseObj (A : KLRWCategory n R) (k : ℕ) :=
    sorry -- Should just return A but as a cochain complex
  specialCaseMor f k :=
    sorry
  generalCaseMor f :=
    sorry
