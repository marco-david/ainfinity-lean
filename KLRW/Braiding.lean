/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import Mathlib
public import KLRW.OneBlackStrand
public import ComputableCochainComplex.AdditiveCompletion

/-!
# Braiding data with finite support on ordinary complexes

Object images are ordinary KLRW cochain complexes with separate `BoundedComplex` data.
Maps and shifts use Mathlib directly. The additive and total-complex extensions remain
unfinished; their existing object-construction placeholders keep the complex and its
support together internally, while the public operations return ordinary complexes.
-/

@[expose] public section

open CategoryTheory AInfinityTheory

universe u
variable {R : Type u} [CommRing R] [CharP R 2] [DecidableEq R] {n : ℕ}

/-- Object and morphism data for a braiding, with finite support on each object image. -/
structure BraidingFunctorData (R : Type u) [CommRing R] [CharP R 2] [DecidableEq R] (n : ℕ) where
  /-- The ordinary complex assigned to a generating KLRW object. -/
  gen₀ : KLRWCategory n R → KLRWComplexCategory n R
  /-- A supplied finite support bound for each generating object image. -/
  gen₀BoundedComplex : ∀ A, BoundedComplex (gen₀ A)
  /-- The cochain map assigned to a generating morphism. -/
  gen₁ : {A B : KLRWCategory n R} → (A ⟶ B) → (gen₀ A ⟶ gen₀ B)
  /-- The higher component valued in the shifted target complex. -/
  gen₂ : {A B C : KLRWCategory n R} → (A ⟶ B) → (B ⟶ C) →
    (gen₀ A ⟶ ((CochainComplex.shiftFunctor (AddKLRWCategory n R) (-1)).obj (gen₀ C)))

  --SFₙ axioms. Note:
  --KLRW is a preadditive category, so its Hom-space is
  --all degree 0. Then only μ₂ is nonzero (it is composition).
  --Tw(Add(KLRW)) is a dg-category, so it has μ₁ = d, μ₂ = composition,
  --and no higher terms.
  /-
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
    -/
attribute [instance] BraidingFunctorData.gen₀BoundedComplex

namespace BraidingFunctorData

variable (β : BraidingFunctorData R n)


/-- The unfinished additive object construction, retaining its support with its output. -/
def addData (A : CMat_ (KLRWCategory n R)) :
    (C : KLRWComplexCategory n R) × BoundedComplex C :=
  -- This is the existing additive-extension placeholder.
  let _ := β
  sorry

/-- The ordinary complex assigned to an object of the additive completion. -/
def add₀ (A : CMat_ (KLRWCategory n R)) : KLRWComplexCategory n R :=
  (addData β A).1

/-- The additive object construction supplies a finite support bound for its image. -/
instance add₀BoundedComplex (A : CMat_ (KLRWCategory n R)) :
    BoundedComplex (β.add₀ A) := (addData β A).2

/-- The unfinished action on morphisms of the additive completion. -/
def add₁ {A B : CMat_ (KLRWCategory n R)} (f : A ⟶ B) :
    β.add₀ A ⟶ β.add₀ B := sorry

/-- The unfinished higher component on morphisms of the additive completion. -/
def add₂ {A B C : CMat_ (KLRWCategory n R)} (f : A ⟶ B) (g : B ⟶ C) :
    β.add₀ A ⟶ β.add₀ C := sorry

/-- The unfinished total-complex construction, retaining its output's finite support. -/
def fullData (A : KLRWComplexCategory n R) [BoundedComplex A] :
    (C : KLRWComplexCategory n R) × BoundedComplex C :=
  -- This is the existing total-complex extension placeholder.
  let _ := β
  sorry

/-- Apply the braiding to an ordinary KLRW complex with supplied finite support. -/
def full₀ (A : KLRWComplexCategory n R) [BoundedComplex A] :
    KLRWComplexCategory n R :=
  (fullData β A).1

/-- The total-complex construction preserves supplied finite support. -/
instance full₀BoundedComplex (A : KLRWComplexCategory n R) [BoundedComplex A] :
    BoundedComplex (β.full₀ A) := (fullData β A).2

/-- The unfinished action on ordinary cochain maps between finite-support inputs. -/
def full₁ {A B : KLRWComplexCategory n R}
    [BoundedComplex A] [BoundedComplex B]
    (f : A ⟶ B) : β.full₀ A ⟶ β.full₀ B := sorry

/-- The unfinished higher component on ordinary cochain maps between finite-support inputs. -/
def full₂ {A B C : KLRWComplexCategory n R}
    [BoundedComplex A] [BoundedComplex B]
    [BoundedComplex C]
    (f : A ⟶ B) (g : B ⟶ C) : β.full₀ A ⟶ β.full₀ C := sorry

end BraidingFunctorData
