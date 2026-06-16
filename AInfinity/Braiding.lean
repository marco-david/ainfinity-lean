module

public import AInfinity.KLRW
public import AInfinity.AdditiveCompletion
public import AInfinity.BoundedCochainComplex

@[expose] public section

open CategoryTheory AInfinityTheory CochainComplex.HomComplex


universe u v w
variable {R : Type u} [CommRing R] [CharP R 2] [DecidableEq R] {n : ℕ}

structure BraidingFunctorData (R : Type u) [CommRing R] [CharP R 2] [DecidableEq R] (n : ℕ) where
  gen₀ : KLRWCategory n R → CochainComplex (CMat_ (KLRWCategory n R)) ℤ
  gen₁ : {A B : KLRWCategory n R} → (A ⟶ B) → (gen₀ A ⟶ gen₀ B)
  gen₂ : {A B C : KLRWCategory n R} → (A ⟶ B) → (B ⟶ C) → ∀ (i : ℤ), (gen₀ A).X i ⟶ (gen₀ C).X (i - 1)
  -- is there an alternate way we want to type this? Do we have a
  -- shorthand for degree whatever chain complex maps?

  -- These are the finite A∞ functor axioms from the blueprint,
  -- for β.gen: KLRW → K•(Add(KLRW)). They will be used to prove the A∞ functor axioms
  -- for Add(KLRW) → K•(Add(KLRW)).
  SF₂ : ∀ {A B C : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (i : ℤ),
    (gen₁ (f ≫ g)).f i
      = (gen₁ f ≫ gen₁ g).f i
        + gen₂ f g i ≫ (gen₀ C).d (i - 1) i
        + (gen₀ A).d i (i + 1) ≫ gen₂ f g (i + 1) ≫
          eqToHom (by rw [show i + 1 - 1 = i by omega])
  SF₃ : ∀ {A B C D : KLRWCategory n R}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (i : ℤ),
    gen₂ f (g ≫ h) i + gen₂ (f ≫ g) h i
      = (gen₁ f).f i ≫ gen₂ g h i
        + gen₂ f g i ≫ (gen₁ h).f (i - 1)
  SF₄ : ∀ {A B C D E : KLRWCategory n R}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E) (i : ℤ),
    gen₂ f g i ≫ gen₂ h k (i - 1) = 0

  gen₂ : {A B C : KLRWCategory n R} → (A ⟶ B) → (B ⟶ C) →
    ((BoundedCochainComplex.shiftFunctor 1).obj (gen₀ A) ⟶ gen₀ C)
  /-
  --SFₙ axioms. Note:
  --KLRW is a preadditive category, so its Hom-space is
  --all degree 0. Then only μ₂ is nonzero (it is composition).
  --Tw(Add(KLRW)) is a dg-category, so it has μ₁ = d, μ₂ = composition,
  --and no higher terms.

  -- [SF₁.gen]: gen₁(f) is a chain map, i.e. 0 = μ₁^B(gen₁(f)).
  -- Concretely: 0 = (gen₁ f)ᵢ ≫ d^i_{gen₀B} + d^i_{gen₀A} ≫ (gen₁ f)_{i+1}
  sf₁ : ∀ {A B : KLRWCategory n R} (f : A ⟶ B) (i : ℤ),
    (0 : (gen₀ A).X i ⟶ (gen₀ B).X (i + 1)) =
    (gen₁ f).f i ≫ (gen₀ B).d i (i + 1) +
    (gen₀ A).d i (i + 1) ≫ (gen₁ f).f (i + 1)

  -- [SF₂.gen]: β₁(μ₂^A(f, g)) = μ₂^B(β₁(f), β₁(g)) + μ₁^B(β₂(f, g))
  -- (gen₂ f g).f i : (gen₀ A).X (i+1) ⟶ (gen₀ C).X i
  -- μ₁^B(gen₂ f g) at degree (i+1):
  --   d^A_{i+1,i+2} ≫ (gen₂ f g).f (i+1)  :  X_A(i+1) ⟶ X_C(i+1)
  --   (gen₂ f g).f i ≫ d^C_{i,i+1}         :  X_A(i+1) ⟶ X_C(i+1)
  sf₂ : ∀ {A B C : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (i : ℤ),
    (gen₁ (f ≫ g)).f (i + 1) =
    (gen₁ f).f (i + 1) ≫ (gen₁ g).f (i + 1) +
    ((gen₀ A).d (i + 1) (i + 2) ≫ (gen₂ f g).f (i + 1) +
     (gen₂ f g).f i ≫ (gen₀ C).d i (i + 1))

  -- [SF₃.gen]: β₂(f, μ₂^A(g, h)) + β₂(μ₂^A(f, g), h) = μ₂^B(β₁(f), β₂(g, h)) + μ₂^B(β₂(f, g), β₁(h))
  -- (gen₁ f).f (i+1) ≫ (gen₂ g h).f i : (gen₀ A).X (i+1) ⟶ (gen₀ D).X i
  -- (gen₂ f g).f i ≫ (gen₁ h).f i     : (gen₀ A).X (i+1) ⟶ (gen₀ D).X i
  sf₃ : ∀ {A B C D : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (i : ℤ),
    (gen₂ f (g ≫ h)).f i + (gen₂ (f ≫ g) h).f i =
    (gen₁ f).f (i + 1) ≫ (gen₂ g h).f i +
    (gen₂ f g).f i ≫ (gen₁ h).f i

  -- [SF₄.gen]: 0 = μ₂^B(β₂(f, g), β₂(h, k))
  -- (shiftFunctor 1).map (gen₂ f g) : (shiftFunctor 1)² (gen₀ A) ⟶ (shiftFunctor 1) (gen₀ C)
  sf₄ : ∀ {A B C D E : KLRWCategory n R}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E),
    (BoundedCochainComplex.shiftFunctor 1).map (gen₂ f g) ≫ gen₂ h k = 0 -/

namespace BraidingFunctorData

variable (β : BraidingFunctorData R n)

structure BraidingFunctorAdd (R : Type u) [CommRing R] [CharP R 2] [DecidableEq R] (n : ℕ) where
  add₀ : CMat_ (KLRWCategory n R) → BoundedCochainComplex (CMat_ (KLRWCategory n R))
  add₁ : {A B : CMat_ (KLRWCategory n R)} → (A ⟶ B) → (add₀ A ⟶ add₀ B)
  add₂ : {A B C : CMat_ (KLRWCategory n R)} → (A ⟶ B) → (B ⟶ C) →
    ((BoundedCochainComplex.shiftFunctor 1).obj (add₀ A) ⟶ add₀ C)

structure BraidingFunctorFull (R : Type u) [CommRing R] [CharP R 2] [DecidableEq R] (n : ℕ) where
  full₀ : BoundedCochainComplex (CMat_ (KLRWCategory n R)) → BoundedCochainComplex (CMat_ (KLRWCategory n R))
  full₁ : {A B : BoundedCochainComplex (CMat_ (KLRWCategory n R))} → (A ⟶ B) → (full₀ A ⟶ full₀ B)
  full₂ : {A B C : BoundedCochainComplex (CMat_ (KLRWCategory n R))} → (A ⟶ B) → (B ⟶ C) →
    ((BoundedCochainComplex.shiftFunctor 1).obj (full₀ A) ⟶ full₀ C)
