module

public import Mathlib
public import KLRW.OneBlackStrand
public import ComputableCochainComplex.AdditiveCompletion

@[expose] public section

open CategoryTheory AInfinityTheory


universe u v w

/-! ### The braiding action on objects

The braiding of the `i`-th and `(i + 1)`-th red strands sends the T-brane at the braided position
`k = i + 1` (the black strand sitting between the two red strands) to the two-term complex
`T_{k-1} ⊕ T_{k+1} ⟶ T_k` in degrees `0` and `1`, with dotless differential; every other
positioning is unchanged, viewed as a complex concentrated in degree `0`. -/

namespace AInfinityTheory.KLRWCategory

variable {R : Type u} [CommRing R] [DecidableEq R] {n : ℕ}

/-- A positioning as a one-term cochain complex in degree `0`. -/
def braneComplex (A : KLRWCategory n R) : CochainComplex (AddKLRWCategory n R) ℤ where
  X i := if i = 0 then [A]ₘ else 𝟎
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := Limits.zero_comp

/-- The two-term complex `[Tneg, Tpos]ₘ ⟶ [A]ₘ` in degrees `0` and `1`, with dotless differential:
every matrix entry of the differential is the unit strand `StrandSpace.dots R 0`. -/
def braidedBraneComplex (Tneg Tpos A : KLRWCategory n R) :
    CochainComplex (AddKLRWCategory n R) ℤ where
  X i := if i = 0 then [Tneg, Tpos]ₘ else if i = 1 then [A]ₘ else 𝟎
  d i j :=
    if hij : i = 0 ∧ j = 1 then by
      rcases hij with ⟨rfl, rfl⟩
      exact fun _ _ => StrandSpace.dots R 0
    else 0
  shape i j hij := by
    by_cases h01 : i = 0 ∧ j = 1
    · exfalso
      rcases h01 with ⟨rfl, rfl⟩
      exact hij (by simp [ComplexShape.up, ComplexShape.up'])
    · simp [h01]
  d_comp_d' i j l hij hjl := by
    by_cases h01 : i = 0 ∧ j = 1
    · rcases h01 with ⟨rfl, rfl⟩
      rw [dif_pos ⟨rfl, rfl⟩, dif_neg (show ¬((1 : ℤ) = 0 ∧ l = 1) by norm_num), Limits.comp_zero]
    · rw [dif_neg h01]
      exact Limits.zero_comp

/-- `braneComplex A` vanishes outside degree `0`. -/
lemma isZero_braneComplex_X (A : KLRWCategory n R) {i : ℤ} (hi : i ≠ 0) :
    Limits.IsZero ((braneComplex A).X i) := by
  show Limits.IsZero (if i = 0 then _ else _)
  rw [if_neg hi]
  exact isZero_explicitZero

/-- `braidedBraneComplex Tneg Tpos A` vanishes outside degrees `0` and `1`. -/
lemma isZero_braidedBraneComplex_X (Tneg Tpos A : KLRWCategory n R) {i : ℤ} (h0 : i ≠ 0)
    (h1 : i ≠ 1) : Limits.IsZero ((braidedBraneComplex Tneg Tpos A).X i) := by
  show Limits.IsZero (if i = 0 then _ else if i = 1 then _ else _)
  rw [if_neg h0, if_neg h1]
  exact isZero_explicitZero

/-- A positioning as a bounded one-term complex in degree `0`. -/
def brane (A : KLRWCategory n R) : KLRWComplexCategory n R :=
  BoundedCochainComplex.mkOfBounded (braneComplex A) (supersetOfSupport := {0}) fun _ hi =>
    Finset.mem_singleton.mpr (not_not.mp (mt (isZero_braneComplex_X A) hi))

/-- The braided T-brane: the bounded two-term complex `[Tneg, Tpos]ₘ ⟶ [A]ₘ` in degrees `0`
and `1`. -/
def braidedBrane (Tneg Tpos A : KLRWCategory n R) : KLRWComplexCategory n R :=
  BoundedCochainComplex.mkOfBounded (braidedBraneComplex Tneg Tpos A)
    (supersetOfSupport := {0, 1}) fun i hi => by
      rw [Finset.mem_insert, Finset.mem_singleton]
      by_contra hmem
      push Not at hmem
      exact hi (isZero_braidedBraneComplex_X Tneg Tpos A hmem.1 hmem.2)

/-- The braiding action on objects for the transposition of the `i`-th and `(i + 1)`-th red
strands (`i : Fin (n - 1)`, so that only genuine transpositions are expressible): the braided
position is `k = i + 1`, whose T-brane becomes the two-term complex `T_{k-1} ⊕ T_{k+1} ⟶ T_k`;
every other positioning is unchanged. -/
def braidingObj (i : Fin (n - 1)) (A : KLRWCategory n R) : KLRWComplexCategory n R :=
  if A.positioning = (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (n + 1)) then
    braidedBrane ⟨⟨i.val, by have := i.isLt; omega⟩⟩ ⟨⟨i.val + 2, by have := i.isLt; omega⟩⟩ A
  else
    brane A

end AInfinityTheory.KLRWCategory

variable {R : Type u} [CommRing R] [CharP R 2] [DecidableEq R] {n : ℕ}

structure BraidingFunctorData (R : Type u) [CommRing R] [CharP R 2] [DecidableEq R] (n : ℕ) where
  gen₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R))
  gen₁ : {A B : KLRWCategory n R} → (A ⟶ B) → (gen₀ A ⟶ gen₀ B)
  gen₂ : {A B C : KLRWCategory n R} → (A ⟶ B) → (B ⟶ C) →
    (gen₀ A ⟶ ((BoundedCochainComplex.shiftFunctor (-1 : ℤ)).obj (gen₀ C)))
  -- invoke shift functor from boundedcochaincomplexes

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
namespace BraidingFunctorData

variable (β : BraidingFunctorData R n)


def add₀ (A : CMat_ (KLRWCategory n R))
  : BoundedCochainComplex (CMat_ (KLRWCategory n R)) :=
  -- Idea: Use CochainComplex.singleFunctor
  let _ := β -- To get β to become a parameter of this until we actually implement it
  sorry

def add₁ {A B : CMat_ (KLRWCategory n R)} (f : A ⟶ B)
  -- Idea: Use the action of CochainComplex.singleFunctor on maps
  : β.add₀ A ⟶ β.add₀ B := sorry

def add₂ {A B C : CMat_ (KLRWCategory n R)} (f : A ⟶ B) (g : B ⟶ C)
  : β.add₀ A ⟶ β.add₀ C := sorry

def full₀ (A : BoundedCochainComplex (CMat_ (KLRWCategory n R)))
  : BoundedCochainComplex (CMat_ (KLRWCategory n R)) :=
  let _ := β -- To get β to become a parameter of this until we actually implement it
  sorry

def full₁ {A B : BoundedCochainComplex (CMat_ (KLRWCategory n R))} (f : A ⟶ B)
  : β.full₀ A ⟶ β.full₀ B := sorry

def full₂ {A B C : BoundedCochainComplex (CMat_ (KLRWCategory n R))}
  (f : A ⟶ B) (g : B ⟶ C) : β.full₀ A ⟶ β.full₀ C := sorry
