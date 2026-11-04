module

public import Mathlib
public import KLRW.OneBlackStrand
public import ComputableCochainComplex.AdditiveCompletion

@[expose] public section

open CategoryTheory AInfinityTheory

def T₀ : KLRWCategory 3 ℤ := ⟨0⟩
def T₁ : KLRWCategory 3 ℤ := ⟨1⟩
def T₂ : KLRWCategory 3 ℤ := ⟨2⟩
def T₃ : KLRWCategory 3 ℤ := ⟨3⟩

def X : ℤ → AddKLRWCategory 3 ℤ
| 0 => [T₀,T₁]ₘ
| 1 => [T₂,T₃]ₘ
| _ => 𝟎

def d : (i : ℤ) → X i ⟶ X (i + 1)
| 0 => CMat_.Hom.ofFin _ _ fun
  | 0, 0 => 2 • StrandSpace.dots ℤ 2
  | 1, 0 => 0
  | 0, 1 => 2 • StrandSpace.dots ℤ 0
  | 1, 1 => 2 • StrandSpace.dots ℤ 1
| _ => 0

theorem d_comp_d (i : ℤ) : d i ≫ d (i + 1) = 0 := by
  by_cases hi : i = 0
  · subst i
    exact Limits.comp_zero
  · simp [d]

def g : (i : ℤ) → X i ⟶ X i
| 0 => CMat_.Hom.ofFin _ _ fun
  | 0, 0 => StrandSpace.dots ℤ 2
  | 1, 0 => 0
  | 0, 1 => StrandSpace.dots ℤ 0
  | 1, 1 => StrandSpace.dots ℤ 1
| 1 => CMat_.Hom.ofFin _ _ fun
  | 0, 0 => StrandSpace.dots ℤ 2
  | 1, 0 => 0
  | 0, 1 => StrandSpace.dots ℤ 0
  | 1, 1 => StrandSpace.dots ℤ 1
| _ => 0

/-- The two-term example complex, with support bounded by degrees zero and one. -/
def A : KLRWComplexCategory 3 ℤ :=
  BoundedCochainComplex.ofComplex (CochainComplex.of X d d_comp_d) (support := {0, 1}) (by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    simpa [X, hi.1, hi.2] using (isZero_explicitZero (C := AddKLRWCategory 3 ℤ)))

/-- The endomorphism of the example complex with components `g`. -/
def f : A ⟶ A :=
  BoundedCochainComplex.homMk (CochainComplex.ofHom X d d_comp_d X d d_comp_d g sorry)

-- #texify f
-- #texify f ≫ f
