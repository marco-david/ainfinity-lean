module

public import Mathlib
public import KLRW.OneBlackStrand
public import ComputableCochainComplex.AdditiveCompletion

@[expose] public section

open CategoryTheory AInfinityTheory

def T₀ : KLRWSl2OneBlackStrand 3 ℤ := ⟨0⟩
def T₁ : KLRWSl2OneBlackStrand 3 ℤ := ⟨1⟩
def T₂ : KLRWSl2OneBlackStrand 3 ℤ := ⟨2⟩
def T₃ : KLRWSl2OneBlackStrand 3 ℤ := ⟨3⟩

def X : ℤ → AddKLRWSl2OneBlackStrand 3 ℤ
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

def A : KLRWSl2OneBlackStrandComplex 3 ℤ := BoundedCochainComplex.of X {0,1} sorry d sorry

def f : A ⟶ A := BoundedCochainComplex.ofHom _ _ _ _ _ _ _ _ _ _ g sorry

-- #texify f
-- #texify f ≫ f
