module

public import Mathlib
public import KLRW.OneBlackStrand
public import ComputableCochainComplex.AdditiveCompletion

@[expose] public section

open CategoryTheory KLRW.Sl2

def T₀ : TBrane 3 ℤ := ⟨0⟩
def T₁ : TBrane 3 ℤ := ⟨1⟩
def T₂ : TBrane 3 ℤ := ⟨2⟩
def T₃ : TBrane 3 ℤ := ⟨3⟩

def X : ℤ → CMat_ (TBrane 3 ℤ)
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

def A : TBraneComplex 3 ℤ := BoundedCochainComplex.of X {0,1} sorry d sorry

def f : A ⟶ A := BoundedCochainComplex.ofHom _ _ _ _ _ _ _ _ _ _ g sorry

-- #texify f
-- #texify f ≫ f
