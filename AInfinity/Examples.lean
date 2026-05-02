module

public import Mathlib
public import AInfinity.KLRW
public import AInfinity.AdditiveCompletion

@[expose] public section

open CategoryTheory AInfinityTheory

def T₀ : KLRWCategory 3 ℤ := ⟨0⟩
def T₁ : KLRWCategory 3 ℤ := ⟨1⟩
def T₂ : KLRWCategory 3 ℤ := ⟨2⟩
def T₃ : KLRWCategory 3 ℤ := ⟨3⟩

def g : [T₀, T₁]ₘ ⟶ [T₀, T₁]ₘ := CMat_.Hom.ofFin _ _ fun
| 0, 0 => StrandSpace.dots ℤ 1
| 1, 0 => StrandSpace.dots ℤ 1
| 0, 1 => StrandSpace.dots ℤ 1
| 1, 1 => StrandSpace.dots ℤ 1

def X : ℤ → AddKLRWCategory 3 ℤ
| 0 => [T₀,T₁]ₘ
| 1 => [T₀,T₁]ₘ
| _ => 𝟎

def cc : KLRWComplexCategory 3 ℤ := BoundedCochainComplex.of X {0,1} sorry 0 sorry

def cm : cc ⟶ cc := BoundedCochainComplex.ofHom _ _ _ _ _ _ _ _ _ _ (fun i ↦ 0) sorry

#texify cm
