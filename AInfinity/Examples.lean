module

public import Mathlib
public import AInfinity.KLRW
public import AInfinity.AdditiveCompletion
public import AInfinity.Braiding
public meta import AInfinity.KLRW
public meta import AInfinity.AdditiveCompletion
public meta import AInfinity.BoundedCochainComplex
public meta import AInfinity.Braiding

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

def A : KLRWComplexCategory 3 ℤ := BoundedCochainComplex.of X {0,1} sorry d sorry

def f : A ⟶ A := BoundedCochainComplex.ofHom _ _ _ _ _ _ _ _ _ _ g sorry

-- TODO: these need a `Texify` instance for `BoundedCochainComplex.Hom` and,
-- since `#texify` refuses terms whose code depends on `sorry`, the `sorry`s in
-- `A`/`f` above must be filled before they can render:
-- #texify f
-- #texify f ≫ f

/-! ### The braiding functor on a single positioning

`beta_gen 0` (over `𝔽₂ = ZMod 2`, `n = 3` marked points) braids the 0-th and
1-st marked points: the T-brane at the braided position `1` goes to the
two-term complex `T₀ ⊕ T₂ ⟶ T₁`, every other positioning stays a one-term
complex in degree `0`. -/

instance : ToString (ZMod 2) := ⟨fun x => toString x.val⟩

def U₀ : KLRWCategory 3 (ZMod 2) := ⟨0⟩
def U₁ : KLRWCategory 3 (ZMod 2) := ⟨1⟩

-- the braided positioning: T₁ ↦ (T₀ ⊕ T₂ ⟶ T₁)
#texify (BraidingFunctorData.beta_gen (R := ZMod 2) (n := 3) 0).obj U₁

-- an unaffected positioning: T₀ ↦ T₀ in degree 0
#texify (BraidingFunctorData.beta_gen (R := ZMod 2) (n := 3) 0).obj U₀
