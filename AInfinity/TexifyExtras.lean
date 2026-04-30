module

public import Mathlib
public import AInfinity.KLRW
public import AInfinity.AdditiveCompletion

@[expose] public section

open CategoryTheory AInfinityTheory

instance (R : Type*) [CommRing R] [DecidableEq R] [ToString R] (n : ℕ) (S T : KLRWCategory n R) :
  Texify (S ⟶ T) := inferInstanceAs (Texify (StrandSpace R))

def T₀ : KLRWCategory 3 ℤ := ⟨0⟩
def T₁ : KLRWCategory 3 ℤ := ⟨1⟩
def T₂ : KLRWCategory 3 ℤ := ⟨2⟩

def h : T₀ ⟶ T₁ := StrandSpace.dots ℤ 3

instance (C : Type*) [Category C] [Preadditive C] [∀ (X Y : C), Texify (X ⟶ Y)] (M N : CMat_ C) :
    Texify (CMat_.Hom M N) where
  texify x :=
    let getEntry (i : Fin N.toList.length) (j : Fin M.toList.length) : String :=
      texifyWithBrackets (x (CMat_.ι.ofFin j) (CMat_.ι.ofFin i))
    let getRow (i : Fin N.toList.length) : String :=
      Finset.univ.sort.map (getEntry i) |> " & ".intercalate
    let entries : String := Finset.univ.sort.map getRow |> r" \\ ".intercalate
    r"\begin{pmatrix} " ++ entries ++ r" \end{pmatrix}"
  requiresParentheses := false

instance (C : Type*) [Category C] [Preadditive C] [∀ (X Y : C), Texify (X ⟶ Y)] (M N : CMat_ C) :
    Texify (M ⟶ N) := inferInstanceAs (Texify (CMat_.Hom M N))

unseal CMat_.ι CMat_.X in
def g : [T₀, T₁]ₘ ⟶ [T₀, T₁]ₘ
| (0 : Fin _), (0 : Fin _) => StrandSpace.dots ℤ 1
| (1 : Fin _), (0 : Fin _) => StrandSpace.dots ℤ 1
| (0 : Fin _), (1 : Fin _) => StrandSpace.dots ℤ 1
| (1 : Fin _), (1 : Fin _) => StrandSpace.dots ℤ 1

#texify g ≫ g
