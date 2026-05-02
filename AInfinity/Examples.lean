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
    if M.toList.length = 0 ∨ N.toList.length = 0 then
      "0"
    else
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
def CMat_.Hom.ofFin {C : Type*} [Category C] [Preadditive C] (xs ys : List C)
    (f : Π (i : Fin xs.length) (j : Fin ys.length), xs[i] ⟶ ys[j]) :
    CMat_.ofList xs ⟶ CMat_.ofList ys := f

def g : [T₀, T₁]ₘ ⟶ [T₀, T₁]ₘ := CMat_.Hom.ofFin _ _ fun
| 0, 0 => StrandSpace.dots ℤ 1
| 1, 0 => StrandSpace.dots ℤ 1
| 0, 1 => StrandSpace.dots ℤ 1
| 1, 1 => StrandSpace.dots ℤ 1

#texify g ≫ g

-- TODO: Make a constructor for BoundedCochainComplex work well with `List.toFinsupp`,
-- except you need to cast from ℕ to ℤ

/--
The KLRW Category lacks zero objects
-/
theorem AInfinityTheory.KLRWCategory.not_isZero (R : Type*) [CommRing R] [DecidableEq R] (n : ℕ)
  (A : KLRWCategory n R) : ¬ Limits.IsZero A := sorry

instance (R : Type*) [CommRing R] [DecidableEq R] (n : ℕ) :
    DecidablePred (Limits.IsZero : KLRWCategory n R → Prop) :=
  fun A ↦ Decidable.isFalse (A.not_isZero)

instance {V : Type*} [Category V] [Preadditive V] [DecidablePred (Limits.IsZero : V → Prop)] :
    DecidablePred (Limits.IsZero : CMat_ V → Prop) := fun M ↦
  if h : M.toList.all (Limits.IsZero ·) then
    Decidable.isTrue sorry
  else
    Decidable.isFalse sorry

def BoundedCochainComplex.toTexRow {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
    [Texify C] [∀ (X Y : C), Texify (X ⟶ Y)] (A : BoundedCochainComplex C)
    (leftmost rightmost : ℤ) (placeDifferentialsBelow : Bool := false) : String := Id.run do
    let mut res := ""
    for i in leftmost...rightmost do
      if placeDifferentialsBelow then
        res := res ++ s!"{texifyWithBrackets (A.X i)} @>>{texifyWithBrackets (A.d i (i + 1))}>"
      else
        res := res ++ s!"{texifyWithBrackets (A.X i)} @>{texifyWithBrackets (A.d i (i + 1))}>>"
    res := res ++ s!"{texifyWithBrackets (A.X rightmost)}"
    return res

def BoundedCochainComplex.Hom.toTexRow {C : Type*} [Category C] [Preadditive C]
    [Limits.HasZeroObject C] [Texify C] [∀ (X Y : C), Texify (X ⟶ Y)]
    {A B : BoundedCochainComplex C}
    (h : A ⟶ B) (leftmost rightmost : ℤ) : String := Id.run do
    let mut res := ""
    for i in leftmost...rightmost do
      res := res ++ s!"@V{texifyWithBrackets (h.f i)}VV"
    return res

instance (C : Type*) [Category C] [Preadditive C] [Limits.HasZeroObject C] [Texify C]
  [∀ (X Y : C), Texify (X ⟶ Y)] : Texify (BoundedCochainComplex C) where
  texify A := Id.run do
    let (leftmost, rightmost) := if h : A.support.Nonempty then
      (A.support.min' h - 1, A.support.max' h + 1)
    else (-1, 1)
    return r"\begin{CD}" ++ A.toTexRow leftmost rightmost ++ r"\end{CD}"
  requiresParentheses := true

instance (C : Type*) [Category C] [Preadditive C] [Limits.HasZeroObject C] [Texify C]
  [∀ (X Y : C), Texify (X ⟶ Y)] (A B : BoundedCochainComplex C) : Texify (A ⟶ B) where
  texify h := Id.run do
    let (leftmostA, rightmostA) := if h : A.support.Nonempty then
      (A.support.min' h - 1, A.support.max' h + 1)
    else (-1, 1)
    let (leftmostB, rightmostB) := if h : B.support.Nonempty then
      (B.support.min' h - 1, B.support.max' h + 1)
    else (-1, 1)
    let leftmost := min leftmostA leftmostB
    let rightmost := max rightmostA rightmostB
    return r"\begin{CD}" ++ A.toTexRow leftmost rightmost ++ r"\\" ++ h.toTexRow leftmost rightmost
      ++ r"\\" ++ B.toTexRow leftmost rightmost true ++ r"\end{CD}"
  requiresParentheses := true

def X : ℤ → AddKLRWCategory 3 ℤ
| 0 => [T₀,T₁]ₘ
| 1 => [T₀,T₁]ₘ
| _ => 𝟎

def cc : KLRWComplexCategory 3 ℤ := BoundedCochainComplex.of X {0,1} sorry 0 sorry

def cm : cc ⟶ cc := BoundedCochainComplex.ofHom _ _ _ _ _ _ _ _ _ _ (fun i ↦ 0) sorry

#texify cm
