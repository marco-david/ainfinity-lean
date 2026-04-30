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
    if M.toList.length = 0 ∧ N.toList.length = 0 then
      "0"
    else if M.toList.length = 0 ∨ N.toList.length = 0 then
      s!"0^\{{N.toList.length} \\times {M.toList.length}}"
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

-- TODO: Make this work well with `List.toFinsupp`, except you need to cast from ℕ to ℤ

def BoundedCochainComplex.mk' {V : Type*} [Category V] [HasExplicitZeroObject V]
  [DecidablePred (Limits.IsZero : V → Prop)]
  [Preadditive V] (X : ℤ → V) (supersetOfSupport : Finset ℤ)
  (h : ∀ i : ℤ, ¬ Limits.IsZero (X i) → i ∈ supersetOfSupport)
  (d : ∀ i : ℤ, X i ⟶ X (i + 1))
  (hd : ∀ i ∈ supersetOfSupport, d i ≫ d (i + 1) = 0) : BoundedCochainComplex V :=
  BoundedCochainComplex.mkOfBounded (CochainComplex.of X d hi) h
  where hi (i : ℤ) : d i ≫ d (i + 1) = 0 := (by
    by_cases hc : i ∈ supersetOfSupport
    · exact hd i hc
    · rw [hc.imp_symm (h i) |>.eq_zero_of_src (d i)]
      simp)

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
    (leftmost rightmost : ℤ) : String := Id.run do
    let mut res := ""
    for i in leftmost...rightmost do
      res := res ++ s!"{texifyWithBrackets (A.X i)} @>{texifyWithBrackets (A.d i (i + 1))}>>"
    res := res ++ s!"{texifyWithBrackets (A.X rightmost)}"
    return r"\begin{CD}" ++ res ++ r"\end{CD}"

instance (C : Type*) [Category C] [Preadditive C] [Limits.HasZeroObject C] [Texify C]
  [∀ (X Y : C), Texify (X ⟶ Y)] : Texify (BoundedCochainComplex C) where
  texify A := Id.run do
    let leftmost := -2
    let rightmost := 2
    return r"\begin{CD}" ++ A.toTexRow leftmost rightmost ++ r"\end{CD}"
  requiresParentheses := true

def X : ℤ → AddKLRWCategory 3 ℤ
| 0 => [T₀]ₘ
| _ => 𝟎
def cc : KLRWComplexCategory 3 ℤ := BoundedCochainComplex.mk' X {0} sorry 0 (by
  intro i hi
  fin_cases hi <;> sorry
)

#texify cc
