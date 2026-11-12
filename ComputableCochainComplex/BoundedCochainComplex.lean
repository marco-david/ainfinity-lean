/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Util.Texify

/-!
# Finite support on cochain complexes

`BoundedComplex C` equips an ordinary cochain complex with an explicit `Finset ℤ`
containing its support. This class makes no assumptions about finite free coordinates.
The bound may include zero terms, so it requires no decision of object vanishing.
Shifts transport this data using Mathlib's existing shift functor.

All complexes and cochain maps are Mathlib objects, with no bundled bounded-complex type.
`CochainComplex.toTex` renders a complex using its support instance, and `Texify` renders
cochain maps whose endpoints have supplied finite support.
-/

@[expose] public section

open CategoryTheory Limits


/-- A supplied finite bound on the degrees with nonzero terms of an existing complex.
This is executable data, independent of any coordinates or freeness of the terms. -/
class BoundedComplex {V : Type*} [Category V] [Preadditive V]
    (C : CochainComplex V ℤ) where
  /-- A finite superset of the degrees with nonzero terms. -/
  support : Finset ℤ
  /-- Every term outside the supplied bound is a zero object. -/
  isZero_of_notMem_support : ∀ i : ℤ, i ∉ support → IsZero (C.X i)

namespace BoundedComplex

variable {V : Type*} [Category V] [Preadditive V]

/-- Shifting a complex translates its supplied support bound by the negative shift. -/
instance shift (C : CochainComplex V ℤ) [BoundedComplex C] (n : ℤ) :
    BoundedComplex ((CochainComplex.shiftFunctor V n).obj C) where
  support := (support C).image (· - n)
  isZero_of_notMem_support i hi := by
    change IsZero (C.X (i + n))
    apply isZero_of_notMem_support (C := C)
    intro h
    exact hi (Finset.mem_image.mpr ⟨i + n, h, add_sub_cancel_right i n⟩)

end BoundedComplex

namespace CochainComplex

/-- Render the objects and differentials of an ordinary complex over an explicit interval. -/
def toTexRow {V : Type*} [Category V] [Preadditive V]
    [Texify V] [∀ (X Y : V), Texify (X ⟶ Y)] (A : CochainComplex V ℤ)
    (leftmost rightmost : ℤ) (placeDifferentialsBelow : Bool := false) : String := Id.run do
  let mut res := ""
  for i in leftmost...rightmost do
    if placeDifferentialsBelow then
      res := res ++ s!"{texifyWithBrackets (A.X i)} @>>{texifyWithBrackets (A.d i (i + 1))}>"
    else
      res := res ++ s!"{texifyWithBrackets (A.X i)} @>{texifyWithBrackets (A.d i (i + 1))}>>"
  res := res ++ s!"{texifyWithBrackets (A.X rightmost)}"
  return res

/-- Render a complex over its supplied finite support interval, including adjacent zero terms.
The support instance belongs to this complex, so rendering is an operation on the object. -/
def toTex {V : Type*} [Category V] [Preadditive V]
    [Texify V] [∀ (X Y : V), Texify (X ⟶ Y)] (A : CochainComplex V ℤ)
    [BoundedComplex A] : String := Id.run do
  let support := BoundedComplex.support A
  let (leftmost, rightmost) := if h : support.Nonempty then
    (support.min' h - 1, support.max' h + 1)
  else (-1, 1)
  return r"\begin{CD}" ++ A.toTexRow leftmost rightmost ++ r"\end{CD}"

end CochainComplex

namespace HomologicalComplex.Hom

/-- Render the components of an ordinary cochain map over an explicit interval. -/
def toTexRow {V : Type*} [Category V] [Preadditive V]
    [Texify V] [∀ (X Y : V), Texify (X ⟶ Y)] {A B : CochainComplex V ℤ}
    (h : A ⟶ B) (leftmost rightmost : ℤ) : String := Id.run do
  let mut res := ""
  for i in leftmost...=rightmost do
    res := res ++ s!"@V{texifyWithBrackets (h.f i)}VV"
  return res

/-- Render a cochain map using the independently supplied support bounds of its endpoints. -/
instance {V : Type*} [Category V] [Preadditive V]
    [Texify V] [∀ (X Y : V), Texify (X ⟶ Y)] (A B : CochainComplex V ℤ)
    [BoundedComplex A] [BoundedComplex B] : Texify (A ⟶ B) where
  texify h := Id.run do
    let supportA := BoundedComplex.support A
    let supportB := BoundedComplex.support B
    let (leftmostA, rightmostA) := if h : supportA.Nonempty then
      (supportA.min' h - 1, supportA.max' h + 1)
    else (-1, 1)
    let (leftmostB, rightmostB) := if h : supportB.Nonempty then
      (supportB.min' h - 1, supportB.max' h + 1)
    else (-1, 1)
    let leftmost := min leftmostA leftmostB
    let rightmost := max rightmostA rightmostB
    return r"\begin{CD}" ++ A.toTexRow leftmost rightmost ++ r"\\" ++ h.toTexRow leftmost rightmost
      ++ r"\\" ++ B.toTexRow leftmost rightmost true ++ r"\end{CD}"
  requiresParentheses := true

end HomologicalComplex.Hom
