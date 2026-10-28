/-
Copyright (c) 2026 Justin Mu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Mu, Annie Yao, Niels Voss, Marco David
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.ZMod.IntUnitsPower

/-! # Gradings for A-infinity categories

This file introduces graded hom spaces, `R`-linear graded quivers, and the grading data
needed to write down A-infinity structures.

The grading type `β` of an A-infinity category is an abelian group of degrees. The
A-infinity axioms only ever use two pieces of additional structure on it:

* integer *degree shifts* `ℤ →+ β`, so that the `n`-ary operation `mₙ` can have degree
  `2 - n`;
* a *Koszul sign character* `β →+ Additive ℤˣ`, so that a degree `d` determines a sign
  `(-1) ^ d`.

They are compatible in that the differential, of degree `shift 1`, is odd.

No degree is ever multiplied, so `β` is *not* required to be a ring. This is what allows
bigradings such as `ℤ × ℤ` or `ℤ × ZMod 2`, where `mₙ` has degree `(2 - n, 0)` and the
sign is the total parity.

A homomorphism of grading types `GradingHom β β'`, written `β →+ᵍ β'`, is an additive
homomorphism preserving the shifts and the signs. It translates degrees when an A-infinity functor changes the grading.
-/

namespace AInfinityTheory

universe u v w

variable (β : Type v)

/-- A grading type is an abelian group of degrees `β` together with a homomorphism
`shift : ℤ →+ β` realising integer degree shifts (the `n`-ary operation `mₙ` has degree
`shift (2 - n)`) and a Koszul sign character `sign : β →+ Additive ℤˣ`, such that the
differential, of degree `shift 1`, is odd. -/
public class GradingType (β : Type*) [AddCommGroup β] where
  /-- The integer degree shifts: `mₙ` has degree `shift (2 - n)`. -/
  shift : ℤ →+ β
  /-- The Koszul sign character, written additively. -/
  sign : β →+ Additive ℤˣ
  /-- The differential has odd degree. -/
  sign_shift_one : sign (shift 1) = Additive.ofMul (-1)

export GradingType (shift sign)

variable {β}

section GradingType

variable [AddCommGroup β] [GradingType β]

/-- The sign of an integer degree shift is Mathlib's `Int.negOnePow`. -/
@[simp]
public lemma sign_shift (n : ℤ) : sign (shift n : β) = Int.negOnePow n := by
  have shift_n : (shift n : β) = n • shift (1 : ℤ) := by
    rw [← map_zsmul, smul_eq_mul, mul_one]
  rw [shift_n, map_zsmul, GradingType.sign_shift_one, ← ofMul_zpow, Int.negOnePow_def]
  rfl

end GradingType

namespace GradingType

/-! ### Instances

Global instances are provided only for the two standard gradings `ℤ` and `ZMod 2`. Product
gradings are constructed by the named definitions `prodFst` and `prodTotal` below and must be
activated locally, since both are reasonable choices on the same product type. -/

/-- The integers, graded by themselves: the shift is the identity and the sign of `n` is
`(-1) ^ n`. -/
public instance : GradingType ℤ where
  shift := AddMonoidHom.id ℤ
  sign := zmultiplesHom (Additive ℤˣ) (Additive.ofMul (-1))
  sign_shift_one := by
    simp only [AddMonoidHom.id_apply, zmultiplesHom_apply, one_zsmul]

@[simp]
public lemma shift_int (n : ℤ) : shift n = n := rfl

/-- The parity grading `ZMod 2`: the shift is reduction modulo `2` and the sign of a parity
`p` is `(-1) ^ p`, using Mathlib's power operation on `ℤˣ` by `ZMod 2`. -/
public instance : GradingType (ZMod 2) where
  shift := Int.castAddHom (ZMod 2)
  sign := (smulAddHom (ZMod 2) (Additive ℤˣ)).flip (Additive.ofMul (-1))
  sign_shift_one := by
    simp only [Int.coe_castAddHom, Int.cast_one, AddMonoidHom.flip_apply, smulAddHom_apply,
      one_smul]

@[simp]
public lemma shift_zmod_two (n : ℤ) : shift n = (n : ZMod 2) := rfl

section Prod

variable (β : Type*) [AddCommGroup β] (γ : Type*) [AddCommGroup γ]

/-- The product grading on `β × γ` whose shifts land in the first factor and whose sign is
read off the first factor alone. -/
public abbrev prodFst [GradingType β] : GradingType (β × γ) where
  shift := (AddMonoidHom.inl β γ).comp shift
  sign := sign.comp (AddMonoidHom.fst β γ)
  sign_shift_one := by
    simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_fst, Function.comp_apply,
      AddMonoidHom.inl_apply, sign_shift_one]

@[simp]
public lemma prodFst_shift [GradingType β] (n : ℤ) :
    (prodFst β γ).shift n = (shift n, 0) := rfl

/-- The product grading on `β × γ` whose shifts land in the first factor and whose sign is
the product of the signs of both factors (the *total* sign). -/
public abbrev prodTotal [GradingType β] [GradingType γ] : GradingType (β × γ) where
  shift := (AddMonoidHom.inl β γ).comp shift
  sign := AddMonoidHom.coprod sign sign
  sign_shift_one := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.inl_apply,
      AddMonoidHom.coprod_apply, sign_shift_one, map_zero, add_zero]

@[simp]
public lemma prodTotal_shift [GradingType β] [GradingType γ] (n : ℤ) :
    (prodTotal β γ).shift n = (shift n, 0) := rfl

end Prod

end GradingType

/-! ### Koszul signs in the standard gradings -/

@[simp]
public lemma sign_int (n : ℤ) : sign n = Int.negOnePow n := rfl

/-- In the parity grading, `sign` is Mathlib's power operation on `ℤˣ` by `ZMod 2`. -/
public lemma sign_zmod_two (p : ZMod 2) : sign p = (-1 : ℤˣ) ^ p := rfl

section Prod

variable (β : Type*) [AddCommGroup β] (γ : Type*) [AddCommGroup γ]

@[simp]
public lemma sign_prodFst [GradingType β] (d : β × γ) :
    @sign (β × γ) _ (GradingType.prodFst β γ) d = sign d.1 := rfl

@[simp]
public lemma sign_prodTotal [GradingType β] [GradingType γ] (d : β × γ) :
    @sign (β × γ) _ (GradingType.prodTotal β γ) d = sign d.1 + sign d.2 := rfl

end Prod

/-! ### Homomorphisms of grading types -/

/-- A homomorphism of grading types is an additive homomorphism `β →+ β'` that preserves the
integer degree shifts and the Koszul signs. It translates degrees in `β` into degrees in `β'`
so that `mₙ` keeps degree `shift (2 - n)` and every Koszul sign is unchanged; for example,
reduction `ℤ → ZMod 2`, or the inclusion of `β` into the product grading `prodFst β γ`. -/
public structure GradingHom (β β' : Type*) [AddCommGroup β] [GradingType β]
    [AddCommGroup β'] [GradingType β'] extends β →+ β' where
  /-- The homomorphism preserves the integer degree shifts. -/
  map_shift' (k : ℤ) : toFun (shift k) = shift k
  /-- The homomorphism preserves the Koszul signs. -/
  map_sign' (b : β) : sign (toFun b) = sign b

/-- `β →+ᵍ β'` denotes the type of homomorphisms of grading types from `β` to `β'`. -/
infixr:25 " →+ᵍ " => GradingHom

namespace GradingHom

variable {β β' β'' : Type*} [AddCommGroup β] [GradingType β] [AddCommGroup β']
  [GradingType β'] [AddCommGroup β''] [GradingType β'']

/-- A homomorphism of grading types is applied to degrees through its underlying function. -/
@[expose]
public instance : FunLike (β →+ᵍ β') β β' where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective' h

/-- A homomorphism of grading types is in particular an additive homomorphism. -/
public instance : AddMonoidHomClass (β →+ᵍ β') β β' where
  map_add f := f.map_add'
  map_zero f := f.map_zero'

@[simp]
public lemma coe_toAddMonoidHom (f : β →+ᵍ β') : ⇑f.toAddMonoidHom = ⇑f := rfl

@[simp]
public lemma coe_mk (f : β →+ β') (h₁ h₂) : ⇑(⟨f, h₁, h₂⟩ : β →+ᵍ β') = ⇑f := rfl

/-- Two homomorphisms of grading types are equal if they agree on every degree. -/
@[ext]
public lemma ext {f g : β →+ᵍ β'} (h : ∀ b, f b = g b) : f = g :=
  DFunLike.ext f g h

/-- A homomorphism of grading types preserves the integer degree shifts. -/
@[simp]
public lemma map_shift (f : β →+ᵍ β') (k : ℤ) : f (shift k) = shift k :=
  f.map_shift' k

/-- A homomorphism of grading types preserves the Koszul signs. -/
@[simp]
public lemma map_sign (f : β →+ᵍ β') (b : β) : sign (f b) = sign b :=
  f.map_sign' b

variable (β) in
/-- The identity homomorphism of a grading type. -/
@[expose]
public def id : β →+ᵍ β where
  toAddMonoidHom := AddMonoidHom.id β
  map_shift' _ := rfl
  map_sign' _ := rfl

@[simp]
public lemma id_apply (b : β) : GradingHom.id β b = b := rfl

/-- The composite of two homomorphisms of grading types. -/
@[expose]
public def comp (g : β' →+ᵍ β'') (f : β →+ᵍ β') : β →+ᵍ β'' where
  toAddMonoidHom := g.toAddMonoidHom.comp f.toAddMonoidHom
  map_shift' k := (congrArg g (f.map_shift k)).trans (g.map_shift k)
  map_sign' b := (g.map_sign (f b)).trans (f.map_sign b)

@[simp]
public lemma comp_apply (g : β' →+ᵍ β'') (f : β →+ᵍ β') (b : β) :
    g.comp f b = g (f b) := rfl

end GradingHom

end AInfinityTheory
