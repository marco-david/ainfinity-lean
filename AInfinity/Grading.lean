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

This file introduces the grading data needed to write down A-infinity structures.

The grading type `β` of an A-infinity category is an abelian group of degrees. The
A-infinity axioms only ever use two pieces of additional structure on it:

* integer *degree shifts* `ℤ →+ β`, so that the `n`-ary operation `mₙ` can have degree
  `2 - n`;
* a *Koszul sign character* `β →+ Additive ℤˣ`, so that a degree `d` determines a sign
  `(-1) ^ d`.

They are compatible in that the differential, of degree `shift 1`, is odd.

No degree is ever multiplied, so `β` is *not* required to be a ring. This is what allows
bigradings such as `ℤ ×ᵗ ℤ` or `ℤ ×ᵗ ZMod 2`, where `mₙ` has degree `(2 - n, 0)` and the
sign is the total parity, or `β ×ˡ γ` and `β ×ʳ γ`, where the shifts and the sign live in the
first, respectively second, factor alone. These are type synonyms for `β × γ`.

A homomorphism of grading types `GradingHom β β'`, written `β →+ᵍ β'`, is an additive
homomorphism preserving the shifts and the signs. It translates degrees when an A-infinity
functor changes the grading. Homomorphisms of grading types compose, with the identity as unit.
The integers are the initial grading type: `GradingHom.ofInt β : ℤ →+ᵍ β` is the shift. The
inclusion `inl` of the first factor into `β ×ᵗ γ` or `β ×ˡ γ`, the projection `fst` out of
`β ×ˡ γ`, and their mirror images `inr` and `snd` for `β ×ʳ γ`, are homomorphisms of grading
types.
-/

namespace AInfinityTheory

universe u v w

variable (β : Type v)

/-- A grading type is an abelian group of degrees `β` together with a homomorphism
`shift : ℤ →+ β` realising integer degree shifts (the `n`-ary operation `mₙ` has degree
`shift (2 - n)`) and a Koszul sign character `sign : β →+ Additive ℤˣ`, such that the
differential, of degree `shift 1`, is odd. -/
public class Grading (β : Type*) [AddCommGroup β] where
  /-- The integer degree shifts: `mₙ` has degree `shift (2 - n)`. -/
  shift : ℤ →+ β
  /-- The Koszul sign character, written additively. -/
  sign : β →+ Additive ℤˣ
  /-- The differential has odd degree. -/
  sign_shift_one : sign (shift 1) = Additive.ofMul (-1)

export Grading (shift sign)

variable {β}

section Grading

variable [AddCommGroup β] [Grading β]

/-- The sign of an integer degree shift is Mathlib's `Int.negOnePow`. -/
@[simp]
public lemma sign_shift (n : ℤ) : sign (shift n : β) = Int.negOnePow n := by
  have shift_n : (shift n : β) = n • shift (1 : ℤ) := by
    rw [← map_zsmul, smul_eq_mul, mul_one]
  rw [shift_n, map_zsmul, Grading.sign_shift_one, ← ofMul_zpow, Int.negOnePow_def]
  rfl

end Grading

namespace Grading

/-! ### Instances

Global instances are provided for the two standard gradings `ℤ` and `ZMod 2`, and below for the
product gradings `β ×ᵗ γ`, `β ×ˡ γ` and `β ×ʳ γ`. -/

/-- The integers, graded by themselves: the shift is the identity and the sign of `n` is
`(-1) ^ n`. -/
public instance : Grading ℤ where
  shift := AddMonoidHom.id ℤ
  sign := zmultiplesHom (Additive ℤˣ) (Additive.ofMul (-1))
  sign_shift_one := by
    simp only [AddMonoidHom.id_apply, zmultiplesHom_apply, one_zsmul]

@[simp]
public lemma shift_int (n : ℤ) : shift n = n := rfl

/-- The parity grading `ZMod 2`: the shift is reduction modulo `2` and the sign of a parity
`p` is `(-1) ^ p`, using Mathlib's power operation on `ℤˣ` by `ZMod 2`. -/
public instance : Grading (ZMod 2) where
  shift := Int.castAddHom (ZMod 2)
  sign := (smulAddHom (ZMod 2) (Additive ℤˣ)).flip (Additive.ofMul (-1))
  sign_shift_one := by
    simp only [Int.coe_castAddHom, Int.cast_one, AddMonoidHom.flip_apply, smulAddHom_apply,
      one_smul]

@[simp]
public lemma shift_zmod_two (n : ℤ) : shift n = (n : ZMod 2) := rfl

end Grading

/-! ### Product gradings

The product of two grading types, seen as abelian groups, carries three natural gradings: `β ×ᵗ γ`,
with shifts in the first factor and the total sign, `β ×ˡ γ`, with shifts and sign in the first
factor alone, and `β ×ʳ γ`, with shifts and sign in the second factor alone. Each is a type synonym
for `β × γ`. -/

section Prod

variable (β γ : Type*)

/-- The total product. A type synonym for `β × γ`, carrying the product grading whose shifts land in
the first factor and whose sign is the product of the signs of both factors. -/
@[expose]
public def TProd := β × γ

/-- The left product. A type synonym for `β × γ`, carrying the product grading whose shifts land in
the first factor and whose sign is read off the first factor alone. -/
@[expose]
public def LProd := β × γ

/-- The right product. A type synonym for `β × γ`, carrying the product grading whose shifts land in
the second factor and whose sign is read off the second factor alone. -/
@[expose]
public def RProd := β × γ

@[inherit_doc] infixr:35 " ×ᵗ " => TProd

@[inherit_doc] infixr:35 " ×ˡ " => LProd

@[inherit_doc] infixr:35 " ×ʳ " => RProd

variable {β γ} [AddCommGroup β] [AddCommGroup γ]

@[expose]
public instance : AddCommGroup (β ×ᵗ γ) := inferInstanceAs (AddCommGroup (β × γ))

@[expose]
public instance : AddCommGroup (β ×ˡ γ) := inferInstanceAs (AddCommGroup (β × γ))

@[expose]
public instance : AddCommGroup (β ×ʳ γ) := inferInstanceAs (AddCommGroup (β × γ))

/-- `toTProd` is the identity, viewed as an equivalence from `β × γ` to `β ×ᵗ γ`. -/
@[expose]
public def toTProd : β × γ ≃+ β ×ᵗ γ := AddEquiv.refl _

/-- `ofTProd` is the identity, viewed as an equivalence from `β ×ᵗ γ` to `β × γ`. -/
@[expose]
public def ofTProd : β ×ᵗ γ ≃+ β × γ := AddEquiv.refl _

/-- `toLProd` is the identity, viewed as an equivalence from `β × γ` to `β ×ˡ γ`. -/
@[expose]
public def toLProd : β × γ ≃+ β ×ˡ γ := AddEquiv.refl _

/-- `ofLProd` is the identity, viewed as an equivalence from `β ×ˡ γ` to `β × γ`. -/
@[expose]
public def ofLProd : β ×ˡ γ ≃+ β × γ := AddEquiv.refl _

/-- `toRProd` is the identity, viewed as an equivalence from `β × γ` to `β ×ʳ γ`. -/
@[expose]
public def toRProd : β × γ ≃+ β ×ʳ γ := AddEquiv.refl _

/-- `ofRProd` is the identity, viewed as an equivalence from `β ×ʳ γ` to `β × γ`. -/
@[expose]
public def ofRProd : β ×ʳ γ ≃+ β × γ := AddEquiv.refl _

@[simp]
public lemma toTProd_symm_eq : (toTProd : β × γ ≃+ β ×ᵗ γ).symm = ofTProd := rfl

@[simp]
public lemma ofTProd_symm_eq : (ofTProd : β ×ᵗ γ ≃+ β × γ).symm = toTProd := rfl

@[simp]
public lemma toTProd_ofTProd (d : β ×ᵗ γ) : toTProd (ofTProd d) = d := rfl

@[simp]
public lemma ofTProd_toTProd (d : β × γ) : ofTProd (toTProd d) = d := rfl

@[simp]
public lemma toLProd_symm_eq : (toLProd : β × γ ≃+ β ×ˡ γ).symm = ofLProd := rfl

@[simp]
public lemma ofLProd_symm_eq : (ofLProd : β ×ˡ γ ≃+ β × γ).symm = toLProd := rfl

@[simp]
public lemma toLProd_ofLProd (d : β ×ˡ γ) : toLProd (ofLProd d) = d := rfl

@[simp]
public lemma ofLProd_toLProd (d : β × γ) : ofLProd (toLProd d) = d := rfl

@[simp]
public lemma toRProd_symm_eq : (toRProd : β × γ ≃+ β ×ʳ γ).symm = ofRProd := rfl

@[simp]
public lemma ofRProd_symm_eq : (ofRProd : β ×ʳ γ ≃+ β × γ).symm = toRProd := rfl

@[simp]
public lemma toRProd_ofRProd (d : β ×ʳ γ) : toRProd (ofRProd d) = d := rfl

@[simp]
public lemma ofRProd_toRProd (d : β × γ) : ofRProd (toRProd d) = d := rfl

/-- The right product grading: shifts land in the second factor and the sign of `(b, c)`
is the sign of `c`. -/
public instance [Grading γ] : Grading (β ×ʳ γ) where
  shift := toRProd.toAddMonoidHom.comp ((AddMonoidHom.inr β γ).comp shift)
  sign := sign.comp ((AddMonoidHom.snd β γ).comp ofRProd.toAddMonoidHom)
  sign_shift_one := by
    change sign (shift 1 : γ) = _
    exact Grading.sign_shift_one

@[simp]
public lemma shift_rProd [Grading γ] (n : ℤ) : (shift n : β ×ʳ γ) = toRProd (0, shift n) := rfl

@[simp]
public lemma sign_rProd [Grading γ] (d : β ×ʳ γ) : sign d = sign (ofRProd d).2 := rfl

variable [Grading β]

/-- The total product grading: shifts land in the first factor and the sign of `(b, c)` is the
product of the signs of `b` and `c`. -/
public instance [Grading γ] : Grading (β ×ᵗ γ) where
  shift := toTProd.toAddMonoidHom.comp ((AddMonoidHom.inl β γ).comp shift)
  sign := (AddMonoidHom.coprod sign sign).comp ofTProd.toAddMonoidHom
  sign_shift_one := by
    change sign (shift 1 : β) + sign (0 : γ) = _
    rw [map_zero, add_zero, Grading.sign_shift_one]

/-- The left product grading: shifts land in the first factor and the sign of `(b, c)`
is the sign of `b`. -/
public instance : Grading (β ×ˡ γ) where
  shift := toLProd.toAddMonoidHom.comp ((AddMonoidHom.inl β γ).comp shift)
  sign := sign.comp ((AddMonoidHom.fst β γ).comp ofLProd.toAddMonoidHom)
  sign_shift_one := by
    change sign (shift 1 : β) = _
    exact Grading.sign_shift_one

@[simp]
public lemma shift_tProd [Grading γ] (n : ℤ) :
    (shift n : β ×ᵗ γ) = toTProd (shift n, 0) := rfl

@[simp]
public lemma shift_lProd (n : ℤ) : (shift n : β ×ˡ γ) = toLProd (shift n, 0) := rfl

@[simp]
public lemma sign_tProd [Grading γ] (d : β ×ᵗ γ) :
    sign d = sign (ofTProd d).1 + sign (ofTProd d).2 := rfl

@[simp]
public lemma sign_lProd (d : β ×ˡ γ) : sign d = sign (ofLProd d).1 := rfl

end Prod

/-! ### Koszul signs in the standard gradings -/

@[simp]
public lemma sign_int (n : ℤ) : sign n = Int.negOnePow n := rfl

/-- In the parity grading, `sign` is Mathlib's power operation on `ℤˣ` by `ZMod 2`. -/
public lemma sign_zmod_two (p : ZMod 2) : sign p = (-1 : ℤˣ) ^ p := rfl

/-! ### Homomorphisms of grading types -/

/-- A homomorphism of grading types is an additive homomorphism `β →+ β'` that preserves the
integer degree shifts and the Koszul signs. -/
public structure GradingHom (β β' : Type*) [AddCommGroup β] [Grading β]
    [AddCommGroup β'] [Grading β'] extends β →+ β' where
  /-- The homomorphism preserves the integer degree shifts. -/
  map_shift' (k : ℤ) : toFun (shift k) = shift k
  /-- The homomorphism preserves the Koszul signs. -/
  map_sign' (b : β) : sign (toFun b) = sign b

/-- `β →+ᵍ β'` denotes the type of homomorphisms of grading types from `β` to `β'`. -/
infixr:25 " →+ᵍ " => GradingHom

namespace GradingHom

variable {β β' β'' β''' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β']
  [Grading β'] [AddCommGroup β''] [Grading β''] [AddCommGroup β'''] [Grading β''']

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

/-- A homomorphism of grading types is determined by its underlying additive homomorphism. -/
public lemma toAddMonoidHom_injective :
    Function.Injective (toAddMonoidHom : (β →+ᵍ β') → β →+ β') := by
  intro f g h
  ext b
  rw [← coe_toAddMonoidHom f, ← coe_toAddMonoidHom g, h]

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

public lemma coe_id : ⇑(GradingHom.id β) = _root_.id := rfl

/-- The composite of two homomorphisms of grading types. -/
@[expose]
public def comp (g : β' →+ᵍ β'') (f : β →+ᵍ β') : β →+ᵍ β'' where
  toAddMonoidHom := g.toAddMonoidHom.comp f.toAddMonoidHom
  map_shift' k := (congrArg g (f.map_shift k)).trans (g.map_shift k)
  map_sign' b := (g.map_sign (f b)).trans (f.map_sign b)

@[simp]
public lemma comp_apply (g : β' →+ᵍ β'') (f : β →+ᵍ β') (b : β) :
    g.comp f b = g (f b) := rfl

@[simp]
public lemma coe_comp (g : β' →+ᵍ β'') (f : β →+ᵍ β') : ⇑(g.comp f) = g ∘ f := rfl

/-- The identity is a right unit for composition of homomorphisms of grading types. -/
@[simp]
public lemma comp_id (f : β →+ᵍ β') : f.comp (GradingHom.id β) = f :=
  ext fun _ => rfl

/-- The identity is a left unit for composition of homomorphisms of grading types. -/
@[simp]
public lemma id_comp (f : β →+ᵍ β') : (GradingHom.id β').comp f = f :=
  ext fun _ => rfl

/-- Composition of homomorphisms of grading types is associative. -/
public lemma comp_assoc (h : β'' →+ᵍ β''') (g : β' →+ᵍ β'') (f : β →+ᵍ β') :
    (h.comp g).comp f = h.comp (g.comp f) :=
  ext fun _ => rfl

variable (β) in
/-- The integers are the initial grading type: the integer degree shift `shift : ℤ →+ β` is the
unique homomorphism of grading types from ℤ to β. -/
@[expose]
public def ofInt : ℤ →+ᵍ β where
  toAddMonoidHom := shift
  map_shift' _ := rfl
  map_sign' := sign_shift

@[simp]
public lemma ofInt_apply (n : ℤ) : ofInt β n = shift n := rfl

/-- The homomorphism of grading types `ℤ → ZMod 2` is reduction modulo `2`. -/
public lemma ofInt_zmod_two_apply (n : ℤ) : ofInt (ZMod 2) n = (n : ZMod 2) := rfl

/-- Every homomorphism of grading types out of `ℤ` is `ofInt`, since it preserves shifts. -/
public lemma eq_ofInt (f : ℤ →+ᵍ β) : f = ofInt β :=
  ext f.map_shift

/-- There is exactly one homomorphism of grading types out of `ℤ`. -/
public instance : Unique (ℤ →+ᵍ β) where
  default := ofInt β
  uniq := eq_ofInt

end GradingHom

/-! ### Inclusions and projections of product gradings

The inclusion `inl` of the first factor into `β ×ᵗ γ` or `β ×ˡ γ`, the projection `fst` out of
`β ×ˡ γ`, and their mirror images `inr` and `snd` for `β ×ʳ γ`, are homomorphisms of grading
types. -/

section Prod

variable (β : Type*) [AddCommGroup β] (γ : Type*) [AddCommGroup γ]

namespace TProd

variable [Grading β] [Grading γ]

/-- The inclusion `b ↦ (b, 0)` of `β` into the product grading `β ×ᵗ γ`. -/
@[expose]
public def inl : β →+ᵍ β ×ᵗ γ where
  toAddMonoidHom := toTProd.toAddMonoidHom.comp (AddMonoidHom.inl β γ)
  map_shift' _ := rfl
  map_sign' b := by
    change sign (toTProd (b, 0)) = sign b
    rw [sign_tProd, ofTProd_toTProd, map_zero, add_zero]

variable {β γ}

@[simp]
public lemma inl_apply (b : β) : inl β γ b = toTProd (b, 0) := rfl

end TProd

namespace LProd

variable [Grading β]

/-- The inclusion `b ↦ (b, 0)` of `β` into the product grading `β ×ˡ γ`. -/
@[expose]
public def inl : β →+ᵍ β ×ˡ γ where
  toAddMonoidHom := toLProd.toAddMonoidHom.comp (AddMonoidHom.inl β γ)
  map_shift' _ := rfl
  map_sign' _ := rfl

/-- The projection of the product grading `β ×ˡ γ` onto its first factor `β`. -/
@[expose]
public def fst : β ×ˡ γ →+ᵍ β where
  toAddMonoidHom := (AddMonoidHom.fst β γ).comp ofLProd.toAddMonoidHom
  map_shift' _ := rfl
  map_sign' _ := rfl

variable {β γ}

@[simp]
public lemma inl_apply (b : β) : inl β γ b = toLProd (b, 0) := rfl

@[simp]
public lemma fst_apply (d : β ×ˡ γ) : fst β γ d = (ofLProd d).1 := rfl

/-- The projection onto the first factor is a retraction of the inclusion. -/
@[simp]
public lemma fst_comp_inl : (fst β γ).comp (inl β γ) = GradingHom.id β :=
  GradingHom.ext fun _ => rfl

end LProd

namespace RProd

variable [Grading γ]

/-- The inclusion `c ↦ (0, c)` of `γ` into the product grading `β ×ʳ γ`. -/
@[expose]
public def inr : γ →+ᵍ β ×ʳ γ where
  toAddMonoidHom := toRProd.toAddMonoidHom.comp (AddMonoidHom.inr β γ)
  map_shift' _ := rfl
  map_sign' _ := rfl

/-- The projection of the product grading `β ×ʳ γ` onto its second factor `γ`. -/
@[expose]
public def snd : β ×ʳ γ →+ᵍ γ where
  toAddMonoidHom := (AddMonoidHom.snd β γ).comp ofRProd.toAddMonoidHom
  map_shift' _ := rfl
  map_sign' _ := rfl

variable {β γ}

@[simp]
public lemma inr_apply (c : γ) : inr β γ c = toRProd (0, c) := rfl

@[simp]
public lemma snd_apply (d : β ×ʳ γ) : snd β γ d = (ofRProd d).2 := rfl

/-- The projection onto the second factor is a retraction of the inclusion. -/
@[simp]
public lemma snd_comp_inr : (snd β γ).comp (inr β γ) = GradingHom.id γ :=
  GradingHom.ext fun _ => rfl

end RProd

end Prod

end AInfinityTheory
