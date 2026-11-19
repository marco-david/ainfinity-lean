/-
Copyright (c) 2026 Hallvard Hareide. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hallvard Hareide
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!
# Root and weight lattices

Coordinate vectors for the root lattice and the weight lattice of the simply-laced Lie algebra
whose Dynkin diagram is `Γ`, written in the basis of simple roots `αᵢ` or of fundamental weights
`ωᵢ`.

## Main definitions

* `SimpleGraph.cartanMatrix`: the Cartan matrix `2I - A` of a simply-laced graph.
* `KLRW.Coords k Γ R`: coordinate vectors for `Γ` with coefficients in `R`, in the basis selected
  by `k : KLRW.CoordKind`.
* `KLRW.RootCoords`, `KLRW.WeightCoords`, `KLRW.DominantWeight`: the root lattice, the weight
  lattice and the dominant integral weights.
* `KLRW.Coords.toWeight`: the Dynkin labels `Cβ` of an element `β` of the root lattice.

## Implementation notes

`Coords k Γ R` is a structure wrapping a function `V → R`, so that vectors in different bases
cannot be confused. It coerces to `V → R` through `FunLike`, so the `i`-th coefficient of `x` is
written `x i`. Its additive structure is transferred from `V → R` along `Coords.equiv`.
-/

@[expose] public section

namespace KLRW

/-- Which basis a coordinate vector is written in. -/
inductive CoordKind
  /-- The simple roots `αᵢ`. -/
  | root
  /-- The fundamental weights `ωᵢ`. -/
  | weight

section Lattices
variable {V : Type*}

/-- The Cartan matrix `2I - A` of a simply-laced graph. -/
def _root_.SimpleGraph.cartanMatrix [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix V V ℤ :=
  2 - G.adjMatrix ℤ

/-- Coordinate vectors for `Γ` in the basis selected by `k`. -/
structure Coords (k : CoordKind) (Γ : SimpleGraph V) (R : Type*) where
  /-- The coefficient of the `i`-th basis vector. -/
  coeff : V → R

/-- `RootCoords Γ ℤ` is the root lattice `Q`; `RootCoords Γ ℕ` is `Q⁺`. -/
abbrev RootCoords (Γ : SimpleGraph V) (R : Type*) := Coords .root Γ R
/-- `WeightCoords Γ ℤ` is the weight lattice `P`; `WeightCoords Γ ℕ` is `P⁺`. -/
abbrev WeightCoords (Γ : SimpleGraph V) (R : Type*) := Coords .weight Γ R
/-- Dominant integral weights of `Γ`. -/
abbrev DominantWeight (Γ : SimpleGraph V) := WeightCoords Γ ℕ

namespace Coords
variable {k : CoordKind} {Γ : SimpleGraph V} {R : Type*}

/-- A coordinate vector coerces to the function sending `i` to its `i`-th coefficient. -/
instance : FunLike (Coords k Γ R) V R where
  coe := coeff
  coe_injective := fun ⟨_⟩ ⟨_⟩ h => congrArg mk h

@[ext] theorem ext {x y : Coords k Γ R} (h : ∀ i, x i = y i) : x = y :=
  DFunLike.ext _ _ h

@[simp] theorem coeff_eq_coe (x : Coords k Γ R) : x.coeff = ⇑x := rfl
@[simp] theorem coe_mk (f : V → R) : ⇑(mk f : Coords k Γ R) = f := rfl

/-- Forget the basis. -/
def equiv : Coords k Γ R ≃ (V → R) := ⟨coeff, mk, fun _ => rfl, fun _ => rfl⟩

instance [AddCommMonoid R] : AddCommMonoid (Coords k Γ R) := Equiv.addCommMonoid equiv
instance [AddCommGroup R] : AddCommGroup (Coords k Γ R) := Equiv.addCommGroup equiv
instance [Fintype V] [DecidableEq R] : DecidableEq (Coords k Γ R) :=
  equiv.injective.decidableEq

@[simp] theorem add_apply [AddCommMonoid R] (x y : Coords k Γ R) (i : V) :
    (x + y) i = x i + y i := rfl

/-- A vector with natural number coefficients, viewed as one with integer coefficients. -/
def toInt (x : Coords k Γ ℕ) : Coords k Γ ℤ := ⟨fun i => x i⟩

/-- Dynkin labels of an element of the root lattice: `β ↦ Cβ`. -/
def toWeight [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (β : RootCoords Γ ℤ) : WeightCoords Γ ℤ :=
  ⟨Γ.cartanMatrix.mulVec β⟩

end Coords
end Lattices

end KLRW
