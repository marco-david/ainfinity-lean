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

Coordinate vectors for the root lattice and the weight lattice of the simply-laced Kac–Moody
algebra whose Dynkin diagram is `Γ`, written in the basis of simple roots `αᵢ` or of fundamental
weights `ωᵢ`.

## Main definitions

* `SimpleGraph.cartanMatrix`: the Cartan matrix `2I - A` of a simply-laced graph.
* `KLRW.Coords k Γ R`: coordinate vectors for `Γ` with coefficients in `R`, in the basis selected
  by `k : KLRW.CoordKind`.
* `KLRW.RootCoords`, `KLRW.WeightCoords`, `KLRW.DominantWeight`: the root lattice, the weight
  lattice and the dominant integral weights.
* `KLRW.Coords.map`: apply a function to every coefficient, e.g. inclusion from `ℕ` to `ℤ`.
* `KLRW.Coords.toWeight`: the additive map sending an element `β` of the root lattice to its
  Dynkin labels `Cβ`.
* `KLRW.simpleRoot Γ i`, `KLRW.fundWeight Γ i`: the simple root `αᵢ` and the fundamental weight
  `ωᵢ`, the `i`-th basis vectors of the root and the weight lattice.

## Main results

* `KLRW.simpleRoot_injective`, `KLRW.fundWeight_injective`: distinct vertices give distinct
  basis vectors.
* `KLRW.coe_toWeight_simpleRoot`: the Dynkin labels of `αᵢ` are the `i`-th column of the Cartan
  matrix, i.e. `αᵢ = 2ωᵢ - Σ_{j ∼ i} ωⱼ`.

## Implementation notes

* `Coords k Γ R` is a structure wrapping a function `V → R`, so that vectors in different bases
  cannot be confused. It coerces to `V → R` through `FunLike`, so the `i`-th coefficient of `x`
  is written `x i`. Its additive structure is transferred from `V → R` along `Coords.equiv`.
* Simple roots and fundamental weights are indexed by the vertices `i : V` themselves, as
  Mathlib's `RootPairing.root : ι ↪ M` indexes roots by a plain type. The index type is not
  wrapped: `simpleRoot Γ i` and `fundWeight Γ i` already live in different types, and the KLRW
  relations need `Γ.Adj i j` on the indices.
* As for `Finsupp`, the `coe_*` lemmas such as `coe_add : ⇑(x + y) = ⇑x + ⇑y` are simp lemmas, so
  proofs never need to unfold how the instances are built. The `*_apply` lemmas for a single
  coefficient are not simp lemmas, since simp derives them from the `coe_*` lemmas; they are
  there for `rw`.
* A weight `λ` is recorded by its Dynkin labels `⟨αᵢ^∨, λ⟩`, i.e. its coordinates in the basis of
  fundamental weights. When the Cartan matrix `C` is invertible (all diagrams of type A, D and E,
  and some indefinite ones such as `E₁₀`), `WeightCoords Γ ℤ` is the weight lattice `P` and
  `toWeight` is injective. When `C` is singular (for instance for the affine trees `D̃ₙ`, `Ẽ₆`,
  `Ẽ₇`, `Ẽ₈`), Kac's realisation gives weights `n - rank C` further coordinates, which the Dynkin
  labels forget, and `toWeight` kills the null roots: for `D̃₄`, `δ = 2α_centre + Σ α_leaf` has
  `Cδ = 0`.
* `C` is symmetric, so Kac's convention `aᵢⱼ = ⟨αᵢ^∨, αⱼ⟩` and the transposed convention of
  Bourbaki and Mathlib give the same `toWeight`.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Cambridge University Press, 1990,
  Chapter 1.
* N. Bourbaki, *Lie groups and Lie algebras, Chapters 4–6*, Springer, 2002, Chapter VI, §1.
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

/-- The entries of the Cartan matrix: `2` on the diagonal, `-1` between adjacent vertices and `0`
between distinct non-adjacent vertices. -/
lemma _root_.SimpleGraph.cartanMatrix_apply [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (i j : V) :
    G.cartanMatrix i j = if i = j then 2 else if G.Adj i j then -1 else 0 := by
  by_cases h : i = j <;> by_cases hA : G.Adj i j <;>
    simp_all [SimpleGraph.cartanMatrix, Matrix.ofNat_apply]

/-- Coordinate vectors for `Γ` in the basis selected by `k`. -/
structure Coords (k : CoordKind) (Γ : SimpleGraph V) (R : Type*) where
  /-- The coefficient of the `i`-th basis vector. -/
  coeff : V → R

/-- `RootCoords Γ ℤ` is the root lattice `Q`; `RootCoords Γ ℕ` is `Q⁺`. -/
abbrev RootCoords (Γ : SimpleGraph V) (R : Type*) := Coords .root Γ R
/-- `WeightCoords Γ ℤ` is the weight lattice `P`, recorded by Dynkin labels (see the module
docstring when the Cartan matrix is singular); `WeightCoords Γ ℕ` is `P⁺`. -/
abbrev WeightCoords (Γ : SimpleGraph V) (R : Type*) := Coords .weight Γ R
/-- Dominant integral weights of `Γ`. -/
abbrev DominantWeight (Γ : SimpleGraph V) := WeightCoords Γ ℕ

namespace Coords
variable {k : CoordKind} {Γ : SimpleGraph V} {R : Type*}

/-- A coordinate vector coerces to the function sending `i` to its `i`-th coefficient. -/
instance : FunLike (Coords k Γ R) V R where
  coe := coeff
  coe_injective := fun ⟨_⟩ ⟨_⟩ h => congrArg mk h

@[ext] lemma ext {x y : Coords k Γ R} (h : ∀ i, x i = y i) : x = y :=
  DFunLike.ext _ _ h

@[simp] lemma coeff_eq_coe (x : Coords k Γ R) : x.coeff = ⇑x := rfl
@[simp] lemma coe_mk (f : V → R) : ⇑(mk f : Coords k Γ R) = f := rfl

/-- The bijection between coordinate vectors and their coefficient functions `V → R`, which
forgets the basis. The additive structure of `Coords k Γ R` is transferred from `V → R` along
it. -/
def equiv : Coords k Γ R ≃ (V → R) := ⟨coeff, mk, fun _ => rfl, fun _ => rfl⟩

instance [AddCommMonoid R] : AddCommMonoid (Coords k Γ R) := Equiv.addCommMonoid equiv
instance [AddCommGroup R] : AddCommGroup (Coords k Γ R) := Equiv.addCommGroup equiv
instance [Fintype V] [DecidableEq R] : DecidableEq (Coords k Γ R) :=
  equiv.injective.decidableEq

/-! ### Coefficients of sums, differences and multiples

Each fact comes in two forms: `coe_add` for the coercion on its own, as in
`Γ.cartanMatrix.mulVec ⇑(x + y)`, and `add_apply` for a single coefficient. Only the `coe_*`
forms are simp lemmas; simp derives the `*_apply` forms from them. -/

section Arithmetic

variable [AddCommMonoid R]

@[simp, norm_cast] lemma coe_zero : ⇑(0 : Coords k Γ R) = 0 := rfl
lemma zero_apply (i : V) : (0 : Coords k Γ R) i = 0 := rfl

@[simp, norm_cast] lemma coe_add (x y : Coords k Γ R) : ⇑(x + y) = ⇑x + ⇑y := rfl
lemma add_apply (x y : Coords k Γ R) (i : V) : (x + y) i = x i + y i := rfl

@[simp, norm_cast] lemma coe_nsmul (n : ℕ) (x : Coords k Γ R) : ⇑(n • x) = n • ⇑x := rfl
lemma nsmul_apply (n : ℕ) (x : Coords k Γ R) (i : V) : (n • x) i = n • x i := rfl

@[simp, norm_cast] lemma coe_sum {ι : Type*} (s : Finset ι) (f : ι → Coords k Γ R) :
    ⇑(∑ j ∈ s, f j) = ∑ j ∈ s, ⇑(f j) :=
  map_sum (equiv.addEquiv : Coords k Γ R ≃+ (V → R)) f s

lemma sum_apply {ι : Type*} (s : Finset ι) (f : ι → Coords k Γ R) (i : V) :
    (∑ j ∈ s, f j) i = ∑ j ∈ s, f j i :=
  (congrFun (coe_sum s f) i).trans (Finset.sum_apply i s _)

end Arithmetic

section ArithmeticGroup

variable [AddCommGroup R]

@[simp, norm_cast] lemma coe_neg (x : Coords k Γ R) : ⇑(-x) = -⇑x := rfl
lemma neg_apply (x : Coords k Γ R) (i : V) : (-x) i = -x i := rfl

@[simp, norm_cast] lemma coe_sub (x y : Coords k Γ R) : ⇑(x - y) = ⇑x - ⇑y := rfl
lemma sub_apply (x y : Coords k Γ R) (i : V) : (x - y) i = x i - y i := rfl

@[simp, norm_cast] lemma coe_zsmul (n : ℤ) (x : Coords k Γ R) : ⇑(n • x) = n • ⇑x := rfl
lemma zsmul_apply (n : ℤ) (x : Coords k Γ R) (i : V) : (n • x) i = n • x i := rfl

end ArithmeticGroup

/-! ### Changing the coefficients -/

section Map

variable {S T : Type*}

/-- Apply `f` to every coefficient, keeping the basis. For instance `x.map (↑)` views an element
`x` of `Q⁺` (resp. `P⁺`) as an element of the lattice `Q` (resp. `P`). -/
def map (f : R → S) (x : Coords k Γ R) : Coords k Γ S := ⟨fun i => f (x i)⟩

@[simp] lemma coe_map (f : R → S) (x : Coords k Γ R) : ⇑(x.map f) = f ∘ ⇑x := rfl
lemma map_apply (f : R → S) (x : Coords k Γ R) (i : V) : x.map f i = f (x i) := rfl

@[simp] lemma map_id (x : Coords k Γ R) : x.map id = x := rfl

@[simp] lemma map_map (f : R → S) (g : S → T) (x : Coords k Γ R) :
    (x.map f).map g = x.map (g ∘ f) := rfl

/-- Applying a map preserving zero to the coefficients of zero gives zero. -/
protected lemma map_zero [AddCommMonoid R] [AddCommMonoid S] {f : R → S} (hf : f 0 = 0) :
    (0 : Coords k Γ R).map f = 0 :=
  ext fun _ => by simp [hf]

/-- Applying an additive map to the coefficients commutes with addition. -/
protected lemma map_add [AddCommMonoid R] [AddCommMonoid S] {f : R → S}
    (hf : ∀ a b, f (a + b) = f a + f b) (x y : Coords k Γ R) :
    (x + y).map f = x.map f + y.map f :=
  ext fun i => by simp [hf]

end Map

/-! ### From roots to weights -/

section ToWeight

variable [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]

/-- The Dynkin labels of an element `β` of the root lattice, i.e. `β` in the basis of fundamental
weights: `β ↦ Cβ`, where `C` is the Cartan matrix of `Γ`. It is injective exactly when `C` is
invertible. -/
def toWeight : RootCoords Γ ℤ →+ WeightCoords Γ ℤ :=
  AddMonoidHom.mk' (fun β => ⟨Γ.cartanMatrix.mulVec β⟩)
    fun _ _ => ext fun _ => by simp [Matrix.mulVec_add]

@[simp] lemma coe_toWeight (β : RootCoords Γ ℤ) :
    ⇑(toWeight β) = Γ.cartanMatrix.mulVec ⇑β := rfl

lemma toWeight_apply (β : RootCoords Γ ℤ) (i : V) :
    toWeight β i = Γ.cartanMatrix.mulVec (⇑β) i := rfl

end ToWeight

end Coords

/-! ### Simple roots and fundamental weights -/

section Basis

variable (Γ : SimpleGraph V) {R : Type*} [DecidableEq V] [Zero R] [One R]

/-- The simple root `αᵢ`: the `i`-th basis vector of the root lattice, with coefficient `1` at `i`
and `0` elsewhere. Over `ℕ` it is an element of `Q⁺`, over `ℤ` of `Q`. -/
def simpleRoot (i : V) : RootCoords Γ R := ⟨Pi.single i 1⟩

/-- The fundamental weight `ωᵢ`: the weight with Dynkin labels `1` at `i` and `0` elsewhere.
Over `ℕ` it is a dominant weight. -/
def fundWeight (i : V) : WeightCoords Γ R := ⟨Pi.single i 1⟩

@[simp] lemma coe_simpleRoot (i : V) : ⇑(simpleRoot Γ i : RootCoords Γ R) = Pi.single i 1 := rfl
lemma simpleRoot_apply (i j : V) :
    (simpleRoot Γ i : RootCoords Γ R) j = Pi.single (M := fun _ => R) i 1 j := rfl

@[simp] lemma coe_fundWeight (i : V) : ⇑(fundWeight Γ i : WeightCoords Γ R) = Pi.single i 1 :=
  rfl
lemma fundWeight_apply (i j : V) :
    (fundWeight Γ i : WeightCoords Γ R) j = Pi.single (M := fun _ => R) i 1 j := rfl

variable [NeZero (1 : R)]

/-- Distinct vertices give distinct simple roots, provided `1 ≠ 0` in `R`. -/
lemma simpleRoot_injective : Function.Injective (simpleRoot Γ : V → RootCoords Γ R) :=
  fun i j h => by simpa [Pi.single_apply, eq_comm] using DFunLike.congr_fun h i

/-- Distinct vertices give distinct fundamental weights, provided `1 ≠ 0` in `R`. -/
lemma fundWeight_injective : Function.Injective (fundWeight Γ : V → WeightCoords Γ R) :=
  fun i j h => by simpa [Pi.single_apply, eq_comm] using DFunLike.congr_fun h i

end Basis

/-- The Dynkin labels of the simple root `αᵢ` are the `i`-th column of the Cartan matrix, that is
`αᵢ = 2ωᵢ - Σ_{j ∼ i} ωⱼ` (see `SimpleGraph.cartanMatrix_apply`). In particular `αᵢ` is not
dominant as soon as `i` has a neighbour. -/
@[simp] lemma coe_toWeight_simpleRoot [Fintype V] [DecidableEq V] (Γ : SimpleGraph V)
    [DecidableRel Γ.Adj] (i : V) :
    ⇑(Coords.toWeight (simpleRoot Γ i)) = Γ.cartanMatrix.col i :=
  Matrix.mulVec_single_one _ _

end Lattices

end KLRW
