/-
Copyright (c) 2026 Hallvard Hareide. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hallvard Hareide
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Root and weight lattices

Coordinate vectors for the root lattice and the weight lattice of the simply-laced Kac–Moody
algebra whose Dynkin diagram is `Γ`, written in the basis of simple roots `αᵢ` or of fundamental
weights `ωᵢ`.

## Main definitions

* `SimpleGraph.cartanMatrix`: the Cartan matrix `2I - A` of a simply-laced graph.
* `KLRW.Coords k Γ R`: coordinate vectors for `Γ` with coefficients in `R`, in the basis selected
  by `k : KLRW.CoordKind`. They form an `R`-module.
* `KLRW.RootCoords`, `KLRW.WeightCoords`, `KLRW.DominantWeight`: the root lattice, the weight
  lattice and the dominant integral weights.
* `KLRW.Coords.single i r`: the vector with coefficient `r` at `i` and `0` elsewhere.
* `KLRW.simpleRoot Γ i`, `KLRW.fundWeight Γ i`: the simple root `αᵢ` and the fundamental weight
  `ωᵢ`, i.e. `single i 1` in the root and in the weight lattice.
* `KLRW.Coords.basis k Γ R`: the basis `(single i 1)ᵢ`, i.e. the simple roots or the fundamental
  weights.
* `KLRW.Coords.map`: apply a function to every coefficient, e.g. inclusion from `ℕ` to `ℤ`.
* `KLRW.Coords.toWeight`: the linear map sending an element `β` of the root lattice to its
  Dynkin labels `Cβ`.

## Main results

* `KLRW.Coords.coe_basis`: the simple roots form a basis of the root lattice and the fundamental
  weights a basis of the weight lattice (over `ℕ`: of `Q⁺` and of `P⁺`).
* `KLRW.Coords.toMatrix_toWeight`: in these bases, the matrix of `toWeight` is the Cartan matrix.
* `KLRW.Coords.toWeight_simpleRoot`: `αᵢ = 2ωᵢ - Σ_{j ∼ i} ωⱼ`.
* `SimpleGraph.cartanMatrix_isSymm`: the Cartan matrix is symmetric.

## Implementation notes

* `Coords k Γ R` is a structure wrapping a function `V → R` and tagged by the basis `k`, so that
  coordinates in the basis of simple roots and in the basis of fundamental weights cannot be
  confused; they are compared through `toWeight`. As in Kac, both bases are indexed by the
  vertices of `Γ`. The `i`-th coefficient of `x` is written `x i`, and the additive and module
  structures are transferred from `V → R` along `Coords.equiv`.
* A weight `λ` is recorded by its Dynkin labels `⟨αᵢ^∨, λ⟩`, i.e. its coordinates in the basis of
  fundamental weights. When the Cartan matrix `C` is invertible (all diagrams of type A, D and E,
  and some indefinite ones such as `E₁₀`), `WeightCoords Γ ℤ` is the weight lattice `P` and
  `toWeight` is injective. When `C` is singular (for instance for the affine trees `D̃ₙ`, `Ẽ₆`,
  `Ẽ₇`, `Ẽ₈`), Kac's realisation gives weights `n - rank C` further coordinates, which the Dynkin
  labels forget, and `toWeight` kills the null roots: for `D̃₄`, `δ = 2α_centre + Σ α_leaf` has
  `Cδ = 0`.
* `C` is symmetric (`SimpleGraph.cartanMatrix_isSymm`), so Kac's convention
  `aᵢⱼ = ⟨αᵢ^∨, αⱼ⟩` and the transposed convention of Bourbaki and Mathlib give the same
  `toWeight`.
* `Coords.basis` is noncomputable, like every Mathlib basis. It is meant for statements and
  proofs; computations use `single`, `simpleRoot` and `fundWeight`, and `coe_basis` identifies
  the basis vectors with them.

## TODO
* Ordering on `RootCoords` and `WeightCoords`
* Dual weights with path from weight to its dual
* Height function
* Compatibility with mathlib's ADE Cartans
* Consider upstreaming to Mathlib


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

/-! ### The Cartan matrix -/

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

/-- The Cartan matrix of a simply-laced graph is symmetric. -/
lemma _root_.SimpleGraph.cartanMatrix_isSymm [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : G.cartanMatrix.IsSymm :=
  Matrix.IsSymm.ext fun i j => by simp only [G.cartanMatrix_apply, eq_comm, G.adj_comm]

/-! ### Coordinate vectors -/

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
forgets the basis. The additive and module structures of `Coords k Γ R` are transferred from
`V → R` along it. -/
def equiv : Coords k Γ R ≃ (V → R) := ⟨coeff, mk, fun _ => rfl, fun _ => rfl⟩

instance [AddCommMonoid R] : AddCommMonoid (Coords k Γ R) := Equiv.addCommMonoid equiv
instance [AddCommGroup R] : AddCommGroup (Coords k Γ R) := Equiv.addCommGroup equiv
/-- Coordinate vectors with coefficients in a semiring `R` form an `R`-module.

The additive equivalence is written out instead of using `equiv.addEquiv`, which is not
reducible, so that for `R = ℕ, ℤ` this module structure agrees with the multiples coming from the
additive structure. See note [reducible non-instances]. -/
instance [Semiring R] : Module R (Coords k Γ R) :=
  AddEquiv.module R { equiv with map_add' := fun _ _ => rfl }
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

section ArithmeticModule

variable [Semiring R]

@[simp, norm_cast] lemma coe_smul (r : R) (x : Coords k Γ R) : ⇑(r • x) = r • ⇑x := rfl
lemma smul_apply (r : R) (x : Coords k Γ R) (i : V) : (r • x) i = r • x i := rfl

end ArithmeticModule

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

/-- Applying an injective map to the coefficients is injective. For instance `map (↑)` embeds
`Q⁺` into `Q` and `P⁺` into `P`, by `map_injective Nat.cast_injective`. -/
lemma map_injective {f : R → S} (hf : Function.Injective f) :
    Function.Injective (map f : Coords k Γ R → Coords k Γ S) :=
  fun _ _ h => ext fun i => hf (DFunLike.congr_fun h i)

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

/-! ### Basis vectors -/

section Single

variable [DecidableEq V] [Zero R]

/-- The vector with coefficient `r` at `i` and `0` elsewhere. For `r = 1` it is the simple root
`αᵢ` (`simpleRoot`) or the fundamental weight `ωᵢ` (`fundWeight`). -/
def single (i : V) (r : R) : Coords k Γ R := ⟨Pi.single i r⟩

@[simp] lemma coe_single (i : V) (r : R) : ⇑(single i r : Coords k Γ R) = Pi.single i r := rfl
lemma single_apply (i : V) (r : R) (j : V) :
    (single i r : Coords k Γ R) j = Pi.single (M := fun _ => R) i r j := rfl

/-- For `r ≠ 0`, distinct indices `i` give distinct vectors `single i r`. -/
lemma single_left_injective {r : R} (hr : r ≠ 0) :
    Function.Injective fun i => (single i r : Coords k Γ R) :=
  fun i j h => by simpa [Pi.single_apply, eq_comm, hr] using DFunLike.congr_fun h i

end Single

/-! ### The basis of simple roots or fundamental weights -/

variable (k Γ R) in
/-- The basis `(single i 1)ᵢ` of `Coords k Γ R`: the simple roots for `k = .root` and the
fundamental weights for `k = .weight`. Over `ℕ` these are bases of `Q⁺` and of `P⁺`. Like every
Mathlib basis it is noncomputable (see the module docstring); `coe_basis` identifies its vectors
with the computable `single i 1`. -/
noncomputable def basis [Finite V] [Semiring R] : Module.Basis V R (Coords k Γ R) :=
  .ofEquivFun { equiv with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

@[simp] lemma basis_repr_apply [Finite V] [Semiring R] (x : Coords k Γ R) (i : V) :
    (basis k Γ R).repr x i = x i :=
  rfl

/-- The basis vectors of `basis k Γ R` are the vectors `single i 1`. -/
@[simp] lemma coe_basis [Finite V] [DecidableEq V] [Semiring R] :
    ⇑(basis k Γ R) = fun i => single i 1 := by
  ext i : 1
  simp [basis]
  rfl

/-- Every vector is the sum of its coefficients times the basis vectors, e.g. `β = Σ βᵢ αᵢ`. -/
lemma sum_smul_single [Fintype V] [DecidableEq V] [Semiring R] (x : Coords k Γ R) :
    ∑ i, x i • single i 1 = x := by
  simpa using (basis k Γ R).sum_repr x

end Coords

/-! ### Simple roots and fundamental weights -/

/-- The simple root `αᵢ`: the vector with coefficient `1` at `i` and `0` elsewhere in the root
lattice. Over `ℕ` it is an element of `Q⁺`, over `ℤ` of `Q`. It is an `abbrev`, so every lemma
about `Coords.single` applies to it. -/
abbrev simpleRoot (Γ : SimpleGraph V) {R : Type*} [DecidableEq V] [Zero R] [One R] (i : V) :
    RootCoords Γ R :=
  Coords.single i 1

/-- The fundamental weight `ωᵢ`: the weight with Dynkin labels `1` at `i` and `0` elsewhere.
Over `ℕ` it is a dominant weight. It is an `abbrev`, so every lemma about `Coords.single`
applies to it. -/
abbrev fundWeight (Γ : SimpleGraph V) {R : Type*} [DecidableEq V] [Zero R] [One R] (i : V) :
    WeightCoords Γ R :=
  Coords.single i 1

/-! ### From roots to weights -/

namespace Coords

section ToWeight

variable {Γ : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]

/-- The Dynkin labels of an element `β` of the root lattice, i.e. `β` in the basis of fundamental
weights: `β ↦ Cβ`, where `C` is the Cartan matrix of `Γ`. It is injective exactly when `C` is
invertible. -/
def toWeight : RootCoords Γ ℤ →ₗ[ℤ] WeightCoords Γ ℤ where
  toFun β := ⟨Γ.cartanMatrix.mulVec β⟩
  map_add' _ _ := congrArg mk (Matrix.mulVec_add _ _ _)
  map_smul' _ _ := congrArg mk (Matrix.mulVec_smul _ _ _)

@[simp] lemma coe_toWeight (β : RootCoords Γ ℤ) :
    ⇑(toWeight β) = Γ.cartanMatrix.mulVec ⇑β := rfl

lemma toWeight_apply (β : RootCoords Γ ℤ) (i : V) :
    toWeight β i = Γ.cartanMatrix.mulVec (⇑β) i := rfl

/-- The Dynkin labels of the simple root `αᵢ` are the `i`-th column of the Cartan matrix. -/
@[simp] lemma coe_toWeight_simpleRoot (i : V) :
    ⇑(toWeight (simpleRoot Γ i)) = Γ.cartanMatrix.col i :=
  Matrix.mulVec_single_one _ _

/-- The simple root `αᵢ` in terms of the fundamental weights: `αᵢ = 2ωᵢ - Σ_{j ∼ i} ωⱼ`. In
particular `αᵢ` is not dominant as soon as `i` has a neighbour. -/
lemma toWeight_simpleRoot (i : V) :
    toWeight (simpleRoot Γ i) =
      2 • fundWeight Γ i - ∑ j ∈ Γ.neighborFinset i, fundWeight Γ j := by
  ext j
  rcases eq_or_ne j i with rfl | h
  · simp [SimpleGraph.cartanMatrix_apply, Matrix.col]
  · by_cases hA : Γ.Adj i j <;>
      simp [SimpleGraph.cartanMatrix_apply, Matrix.col, Pi.single_apply, h, hA, Γ.adj_comm]

/-- In the bases of simple roots and of fundamental weights, the matrix of `toWeight` is the
Cartan matrix. -/
theorem toMatrix_toWeight :
    LinearMap.toMatrix (basis .root Γ ℤ) (basis .weight Γ ℤ) toWeight = Γ.cartanMatrix := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp [Matrix.col]

end ToWeight

end Coords
end Lattices

end KLRW
