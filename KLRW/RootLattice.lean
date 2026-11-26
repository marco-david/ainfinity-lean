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
algebra whose Dynkin diagram is `Γ`, written in the basis of simple roots $α_i$ or of
fundamental weights $ω_i$.

## Main definitions

* `SimpleGraph.cartanMatrix`: the Cartan matrix $2I - A$ of a simply-laced graph.
* `KLRW.Coords k Γ R`: coordinate vectors for `Γ` with coefficients in `R`, in the basis selected
  by `k : KLRW.CoordKind`. They form an `R`-module.
* `KLRW.RootCoords`, `KLRW.WeightCoords`, `KLRW.DominantWeight`: the root lattice, the weight
  lattice and the dominant integral weights.
* `KLRW.Coords.single i r`: the vector with coefficient `r` at `i` and `0` elsewhere.
* `KLRW.simpleRoot Γ i`, `KLRW.fundamentalWeight Γ i`: the simple root $α_i$ and the
  fundamental weight $ω_i$, i.e. `single i 1` in the root and in the weight lattice.
* `KLRW.Coords.basis k Γ R`: the basis formed by the vectors `single i 1`, i.e. the simple roots
  or the fundamental weights.
* `KLRW.Coords.map`: apply a function to every coefficient, e.g. inclusion from `ℕ` to `ℤ`.
* `KLRW.Coords.toWeight`: the linear map sending an element $β$ of the root lattice to its
  Dynkin labels $Cβ$.

## Main statements

* `KLRW.Coords.coe_basis`: the simple roots form a basis of the root lattice and the fundamental
  weights a basis of the weight lattice (over `ℕ`: of the $ℕ$-sums of simple roots and of the
  dominant weights).
* `KLRW.Coords.toMatrix_toWeight`: in these bases, the matrix of `toWeight` is the Cartan matrix.
* `KLRW.Coords.toWeight_simpleRoot`: $α_i = 2ω_i - ∑_{j ∼ i} ω_j$.
* `SimpleGraph.cartanMatrix_isSymm`: the Cartan matrix is symmetric.

## Notation

We use the standard notation $α_i$ and $ω_i$ for the simple roots and the fundamental
weights, and $C$ for the Cartan matrix. In the terms of Lusztig (see References):
* `V` is the index set $I$, and `Γ` is the graph of a simply laced Cartan datum $(I, ⋅)$
  (§2.1.3, §14.1.3); `Γ.cartanMatrix i j` is $i ⋅ j$.
* `RootCoords Γ ℤ` is $ℤ[I]$ and `RootCoords Γ ℕ` is $ℕ[I]$ (§1.2.1);
  `simpleRoot Γ i` is $i$.
* `WeightCoords Γ ℤ` is $X = \mathrm{Hom}(ℤ[I], ℤ)$ of the simply connected
  root datum (§2.2.2): `x i` is $⟨i, x⟩$, `fundamentalWeight Γ i` is the dual basis
  vector, and `DominantWeight Γ` is $X^+$ (§3.5.5).
* `toWeight` is the map $ℤ[I] → X$ induced by $i ↦ i'$ (§2.2.1).

## Implementation notes

* `Coords k Γ R` is a structure wrapping a function `V → R` and tagged by the basis `k`, so that
  coordinates in the basis of simple roots and in the basis of fundamental weights cannot be
  confused; they are compared through `toWeight`. Bases are indexed by the
  vertices of `Γ`. The `i`-th coefficient of `x` is written `x i`, and the additive and module
  structures are transferred from `V → R` along `Coords.equiv`.
* A weight is recorded by its Dynkin labels, i.e. its coordinates in the basis of fundamental
  weights. This is faithful when $\det C ≠ 0$, which includes all types A, D and E. When
  $\det C = 0$, as for the affine types, it is not: different weights of the Kac–Moody algebra
  can have the same labels, and `toWeight` sends some nonzero elements of the root lattice to
  $0$, e.g. the null root $δ = 2α_{\mathrm{centre}} + ∑ α_{\mathrm{leaf}}$ of
  $\tilde D_4$.
* $C$ is symmetric (`SimpleGraph.cartanMatrix_isSymm`), so the conventions
  $a_{ij} = ⟨α_i^∨, α_j⟩$ and its transpose (used by Mathlib) give the
  same `toWeight`.
* `Coords.basis` is noncomputable, like every Mathlib basis. It is meant for statements and
  proofs; computations should use `single`, `simpleRoot` and `fundamentalWeight`. `coe_basis`
  identifies the basis vectors with them.

## TODO
* Orderings on `RootCoords` and `WeightCoords`
* Dual weights with path from weight to its dual
* Height function
* Compatibility with mathlib's ADE Cartans
* Consider upstreaming to Mathlib

## References

* G. Lusztig, *Introduction to quantum groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §§1.1–1.2, 2.1–2.2, 3.5 and 14.1.
-/

@[expose] public section

namespace KLRW

/-- Which basis a coordinate vector is written in. -/
inductive CoordKind
  /-- The simple roots $α_i$. -/
  | root
  /-- The fundamental weights $ω_i$. -/
  | weight

variable {V : Type*}

/-! ### The Cartan matrix -/

section CartanMatrix

variable [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The Cartan matrix $2I - A$ of a simply-laced graph. -/
def _root_.SimpleGraph.cartanMatrix : Matrix V V ℤ :=
  2 - G.adjMatrix ℤ

/-- The entries of the Cartan matrix: `2` on the diagonal, `-1` between adjacent vertices and `0`
between distinct non-adjacent vertices. -/
lemma _root_.SimpleGraph.cartanMatrix_apply (i j : V) :
    G.cartanMatrix i j = if i = j then 2 else if G.Adj i j then -1 else 0 := by
  by_cases h : i = j <;> by_cases hA : G.Adj i j <;>
    simp_all [SimpleGraph.cartanMatrix, Matrix.ofNat_apply]

/-- The Cartan matrix of a simply-laced graph is symmetric. -/
lemma _root_.SimpleGraph.cartanMatrix_isSymm : G.cartanMatrix.IsSymm :=
  Matrix.IsSymm.ext fun i j => by simp only [G.cartanMatrix_apply, eq_comm, G.adj_comm]

end CartanMatrix

/-! ### Coordinate vectors -/

/-- Coordinate vectors for `Γ` in the basis selected by `k`. -/
structure Coords (k : CoordKind) (Γ : SimpleGraph V) (R : Type*) where
  /-- The coefficient of the `i`-th basis vector. -/
  coeff : V → R

/-- `RootCoords Γ ℤ` is the root lattice; `RootCoords Γ ℕ` consists of the $ℕ$-sums of simple
roots. -/
abbrev RootCoords (Γ : SimpleGraph V) (R : Type*) := Coords .root Γ R
/-- `WeightCoords Γ ℤ` is the weight lattice, recorded by Dynkin labels (see the module docstring
when the Cartan matrix is singular); `WeightCoords Γ ℕ` consists of the dominant weights. -/
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
reducible, so that for `R = ℕ` and `R = ℤ` this module structure agrees with the multiples coming
from the additive structure. -/
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

/-- Apply `f` to every coefficient, keeping the basis. For instance `x.map (↑)` views an
$ℕ$-sum of simple roots (resp. a dominant weight) `x` as an element of the root lattice (resp.
the weight lattice). -/
def map (f : R → S) (x : Coords k Γ R) : Coords k Γ S := ⟨fun i => f (x i)⟩

@[simp] lemma coe_map (f : R → S) (x : Coords k Γ R) : ⇑(x.map f) = f ∘ ⇑x := rfl
lemma map_apply (f : R → S) (x : Coords k Γ R) (i : V) : x.map f i = f (x i) := rfl

@[simp] lemma map_id (x : Coords k Γ R) : x.map id = x := rfl

@[simp] lemma map_map (f : R → S) (g : S → T) (x : Coords k Γ R) :
    (x.map f).map g = x.map (g ∘ f) := rfl

/-- Applying an injective map to the coefficients is injective. For instance `map (↑)` embeds the
$ℕ$-sums of simple roots into the root lattice and the dominant weights into the weight lattice,
by `map_injective Nat.cast_injective`. -/
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
$α_i$ (`simpleRoot`) or the fundamental weight $ω_i$ (`fundamentalWeight`). -/
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

section Basis

variable [Finite V] [Semiring R]

variable (k Γ R) in
/-- The basis of `Coords k Γ R` formed by the vectors `single i 1`: the simple roots for
`k = .root` and the fundamental weights for `k = .weight`. Over `ℕ` these are bases of the
$ℕ$-sums of simple roots and of the dominant weights. Like every Mathlib basis it is
noncomputable (see the module docstring); `coe_basis` identifies its vectors with the computable
`single i 1`. -/
noncomputable def basis : Module.Basis V R (Coords k Γ R) :=
  .ofEquivFun { equiv with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

@[simp] lemma basis_repr_apply (x : Coords k Γ R) (i : V) : (basis k Γ R).repr x i = x i :=
  rfl

/-- The basis vectors of `basis k Γ R` are the vectors `single i 1`. -/
@[simp] lemma coe_basis [DecidableEq V] : ⇑(basis k Γ R) = fun i => single i 1 :=
  Module.Basis.coe_ofEquivFun _

omit [Finite V] in
/-- Every vector is the sum of its coefficients times the basis vectors, e.g.
$β = ∑_i β_i α_i$. -/
lemma sum_smul_single [Fintype V] [DecidableEq V] (x : Coords k Γ R) :
    ∑ i, x i • single i 1 = x := by
  simpa using (basis k Γ R).sum_repr x

end Basis

end Coords

/-! ### Simple roots and fundamental weights -/

/-- The simple root $α_i$: the vector with coefficient `1` at `i` and `0` elsewhere, in the root
lattice (over `ℤ`) or among the $ℕ$-sums of simple roots (over `ℕ`). -/
abbrev simpleRoot (Γ : SimpleGraph V) {R : Type*} [DecidableEq V] [Zero R] [One R] (i : V) :
    RootCoords Γ R :=
  Coords.single i 1

/-- The fundamental weight $ω_i$: the weight with Dynkin labels `1` at `i` and `0`
elsewhere. Over `ℕ` it is a dominant weight. -/
abbrev fundamentalWeight (Γ : SimpleGraph V) {R : Type*} [DecidableEq V] [Zero R] [One R]
    (i : V) : WeightCoords Γ R :=
  Coords.single i 1

/-! ### From roots to weights -/

namespace Coords

section ToWeight

variable {Γ : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]

/-- The Dynkin labels of an element $β$ of the root lattice, i.e. $β$ in the basis of
fundamental weights: $β ↦ Cβ$, where $C$ is the Cartan matrix of `Γ`. -/
def toWeight : RootCoords Γ ℤ →ₗ[ℤ] WeightCoords Γ ℤ where
  toFun β := ⟨Γ.cartanMatrix.mulVec β⟩
  map_add' _ _ := congrArg mk (Matrix.mulVec_add _ _ _)
  map_smul' _ _ := congrArg mk (Matrix.mulVec_smul _ _ _)

@[simp] lemma coe_toWeight (β : RootCoords Γ ℤ) :
    ⇑(toWeight β) = Γ.cartanMatrix.mulVec ⇑β := rfl

lemma toWeight_apply (β : RootCoords Γ ℤ) (i : V) :
    toWeight β i = Γ.cartanMatrix.mulVec (⇑β) i := rfl

/-- The Dynkin labels of the simple root $α_i$ are the `i`-th column of the Cartan matrix. -/
@[simp] lemma coe_toWeight_simpleRoot (i : V) :
    ⇑(toWeight (simpleRoot Γ i)) = Γ.cartanMatrix.col i :=
  Matrix.mulVec_single_one _ _

/-- The simple root $α_i$ in terms of the fundamental weights:
$α_i = 2ω_i - ∑_{j ∼ i} ω_j$. In particular $α_i$ is not dominant as soon
as `i` has a neighbour. -/
lemma toWeight_simpleRoot (i : V) :
    toWeight (simpleRoot Γ i) =
      2 • fundamentalWeight Γ i - ∑ j ∈ Γ.neighborFinset i, fundamentalWeight Γ j := by
  ext j
  rcases eq_or_ne j i with rfl | h
  · simp [SimpleGraph.cartanMatrix_apply, Matrix.col]
  · by_cases hA : Γ.Adj i j <;>
      simp [SimpleGraph.cartanMatrix_apply, Matrix.col, Pi.single_apply, h, hA, Γ.adj_comm]

/-- In the bases of simple roots and of fundamental weights, the matrix of `toWeight` is the
Cartan matrix. -/
lemma toMatrix_toWeight :
    LinearMap.toMatrix (basis .root Γ ℤ) (basis .weight Γ ℤ) toWeight = Γ.cartanMatrix := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp [Matrix.col]

end ToWeight

end Coords

end KLRW
