/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi, Marco David
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import AInfinity.AInfinityCategoryStruct
public import AInfinity.Composition

/-! # Composable multilinear maps

Fix a map on objects `obj : Obj → Obj'` between graded `R`-linear quivers and a homomorphism of
gradings `degMap : β →+ᵍ β'`. A composable multilinear map Φ over `obj` and `degMap` consists of,
for each n ≥ 1 and each composable string of objects X₀, …, Xₙ, a graded multilinear map
$$\Phi_n : \operatorname{Hom}(X_0, X_1) \otimes \dots \otimes \operatorname{Hom}(X_{n-1}, X_n)
  \to \operatorname{Hom}(\operatorname{obj} X_0, \operatorname{obj} X_n)$$
of degree (s - n) · 1, for a fixed integer `s`. No relations are imposed.

In reduced degrees ‖a‖ = |a| - 1, the component Φₙ has degree s - 1 for every n: a composable
multilinear map is the family of Taylor coefficients of a map of degree s - 1 between bar
constructions, along the map `obj` on objects. The structure maps of A∞-theory are of this form:

* the components φₙ of an A∞-functor `F`, of degree 1 - n, are a composable multilinear map
  with `s = 1` over `F.obj` and `F.degMap`
  (`AInfinityTheory.AInfinityFunctorData.toComposableMultilinearMap`);
* the higher compositions mₙ of an A∞-category, of degree 2 - n, are a composable multilinear
  map with `s = 2` over the identity
  (`AInfinityTheory.AInfinityCategoryStruct.toComposableMultilinearMap`);
* for an A∞-functor `F` to an A∞-category with operations m', both sides m' ∘ F and F ∘ m of
  the A∞-functor equation are composable multilinear maps with `s = 2` over `F.obj` and
  `F.degMap`.

The last example is the reason why the maps `obj` and `degMap` are parameters of the type, and not
fields: composable multilinear maps of different degrees `s` over the same `obj` and `degMap` can
be fed to the same outer map, see `AInfinityTheory.ComposableMultilinearMap.compMarked` in
`AInfinity.FunctorComposition.Defs`.

## Main definitions

* `AInfinityTheory.ComposableMultilinearMap R obj degMap s`: a composable multilinear map.
* `AInfinityTheory.ComposableMultilinearMap.id`: the identity, with `s = 1`: its unary component
  is the identity and its other components vanish.
* `AInfinityTheory.AInfinityCategoryStruct.toComposableMultilinearMap`: the operations mₙ of an
  A∞-category structure, as a composable multilinear map with `s = 2`.
* `AInfinityTheory.compositionBlockObj`: the object string of a block of a composition.
* `AInfinityTheory.ComposableMultilinearMap.blockMap`: the value of a composable multilinear map
  on a block of a composition.
* `AInfinityTheory.ComposableMultilinearMap.applyBlocks`: a composable multilinear map applied to
  a composable string of morphisms along a composition.
* `AInfinityTheory.ComposableMultilinearMap.compTerm`: the term Φₖ(P₁(…), …, Pₖ(…)) of a
  composite, for a composition into k blocks and a choice `P` of a map for each block.
* `AInfinityTheory.ComposableMultilinearMap.comp`: the composite Φ ∘ F, with components
  $$(\Phi \circ F)_n(a_1, \dots, a_n) = \sum_{k \ge 1} \sum_{i_1 + \dots + i_k = n}
    \Phi_k(F_{i_1}(a_1, \dots, a_{i_1}), \dots, F_{i_k}(a_{n-i_k+1}, \dots, a_n)).$$
  It is linear in Φ, and polynomial in `F`: its term Φₖ(F, …, F) is k-linear. For the operations
  m' of an A∞-category, m' ∘ F is the right-hand side of the A∞-functor equation of `F`.

## Main results

* `AInfinityTheory.ComposableMultilinearMap.total_map_congr`: congruence for the components of a
  composable multilinear map in the type of all morphisms. Only the arities and the inputs are
  compared.
* `AInfinityTheory.ComposableMultilinearMap.comp_map_v_apply`: the value of Φ ∘ F, as a sum of
  terms.
* `AInfinityTheory.ComposableMultilinearMap.comp_id`: `Φ ∘ 𝟙 = Φ`. Only the composition of `n`
  into blocks of size one contributes to the composite.
* `AInfinityTheory.ComposableMultilinearMap.id_comp`: `𝟙 ∘ F = F`. Only the composition of `n`
  with a single block contributes to the composite.

## Implementation notes

The degree of Φₙ is written `(s - n : ℤ) • degOne`, so that for `s = 2` it is syntactically the
degree `(2 - n : ℤ) • degOne` of an operation. The degree of Φₙ(a₁, …, aₙ) is
`AInfinityTheory.targetDeg s deg`.

The inputs of Φₙ are graded by `β` and its output by `β'`, so the output family is read through
`degMap`. All degree arithmetic happens in `β`.

Composites of maps on objects are written `fun X ↦ g (f X)` and the identity `fun X ↦ X`, so that
they reduce when applied. The laws `GradingHom.comp_id`, `GradingHom.id_comp` and
`GradingHom.comp_assoc` hold by `rfl`, so composable multilinear maps over both sides of these
laws have the same type. For instance, the two sides of the unit law `comp_id` are over
`fun X ↦ f X` and `φ.comp (GradingHom.id β)`, and over `f` and `φ`, so `comp_id` and `id_comp` are
equalities in one type and can be used to rewrite.

A term of a composite is described by a composition `c` of `n` and a choice
`P : Fin c.length → Σ u : ℤ, ComposableMultilinearMap R f φ u` of a composable multilinear map,
together with its degree, for each block of `c`. For Φ ∘ F the choice is constant; the marked
composite Φ ∘ (F | D) of `AInfinity.FunctorComposition.Defs` chooses `D` on one block.

Terms are defined in any degree `d` equal to their degree, with a proof of the equality as an
argument, as for `stasheffTerm`. Every definition that transports along equalities of objects or
degrees is stated so that the endpoints of `homCongr` are syntactically those of its type. Then
`simp` removes the transport from under `GradedLinearQuiver.Total.of`, and two descriptions of a
term are compared with `ComposableMultilinearMap.total_map_congr`.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

open GradedLinearQuiver

variable {n : ℕ}

/-- A composable multilinear map Φ over a map on objects `obj` and a homomorphism of gradings
`degMap`: for each n ≥ 1 and each composable string of objects X₀, …, Xₙ, a multilinear map
Φₙ : Hom(X₀, X₁) ⊗ ⋯ ⊗ Hom(Xₙ₋₁, Xₙ) → Hom(obj X₀, obj Xₙ) of degree (s - n) · 1. In reduced
degrees, every Φₙ has degree s - 1. The components of A∞-functors are the case `s = 1` and the
operations of A∞-categories are the case `s = 2`. No relations are imposed. -/
structure ComposableMultilinearMap (R : Type*) [Semiring R] {β β' : Type*} [AddCommGroup β]
    [Grading β] [AddCommGroup β'] [Grading β'] {Obj Obj' : Type*} [GradedLinearQuiver β R Obj]
    [GradedLinearQuiver β' R Obj'] (obj : Obj → Obj') (degMap : β →+ᵍ β') (s : ℤ) where
  /-- The components Φₙ, of degree (s - n) · 1, landing in the hom spaces of the target in the
  translated degrees. -/
  map {n : ℕ} [NeZero n] (X : Fin (n + 1) → Obj) :
    GradedMultilinearMap R (ComposableHom β R X)
      (fun b : β ↦ (obj (X 0) →ᵍ[R] obj (X (Fin.last n))) (degMap b))
      ((s - n : ℤ) • degOne)

namespace ComposableMultilinearMap

variable {β β' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  {R : Type*} [Semiring R] {Obj Obj' : Type*} [GradedLinearQuiver β R Obj]
  [GradedLinearQuiver β' R Obj'] {obj : Obj → Obj'} {degMap : β →+ᵍ β'} {s : ℤ}

/-- Two composable multilinear maps are equal if their components agree on all composable
strings of inputs. -/
@[ext]
lemma ext {Φ Ψ : ComposableMultilinearMap R obj degMap s}
    (h : ∀ {n : ℕ} [NeZero n] {X : Fin (n + 1) → Obj} {deg : Fin n → β}
      (a : ∀ i, ComposableHom β R X i (deg i)) {j : β} (hj : targetDeg s deg = j),
      (Φ.map X).v deg j hj a = (Ψ.map X).v deg j hj a) : Φ = Ψ := by
  obtain ⟨Φ⟩ := Φ
  obtain ⟨Ψ⟩ := Ψ
  congr 1
  funext n _ X
  exact GradedMultilinearMap.ext fun deg j hj ↦ MultilinearMap.ext fun a ↦ h a hj

/-- Congruence for the components of a composable multilinear map in the type of all morphisms:
only the arities and the inputs are compared. The object strings and the degrees are determined
by the inputs. -/
theorem total_map_congr (Φ : ComposableMultilinearMap R obj degMap s) {k k' : ℕ} [NeZero k]
    [NeZero k'] (e : k = k') {Y : Fin (k + 1) → Obj} {Y' : Fin (k' + 1) → Obj} {δ : Fin k → β}
    {δ' : Fin k' → β} {j j' : β} (hj : targetDeg s δ = j) (hj' : targetDeg s δ' = j')
    {b : ∀ i, ComposableHom β R Y i (δ i)} {b' : ∀ i, ComposableHom β R Y' i (δ' i)}
    (hb : ∀ i, Total.of (b i) = Total.of (b' (i.cast e))) :
    Total.of ((Φ.map Y).v δ j hj b) = Total.of ((Φ.map Y').v δ' j' hj' b') := by
  subst hj hj'
  exact Total.congr_composable (fun k _ Y δ b ↦ Total.of ((Φ.map Y).v δ _ rfl b)) e hb

/-! ### The identity -/

section Identity

variable (X : Fin (1 + 1) → Obj)

lemma idMap_deg {deg : Fin 1 → β} {j : β} (hj : targetDeg 1 deg = j) :
    deg 0 = GradingHom.id β j := by
  simpa [targetDeg] using hj

/-- The unary component of the identity composable multilinear map: the identity of
Hom(X₀, X₁). -/
def idMap : GradedMultilinearMap R (ComposableHom β R X)
    (fun b : β ↦ (X 0 →ᵍ[R] X (Fin.last 1)) (GradingHom.id β b))
    (((1 : ℤ) - ((1 : ℕ) : ℤ)) • degOne) :=
  .mk fun deg j hj ↦
    { toFun := fun a ↦ homCongr R rfl rfl (idMap_deg hj) (a 0)
      map_update_add' := fun m i x y ↦ by
        obtain rfl : i = 0 := Subsingleton.elim _ _
        simp only [Function.update_self]
        exact map_add _ x y
      map_update_smul' := fun m i c x ↦ by
        obtain rfl : i = 0 := Subsingleton.elim _ _
        simp only [Function.update_self]
        exact map_smul _ c x }

lemma idMap_v_apply {deg : Fin 1 → β} (a : ∀ i, ComposableHom β R X i (deg i)) {j : β}
    (hj : targetDeg 1 deg = j) :
    (idMap X).v deg j hj a = homCongr R rfl rfl (idMap_deg hj) (a 0) :=
  rfl

/-- The component of arity n of the identity composable multilinear map: the identity for
n = 1, and zero otherwise. -/
def idComponent {n : ℕ} [NeZero n] (X : Fin (n + 1) → Obj) :
    GradedMultilinearMap R (ComposableHom β R X)
      (fun b : β ↦ (X 0 →ᵍ[R] X (Fin.last n)) (GradingHom.id β b)) (((1 : ℤ) - n) • degOne) :=
  match n with
  | 1 => idMap X
  | _ => 0

variable (β R Obj) in
/-- The identity composable multilinear map, with `s = 1`: its unary component is the identity
and its components of higher arity vanish. These are the components of the identity
A∞-functor. -/
protected def id : ComposableMultilinearMap R (fun X : Obj ↦ X) (GradingHom.id β) 1 where
  map X := idComponent X

@[simp]
lemma id_map_one : (ComposableMultilinearMap.id β R Obj).map X = idMap X :=
  rfl

lemma id_map_eq_zero [NeZero n] (hn : n ≠ 1) (X : Fin (n + 1) → Obj) :
    (ComposableMultilinearMap.id β R Obj).map X = 0 := by
  change idComponent X = 0
  unfold idComponent
  split
  · exact absurd rfl hn
  · rfl

end Identity

end ComposableMultilinearMap

/-! ### The operations of an A∞-category structure -/

namespace AInfinityCategoryStruct

variable {β : Type*} [AddCommGroup β] [Grading β] {R : Type*} [Semiring R] {Obj : Type*}
  [AInfinityCategoryStruct β R Obj]

variable (β R Obj) in
/-- The higher compositions mₙ of an A∞-category structure, of degree 2 - n, as a composable
multilinear map with `s = 2` over the identity. -/
def toComposableMultilinearMap :
    ComposableMultilinearMap R (fun X : Obj ↦ X) (GradingHom.id β) 2 where
  map X := m X

@[simp]
lemma toComposableMultilinearMap_map {n : ℕ} [NeZero n] (X : Fin (n + 1) → Obj) :
    (toComposableMultilinearMap β R Obj).map X = m X :=
  rfl

end AInfinityCategoryStruct

/-! ### Blocks of a composition

A composition c = (i₁, …, iₖ) of `n` cuts a composable string of `n` inputs into k
blocks: the `l`-th block has size iₗ, which is `c.blocksFun l`, and starts at
position `c.sizeUpTo l`. In a composite Φ ∘ F, the component of `F` of arity iₗ is applied to the
`l`-th block and the component of Φ of arity k to the resulting k values, so both the sizes of the
blocks and their number must be positive. The lemmas on `Composition` used here are in
`AInfinity.Composition`. -/

section CompositionBlock

variable {Obj : Type*} (X : Fin (n + 1) → Obj) (c : Composition n) (l : Fin c.length)

/-- The object string of the `l`-th block of a composition `c` of `n`: its `i`-th object is
`X (c.sizeUpTo l + i)`, for `i ≤ c.blocksFun l`. -/
def compositionBlockObj : Fin (c.blocksFun l + 1) → Obj :=
  fun i ↦ X ((i.natAdd (c.sizeUpTo l)).castLE (Nat.succ_le_succ (c.sizeUpTo_add_blocksFun_le l)))

@[simp]
lemma compositionBlockObj_zero :
    compositionBlockObj X c l 0 = X (c.boundary l.castSucc) := by
  unfold compositionBlockObj
  congr 1

@[simp]
lemma compositionBlockObj_last :
    compositionBlockObj X c l (Fin.last (c.blocksFun l)) = X (c.boundary l.succ) := by
  unfold compositionBlockObj Composition.boundary
  congr 1
  ext
  simp [Composition.sizeUpTo_succ']

end CompositionBlock

/-! ### Degrees -/

section Degrees

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] (φ : β →+ᵍ β') (ψ : β' →+ᵍ β'') (deg : Fin n → β)

/-- Applying maps of degrees (σ₁ - i₁) · 1, …, (σₖ - iₖ) · 1 to the blocks of a composition
c = (i₁, …, iₖ) of `n`, and then a map of degree (s - k) · 1 to their values, has the degree of
a map of degree (s + ∑ₗ (σₗ - 1) - n) · 1. -/
lemma targetDeg_targetDeg_embedding_of_sum (s : ℤ) (c : Composition n) (σ : Fin c.length → ℤ) :
    targetDeg s (fun l ↦ targetDeg (σ l) fun j ↦ deg (c.embedding l j)) =
      targetDeg (s + ∑ l, (σ l - 1)) deg := by
  simp only [targetDeg, Finset.sum_add_distrib, c.sum_sum_apply_embedding, add_assoc,
    ← Finset.sum_smul, ← add_smul, c.sum_sub_blocksFun_add s σ]

/-- `targetDeg_targetDeg_embedding_of_sum` translated along homomorphisms of gradings. -/
lemma degMap_targetDeg_degMap_targetDeg_embedding {s u : ℤ} (c : Composition n)
    (σ : Fin c.length → ℤ) (hσ : s + ∑ l, (σ l - 1) = u) {j : β} (hj : targetDeg u deg = j) :
    ψ (targetDeg s fun l ↦ φ (targetDeg (σ l) fun i ↦ deg (c.embedding l i))) = (ψ.comp φ) j :=
  congrArg ψ ((targetDeg_map φ s _).trans (congrArg φ
    ((targetDeg_targetDeg_embedding_of_sum deg s c σ).trans (hσ ▸ hj))))

end Degrees

namespace ComposableMultilinearMap

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}
  [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj'] [GradedLinearQuiver β'' R Obj'']
  {f : Obj → Obj'} {φ : β →+ᵍ β'} {g : Obj' → Obj''} {ψ : β' →+ᵍ β''} {s t u : ℤ}

/-! ### The value of a composable multilinear map on a block of a composition -/

section Block

variable (D : ComposableMultilinearMap R f φ t) (X : Fin (n + 1) → Obj) (deg : Fin n → β)
  (c : Composition n) (l : Fin c.length)

/-- The component of arity iₗ of `D` on the `l`-th block of a composition c = (i₁, …, iₖ) of `n`,
as a multilinear map into the hom space of the `l`-th input of an outer map of arity k.
Evaluated on composable inputs, it is `blockMap`. -/
def blockMultilinearMap :
    MultilinearMap R (fun j ↦ ComposableHom β R X (c.embedding l j) (deg (c.embedding l j)))
      (ComposableHom β' R (fun k ↦ f (X (c.boundary k))) l
        (φ (targetDeg t fun j ↦ deg (c.embedding l j)))) :=
  (homCongr R (congrArg f (compositionBlockObj_zero X c l))
    (congrArg f (compositionBlockObj_last X c l)) rfl).toLinearMap.compMultilinearMap
    ((D.map (compositionBlockObj X c l)).v (fun j ↦ deg (c.embedding l j)) _ rfl)

variable {X deg}

/-- The value of the component of arity iₗ of `D` on the `l`-th block of a composition
c = (i₁, …, iₖ) of `n`, as the `l`-th input of an outer map of arity k. -/
def blockMap (D : ComposableMultilinearMap R f φ t)
    (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (c : Composition n) (l : Fin c.length) :
    ComposableHom β' R (fun k ↦ f (X (c.boundary k))) l
      (φ (targetDeg t fun j ↦ deg (c.embedding l j))) :=
  homCongr R (congrArg f (compositionBlockObj_zero X c l))
    (congrArg f (compositionBlockObj_last X c l)) rfl
    ((D.map (compositionBlockObj X c l)).v (fun j ↦ deg (c.embedding l j)) _ rfl
      fun j ↦ a (c.embedding l j))

@[simp]
lemma blockMultilinearMap_apply (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) :
    D.blockMultilinearMap X deg c l (fun j ↦ a (c.embedding l j)) = D.blockMap a c l :=
  rfl

end Block

/-! ### A composable multilinear map applied along a composition -/

section ApplyBlocks

variable (Φ : ComposableMultilinearMap R g ψ s) (f) (X : Fin (n + 1) → Obj) [NeZero n]
  (c : Composition n)

/-- The component of arity k of Φ applied to a composable string `B` of k morphisms between the
objects `f (X (c.boundary k))`, for a composition `c` of `n` into k blocks: a morphism from
`g (f X₀)` to `g (f Xₙ)`, in any degree `d` equal to its degree. -/
def applyBlocks {ε : Fin c.length → β'}
    (B : ∀ l, ComposableHom β' R (fun k ↦ f (X (c.boundary k))) l (ε l)) (d : β'')
    (hd : ψ (targetDeg s ε) = d) : (g (f (X 0)) →ᵍ[R] g (f (X (Fin.last n)))) d :=
  homCongr R (congrArg (fun k ↦ g (f (X k))) c.boundary_zero)
    (congrArg (fun k ↦ g (f (X k))) c.boundary_last) hd
    ((Φ.map fun k ↦ f (X (c.boundary k))).v ε _ rfl B)

end ApplyBlocks

section CompTerm

variable (Φ : ComposableMultilinearMap R g ψ s) [NeZero n] (X : Fin (n + 1) → Obj)
  (deg : Fin n → β) (c : Composition n)
  (P : Fin c.length → Σ u : ℤ, ComposableMultilinearMap R f φ u) (d : β'')
  (hd : ψ (targetDeg s fun l ↦ φ (targetDeg (P l).1 fun j ↦ deg (c.embedding l j))) = d)

/-- The term indexed by a composition c = (i₁, …, iₖ) of `n` of a composite: the multilinear map
(a₁, …, aₙ) ↦ Φₖ(P₁(a₁, …, a_{i₁}), …, Pₖ(a_{n-iₖ+1}, …, aₙ)),
for a choice `P` of a composable multilinear map for each block of `c`. -/
def compTermMultilinearMap :
    MultilinearMap R (fun i ↦ ComposableHom β R X i (deg i))
      ((g (f (X 0)) →ᵍ[R] g (f (X (Fin.last n)))) d) :=
  (homCongr R (congrArg (fun k ↦ g (f (X k))) c.boundary_zero)
    (congrArg (fun k ↦ g (f (X k))) c.boundary_last) hd).toLinearMap.compMultilinearMap
    (MultilinearMap.compComposition c
      ((Φ.map fun k ↦ f (X (c.boundary k))).v
        (fun l ↦ φ (targetDeg (P l).1 fun j ↦ deg (c.embedding l j))) _ rfl)
      fun l ↦ (P l).2.blockMultilinearMap X deg c l)

variable {X deg}

/-- The value Φₖ(P₁(a₁, …, a_{i₁}), …, Pₖ(a_{n-iₖ+1}, …, aₙ)) of the term indexed by a
composition c = (i₁, …, iₖ) of `n` of a composite, for a choice `P` of a composable multilinear
map for each block of `c`. -/
def compTerm (Φ : ComposableMultilinearMap R g ψ s)
    (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (c : Composition n)
    (P : Fin c.length → Σ u : ℤ, ComposableMultilinearMap R f φ u) (d : β'')
    (hd : ψ (targetDeg s fun l ↦ φ (targetDeg (P l).1 fun j ↦ deg (c.embedding l j))) = d) :
    (g (f (X 0)) →ᵍ[R] g (f (X (Fin.last n)))) d :=
  Φ.applyBlocks f X c (fun l ↦ (P l).2.blockMap a c l) d hd

@[simp]
lemma compTermMultilinearMap_apply (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) :
    Φ.compTermMultilinearMap X deg c P d hd a = Φ.compTerm a c P d hd :=
  rfl

end CompTerm

/-! ### The composite Φ ∘ F -/

section Comp

variable (Φ : ComposableMultilinearMap R g ψ s) (F : ComposableMultilinearMap R f φ 1)

omit [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj'] in
/-- A term of Φ ∘ F has the degree of Φ. -/
lemma comp_deg (φ : β →+ᵍ β') (ψ : β' →+ᵍ β'') (deg : Fin n → β) (c : Composition n) {j : β}
    (hj : targetDeg s deg = j) :
    ψ (targetDeg s fun l ↦ φ (targetDeg 1 fun i ↦ deg (c.embedding l i))) = (ψ.comp φ) j :=
  degMap_targetDeg_degMap_targetDeg_embedding φ ψ deg c _ (by simp) hj

/-- The composite Φ ∘ F of a composable multilinear map Φ with a composable multilinear map `F`
with `s = 1`, written in Mathlib's order. Its component of arity n is the sum, over all
compositions i₁ + ⋯ + iₖ = n, of Φₖ applied to the values of F_{i₁}, …, F_{iₖ}. It has the same
degree `s` as Φ, and is linear in Φ only. -/
protected def comp : ComposableMultilinearMap R (fun X ↦ g (f X)) (ψ.comp φ) s where
  map X := .mk fun deg j hj ↦ ∑ c : Composition _,
    Φ.compTermMultilinearMap X deg c (fun _ ↦ ⟨1, F⟩) ((ψ.comp φ) j) (comp_deg φ ψ deg c hj)

variable {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))
  [NeZero n] {j : β}

/-- The value of the component of arity n of Φ ∘ F: the sum, over all compositions `c` of `n`, of
Φ applied to the values of `F` on the blocks of `c`. -/
lemma comp_map_v_apply (hj : targetDeg s deg = j) :
    ((Φ.comp F).map X).v deg j hj a =
      ∑ c : Composition n, Φ.compTerm a c (fun _ ↦ ⟨1, F⟩) ((ψ.comp φ) j)
        (comp_deg φ ψ deg c hj) :=
  sum_apply Finset.univ (fun c ↦ Φ.compTermMultilinearMap X deg c (fun _ ↦ ⟨1, F⟩)
    ((ψ.comp φ) j) (comp_deg φ ψ deg c hj)) a

end Comp

end ComposableMultilinearMap

namespace ComposableMultilinearMap

variable {β β' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  {R : Type*} [Semiring R] {Obj Obj' : Type*} [GradedLinearQuiver β R Obj]
  [GradedLinearQuiver β' R Obj'] {f : Obj → Obj'} {φ : β →+ᵍ β'} {s : ℤ}

/-! ### Values of the identity on blocks -/

section IdBlock

/-- The unary component of the identity is the identity, in the type of all morphisms. -/
lemma total_id_map {k : ℕ} [NeZero k] (hk : k = 1) {Y : Fin (k + 1) → Obj} {δ : Fin k → β}
    (b : ∀ i, ComposableHom β R Y i (δ i)) {j : β} (hj : targetDeg 1 δ = j) :
    Total.of (((ComposableMultilinearMap.id β R Obj).map Y).v δ j hj b) =
      Total.of (b ⟨0, hk ▸ Nat.one_pos⟩) := by
  subst hk
  simp only [id_map_one, idMap_v_apply, Total.of_homCongr]
  rfl

variable {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))
  (c : Composition n) (l : Fin c.length)

/-- The value of the identity on a block of size one is the input of that block. -/
lemma total_id_blockMap (hl : c.blocksFun l = 1) :
    Total.of ((ComposableMultilinearMap.id β R Obj).blockMap a c l) =
      Total.of (a (c.embedding l ⟨0, hl ▸ Nat.one_pos⟩)) := by
  simp only [blockMap, Total.of_homCongr]
  exact total_id_map hl _ _

/-- The value of the identity on a block of size other than one vanishes. -/
lemma id_blockMap_eq_zero (hl : c.blocksFun l ≠ 1) :
    (ComposableMultilinearMap.id β R Obj).blockMap a c l = 0 := by
  simp only [blockMap, id_map_eq_zero hl, GradedMultilinearMap.zero_v]
  exact map_zero _

end IdBlock

/-! ### The identity is a right unit -/

section CompId

variable (Φ : ComposableMultilinearMap R f φ s) [NeZero n] {X : Fin (n + 1) → Obj}
  {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

/-- A term of Φ ∘ 𝟙 vanishes unless all blocks of its composition have size one. -/
lemma compTerm_id_eq_zero (c : Composition n) (hc : c ≠ Composition.ones n) (d : β')
    (hd : _) :
    Φ.compTerm a c (fun _ ↦ ⟨1, ComposableMultilinearMap.id β R Obj⟩) d hd = 0 := by
  obtain ⟨i, hi, h1⟩ := Composition.ne_ones_iff.1 hc
  obtain ⟨l, rfl⟩ := List.mem_iff_get.1 hi
  simp only [compTerm, applyBlocks]
  rw [MultilinearMap.map_coord_zero _ l (id_blockMap_eq_zero a c l (Nat.ne_of_gt h1)), map_zero]

/-- The term of Φ ∘ 𝟙 indexed by the composition into blocks of size one is the value of Φ. -/
lemma total_compTerm_id_ones (d : β') (hd : _) {j : β} (hj : targetDeg s deg = j) :
    Total.of (Φ.compTerm a (Composition.ones n)
      (fun _ ↦ ⟨1, ComposableMultilinearMap.id β R Obj⟩) d hd) =
      Total.of ((Φ.map X).v deg j hj a) := by
  simp only [compTerm, applyBlocks, Total.of_homCongr]
  refine Φ.total_map_congr (Composition.ones_length n) _ _ fun l ↦ ?_
  refine (total_id_blockMap a _ l (Composition.ones_blocksFun n l)).trans ?_
  exact congrArg (fun i ↦ Total.of (a i)) ((Composition.ones_embedding l _).trans (Fin.ext rfl))

/-- The identity is a right unit for the composition of composable multilinear maps. -/
theorem comp_id (Φ : ComposableMultilinearMap R f φ s) :
    Φ.comp (ComposableMultilinearMap.id β R Obj) = Φ := by
  ext n _ X deg a j hj
  rw [comp_map_v_apply, Finset.sum_eq_single (Composition.ones n)
    (fun c _ hc ↦ compTerm_id_eq_zero Φ a c hc _ _) (fun hn ↦ absurd (Finset.mem_univ _) hn)]
  exact Total.of_inj.1 (total_compTerm_id_ones Φ a _ _ hj)

end CompId

/-! ### The identity is a left unit -/

section IdComp

variable (F : ComposableMultilinearMap R f φ 1) [NeZero n] {X : Fin (n + 1) → Obj}
  {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

/-- A term of 𝟙 ∘ F vanishes unless its composition has a single block. -/
lemma id_compTerm_eq_zero (c : Composition n) (hc : c ≠ Composition.single n (NeZero.pos n))
    (d : β') (hd : _) :
    (ComposableMultilinearMap.id β' R Obj').compTerm a c (fun _ ↦ ⟨1, F⟩) d hd = 0 := by
  have hl : c.length ≠ 1 := fun hl ↦ hc ((Composition.eq_single_iff_length (NeZero.pos n)).2 hl)
  simp only [compTerm, applyBlocks, id_map_eq_zero hl, GradedMultilinearMap.zero_v]
  exact map_zero _

/-- The term of 𝟙 ∘ F indexed by the composition with a single block is the value of `F`. -/
lemma total_id_compTerm_single (d : β') (hd : _) {j : β} (hj : targetDeg 1 deg = j) :
    Total.of ((ComposableMultilinearMap.id β' R Obj').compTerm a
      (Composition.single n (NeZero.pos n)) (fun _ ↦ ⟨1, F⟩) d hd) =
      Total.of ((F.map X).v deg j hj a) := by
  simp only [compTerm, applyBlocks, Total.of_homCongr]
  refine (total_id_map (Composition.single_length (NeZero.pos n)) _ _).trans ?_
  simp only [blockMap, Total.of_homCongr]
  refine F.total_map_congr (Composition.single_blocksFun (NeZero.pos n) _) _ _ fun i ↦ ?_
  exact congrArg (fun i ↦ Total.of (a i))
    (Fin.ext ((Composition.coe_embedding _ _ _).trans (zero_add _)))

/-- The identity is a left unit for the composition of composable multilinear maps. -/
theorem id_comp (F : ComposableMultilinearMap R f φ 1) :
    (ComposableMultilinearMap.id β' R Obj').comp F = F := by
  ext n _ X deg a j hj
  rw [comp_map_v_apply, Finset.sum_eq_single (Composition.single n (NeZero.pos n))
    (fun c _ hc ↦ id_compTerm_eq_zero F a c hc _ _) (fun hn ↦ absurd (Finset.mem_univ _) hn)]
  exact Total.of_inj.1 (total_id_compTerm_single F a _ _ hj)

end IdComp

end ComposableMultilinearMap

end AInfinityTheory
