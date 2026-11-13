/-
Copyright (c) 2026 Marco David. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco David
-/
module

public import AInfinity.AInfinityFunctor
public import AInfinity.ArityLeTwo

/-! # A∞-functors with vanishing higher components

Many A∞-functors between A∞-categories with vanishing higher operations, such as the braiding
functors on KLRW categories, have vanishing components φₙ for n ≥ 3. Such functor data is
determined by a map on objects, a homomorphism of gradings, unary components φ₁ of degree 0 and
binary components φ₂ of degree -1. If the source and the target have vanishing operations mₙ and
m'ₙ for n ≥ 3, the functor equations reduce to four identities, in arities 1, 2, 3 and 4:
* φ₁ commutes with the differentials: φ₁(m₁(a)) = m'₁(φ₁(a));
* φ₁ commutes with the compositions up to the homotopy φ₂:
  (-1)^‖b‖ φ₂(m₁(a), b) + φ₂(a, m₁(b)) + φ₁(m₂(a, b)) = m'₂(φ₁(a), φ₁(b)) + m'₁(φ₂(a, b));
* φ₂ is compatible with the compositions:
  (-1)^‖c‖ φ₂(m₂(a, b), c) + φ₂(a, m₂(b, c)) = m'₂(φ₂(a, b), φ₁(c)) + m'₂(φ₁(a), φ₂(b, c));
* the composite of two binary components vanishes: m'₂(φ₂(a, b), φ₂(c, e)) = 0.
Here ‖b‖ = |b| - 1 is the reduced degree. In arity at least 5, every term of the functor
equation involves an operation or a functor component of arity at least 3, and vanishes.

## Main definitions

* `AInfinityTheory.AInfinityFunctorData.mapOfGradedLinearMap`: a unary functor component from a
  graded linear map of degree `0`.
* `AInfinityTheory.AInfinityFunctorData.mapOfBilinear`: a binary functor component from a family
  of bilinear maps of degree `-1`.
* `AInfinityTheory.AInfinityFunctorData.ofArityLeTwo`: the A∞-functor data with given unary and
  binary components, vanishing in arity at least three.

## Main results

* `AInfinityTheory.AInfinityFunctorData.ofArityLeTwo_mapCompSum_eq_compMapSum`: between A∞-category
  structures with vanishing higher operations, the functor equations for `ofArityLeTwo` hold as
  soon as the four identities above do.
* `AInfinityTheory.AInfinityFunctorData.mapCompSum_eq_zero_of_four_le`,
  `AInfinityTheory.AInfinityFunctorData.compMapSum_eq_zero_of_five_le`: the vanishing of the two
  sides of the functor equation in high arities, for any functor data whose components, and any
  structures whose operations, vanish outside arities 1 and 2.

## Implementation notes

As for `AInfinityCategory.ofArityLeTwo`, the source and the target are the A∞-category structures
built by `AInfinityCategoryStruct.ofArityLeTwo`, whose operations, like those of `ofArityLeTwo`,
read a composable string of objects only at its first few objects. For a concrete index triple
or composition, each surviving term of the functor equations is then definitionally an expression
in the operations and the components, so the four identities are stated in exactly the form
produced by unfolding the functor equations, with all intermediate degrees free and constrained by
equations. Unlike in `AInfinityCategory.ofArityLeTwo`, the identities take every degree equation
as a hypothesis, including those that follow from the others, so that their statements contain no
proofs.

To build an `AInfinityFunctor` between A∞-categories whose instances are definitionally of this
form, such as `AInfinityCategory.ofLinearCategory` and `DGCategory.aInfinityCategory`, use
`ofArityLeTwo` as the functor data and `ofArityLeTwo_mapCompSum_eq_compMapSum` as the proof of the
functor equations.
-/

@[expose] public section

namespace AInfinityTheory

open GradedLinearQuiver

open AInfinityCategoryStruct (m)

variable {β β' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']

namespace AInfinityFunctorData

/-! ### Vanishing terms of the functor equations

If the operations of the source and of the target, and the functor components, all vanish
outside arities 1 and 2, then only a few terms of the functor equations survive: none in arities
at least 5, and only the compositions (2, 1) and (1, 2) of 3 and (2, 2) of 4 on the right-hand
side. -/

section Vanishing

variable {R : Type*} [Semiring R] {Obj Obj' : Type*}
  [AInfinityCategoryStruct β R Obj] [AInfinityCategoryStruct β' R Obj']
  (F : AInfinityFunctorData β β' R Obj Obj')
  (hm : ∀ (k : ℕ) [NeZero k], k ∉ ({1, 2} : Set ℕ) → ∀ X : Fin (k + 1) → Obj,
    m (β := β) (R := R) X = 0)
  (hm' : ∀ (k : ℕ) [NeZero k], k ∉ ({1, 2} : Set ℕ) → ∀ Y : Fin (k + 1) → Obj',
    m (β := β') (R := R) Y = 0)
  (hF : ∀ (k : ℕ) [NeZero k], k ∉ ({1, 2} : Set ℕ) → ∀ X : Fin (k + 1) → Obj, F.map X = 0)

include hm hF in
/-- In arity 3, only the two terms φ₂(m₂(a₁, a₂), a₃) and φ₂(a₁, m₂(a₂, a₃)) of the left-hand
side of the functor equation survive. -/
lemma mapCompSum_arity_three_of_arity_notMem {X : Fin (3 + 1) → Obj} {deg : Fin 3 → β}
    (a : ∀ i : Fin 3, ComposableHom β R X i (deg i)) (d : β) (hd : operationTargetDeg deg = d) :
    F.mapCompSum a d hd =
      (sign (deg 2 - degOne)).toMul • F.mapCompTerm a ⟨0, 2, 1, rfl, one_le_two⟩ d hd +
        F.mapCompTerm a ⟨1, 2, 0, rfl, one_le_two⟩ d hd := by
  have h := fun p hp ↦ F.mapCompTerm_eq_zero_of_arity_notMem a {1, 2} {1, 2} hm hF p hp d hd
  rw [mapCompSum_arity_three, h ⟨0, 1, 2, rfl, le_rfl⟩ (by simp),
    h ⟨1, 1, 1, rfl, le_rfl⟩ (by simp), h ⟨2, 1, 0, rfl, le_rfl⟩ (by simp),
    h ⟨0, 3, 0, rfl, by decide⟩ (by simp)]
  simp only [smul_zero, zero_add, add_zero]

include hm hF in
/-- In arity n ≥ 4, every term of the left-hand side of the functor equation involves a functor
component or an operation of arity at least 3, and vanishes. -/
lemma mapCompSum_eq_zero_of_four_le {n : ℕ} (hn : 4 ≤ n) {X : Fin (n + 1) → Obj}
    {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (d : β)
    (hd : operationTargetDeg deg = d) :
    F.mapCompSum a d hd = 0 :=
  signedStasheffSum_eq_zero fun p ↦ F.mapCompTerm_eq_zero_of_arity_notMem a {1, 2} {1, 2} hm hF p
    (by
      have := p.sum_eq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega) d hd

include hm' hF in
/-- In arity 3, only the two terms m'₂(φ₂(a₁, a₂), φ₁(a₃)) and m'₂(φ₁(a₁), φ₂(a₂, a₃)) of the
right-hand side of the functor equation survive, indexed by the compositions (2, 1) and
(1, 2) of 3. -/
lemma compMapSum_arity_three_of_arity_notMem {X : Fin (3 + 1) → Obj} {deg : Fin 3 → β}
    (a : ∀ i : Fin 3, ComposableHom β R X i (deg i)) (d : β) (hd : operationTargetDeg deg = d) :
    F.compMapSum a d hd =
      F.compMapTerm a ⟨[2, 1], by simp, rfl⟩ d hd +
        F.compMapTerm a ⟨[1, 2], by simp, rfl⟩ d hd := by
  refine Fintype.sum_eq_add _ _ (by decide) fun c ⟨h₁, h₂⟩ ↦
    F.compMapTerm_eq_zero_of_arity_notMem a {1, 2} {1, 2} hm' hF c ?_ d hd
  obtain ⟨blocks, hpos, hsum⟩ := c
  rcases blocks with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
  · simp at hsum
  · simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
    refine Or.inr ⟨⟨0, by simp [Composition.length]⟩, ?_⟩
    show ¬(x = 1 ∨ x = 2)
    omega
  · by_contra! h
    have hx : x = 1 ∨ x = 2 := h.2 ⟨0, by simp [Composition.length]⟩
    have hy : y = 1 ∨ y = 2 := h.2 ⟨1, by simp [Composition.length]⟩
    simp only [List.sum_cons, List.sum_nil] at hsum
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | omega | simp_all
  · exact Or.inl (by simp [Composition.length])

include hm' hF in
/-- In arity 4, only the term m'₂(φ₂(a₁, a₂), φ₂(a₃, a₄)) of the right-hand side of the functor
equation survives, indexed by the composition (2, 2) of 4. -/
lemma compMapSum_arity_four_of_arity_notMem {X : Fin (4 + 1) → Obj} {deg : Fin 4 → β}
    (a : ∀ i : Fin 4, ComposableHom β R X i (deg i)) (d : β) (hd : operationTargetDeg deg = d) :
    F.compMapSum a d hd = F.compMapTerm a ⟨[2, 2], by simp, rfl⟩ d hd := by
  refine Fintype.sum_eq_single _ fun c hc ↦
    F.compMapTerm_eq_zero_of_arity_notMem a {1, 2} {1, 2} hm' hF c ?_ d hd
  obtain ⟨blocks, hpos, hsum⟩ := c
  rcases blocks with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
  · simp at hsum
  · simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
    refine Or.inr ⟨⟨0, by simp [Composition.length]⟩, ?_⟩
    show ¬(x = 1 ∨ x = 2)
    omega
  · by_contra! h
    have hx : x = 1 ∨ x = 2 := h.2 ⟨0, by simp [Composition.length]⟩
    have hy : y = 1 ∨ y = 2 := h.2 ⟨1, by simp [Composition.length]⟩
    simp only [List.sum_cons, List.sum_nil] at hsum
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | omega | simp_all
  · exact Or.inl (by simp [Composition.length])

include hm' hF in
/-- In arity n ≥ 5, every term of the right-hand side of the functor equation involves a functor
component or an operation of arity at least 3, and vanishes. -/
lemma compMapSum_eq_zero_of_five_le {n : ℕ} [NeZero n] (hn : 5 ≤ n) {X : Fin (n + 1) → Obj}
    {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (d : β)
    (hd : operationTargetDeg deg = d) :
    F.compMapSum a d hd = 0 := by
  refine Finset.sum_eq_zero fun c _ ↦
    F.compMapTerm_eq_zero_of_arity_notMem a {1, 2} {1, 2} hm' hF c ?_ d hd
  obtain ⟨blocks, hpos, hsum⟩ := c
  rcases blocks with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
  · simp at hsum
    omega
  · simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
    refine Or.inr ⟨⟨0, by simp [Composition.length]⟩, ?_⟩
    show ¬(x = 1 ∨ x = 2)
    omega
  · by_contra! h
    have hx : x = 1 ∨ x = 2 := h.2 ⟨0, by simp [Composition.length]⟩
    have hy : y = 1 ∨ y = 2 := h.2 ⟨1, by simp [Composition.length]⟩
    simp only [List.sum_cons, List.sum_nil] at hsum
    omega
  · exact Or.inl (by simp [Composition.length])

end Vanishing

variable {R : Type*} [CommSemiring R] {Obj Obj' : Type*}
  [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj']

variable (obj : Obj → Obj') (degMap : β →+ᵍ β')

/-- The unary functor component given by a graded linear map `φ` of degree `0`, from the
morphisms from `X 0` to `X 1` to the morphisms from `obj (X 0)` to `obj (X 1)` in the translated
degrees. -/
def mapOfGradedLinearMap {X : Fin (1 + 1) → Obj}
    (φ : GradedLinearMap R (X 0 →ᵍ[R, β] X 1) (fun b ↦ (obj (X 0) →ᵍ[R] obj (X 1)) (degMap b)) 0) :
    GradedMultilinearMap R (ComposableHom β R X)
      (fun b : β ↦ (obj (X 0) →ᵍ[R] obj (X (Fin.last 1))) (degMap b)) ((1 - 1 : ℤ) • degOne) :=
  .mk fun deg j h ↦ MultilinearMap.ofSubsingletonₗ' 0 (φ.v (deg 0) j (by simpa using h))

/-- The binary functor component given by a family of bilinear maps `φ p q j`, sending morphisms
of degrees `p` and `q` to a morphism of degree `j = p + q - 1` in the translated degrees. -/
def mapOfBilinear {X : Fin (2 + 1) → Obj}
    (φ : ∀ p q j : β, p + q - degOne = j →
      (X 0 →ᵍ[R] X 1) p →ₗ[R] (X 1 →ᵍ[R] X 2) q →ₗ[R] (obj (X 0) →ᵍ[R] obj (X 2)) (degMap j)) :
    GradedMultilinearMap R (ComposableHom β R X)
      (fun b : β ↦ (obj (X 0) →ᵍ[R] obj (X (Fin.last 2))) (degMap b)) ((1 - 2 : ℤ) • degOne) :=
  .mk fun deg j h ↦ LinearMap.uncurryFinTwo (φ (deg 0) (deg 1) j (by
    rw [← h, Fin.sum_univ_two]
    module))

variable (φ₁ : ∀ X Y : Obj,
    GradedLinearMap R (X →ᵍ[R, β] Y) (fun b ↦ (obj X →ᵍ[R] obj Y) (degMap b)) 0)
  (φ₂ : ∀ (X Y Z : Obj) (p q j : β), p + q - degOne = j →
    (X →ᵍ[R] Y) p →ₗ[R] (Y →ᵍ[R] Z) q →ₗ[R] (obj X →ᵍ[R] obj Z) (degMap j))

/-- The functor components with unary components `φ₁` and binary components `φ₂`, vanishing in
every arity `n ≥ 3`. -/
def mapOfArityLeTwo {n : ℕ} [NeZero n] (X : Fin (n + 1) → Obj) :
    GradedMultilinearMap R (ComposableHom β R X)
      (fun b : β ↦ (obj (X 0) →ᵍ[R] obj (X (Fin.last n))) (degMap b)) ((1 - n : ℤ) • degOne) :=
  match n with
    | 1 => mapOfGradedLinearMap obj degMap (φ₁ (X 0) (X 1))
    | 2 => mapOfBilinear obj degMap (φ₂ (X 0) (X 1) (X 2))
    | _ => 0

/-- The A∞-functor data with map on objects `obj`, grading homomorphism `degMap`, unary
components `φ₁`, binary components `φ₂`, and vanishing components in every arity `n ≥ 3`. -/
abbrev ofArityLeTwo : AInfinityFunctorData β β' R Obj Obj' where
  obj := obj
  degMap := degMap
  map := mapOfArityLeTwo obj degMap φ₁ φ₂

lemma ofArityLeTwo_map_eq_zero {n : ℕ} [NeZero n] (hn : n ∉ ({1, 2} : Set ℕ))
    (X : Fin (n + 1) → Obj) : (ofArityLeTwo obj degMap φ₁ φ₂).map X = 0 := by
  change mapOfArityLeTwo obj degMap φ₁ φ₂ X = 0
  unfold mapOfArityLeTwo
  split <;> simp_all

/-! ### The functor equations

When the source and the target are A∞-category structures with vanishing higher operations, as
built by `AInfinityCategoryStruct.ofArityLeTwo`, the functor equations for `ofArityLeTwo` reduce
to four identities, in arities 1, 2, 3 and 4. They are stated below with all intermediate degrees
free and constrained by equations, in exactly the form produced by unfolding the functor
equations, so that they apply without any transport. -/

section Equations

variable (f : ∀ X Y : Obj, GradedLinearMap R (X →ᵍ[R, β] Y) (X →ᵍ[R] Y) degOne)
  (g : ∀ (X Y Z : Obj) (p q i : β), p + q = i →
    (X →ᵍ[R, β] Y) p →ₗ[R] (Y →ᵍ[R] Z) q →ₗ[R] (X →ᵍ[R] Z) i)
  (f' : ∀ X Y : Obj', GradedLinearMap R (X →ᵍ[R, β'] Y) (X →ᵍ[R] Y) degOne)
  (g' : ∀ (X Y Z : Obj') (p q i : β'), p + q = i →
    (X →ᵍ[R, β'] Y) p →ₗ[R] (Y →ᵍ[R] Z) q →ₗ[R] (X →ᵍ[R] Z) i)

/-- The functor equations for the A∞-functor data `ofArityLeTwo obj degMap φ₁ φ₂` between
A∞-category structures with vanishing higher operations hold as soon as they hold in arities
1, 2, 3 and 4. -/
theorem ofArityLeTwo_mapCompSum_eq_compMapSum
    -- Arity 1: the unary components commute with the differentials.
    (map_differential : ∀ (X Y : Obj) {p e b d : β} (h₁ : p + degOne = e) (h₂ : e + 0 = d)
      (h₃ : p + 0 = b) (h₄ : degMap b + degOne = degMap d) (a : (X →ᵍ[R] Y) p),
      (φ₁ X Y).v e d h₂ ((f X Y).v p e h₁ a) =
        (f' (obj X) (obj Y)).v (degMap b) (degMap d) h₄ ((φ₁ X Y).v p b h₃ a))
    -- Arity 2: the unary components commute with the compositions, up to the homotopy given by
    -- the binary components.
    (map_composition : ∀ (X Y Z : Obj) {p q p' q' e d b₁ b₂ j : β} (hp : p + degOne = p')
      (hq : q + degOne = q') (h : p + q = e) (h₁ : p' + q - degOne = d)
      (h₂ : p + q' - degOne = d) (he : e + 0 = d) (hb₁ : p + 0 = b₁) (hb₂ : q + 0 = b₂)
      (hj : p + q - degOne = j) (h₃ : degMap b₁ + degMap b₂ = degMap d)
      (h₄ : degMap j + degOne = degMap d) (a : (X →ᵍ[R] Y) p) (b : (Y →ᵍ[R] Z) q),
      (sign (q - degOne)).toMul • φ₂ X Y Z p' q d h₁ ((f X Y).v p p' hp a) b +
          φ₂ X Y Z p q' d h₂ a ((f Y Z).v q q' hq b) + (φ₁ X Z).v e d he (g X Y Z p q e h a b) =
        g' (obj X) (obj Y) (obj Z) (degMap b₁) (degMap b₂) (degMap d) h₃ ((φ₁ X Y).v p b₁ hb₁ a)
            ((φ₁ Y Z).v q b₂ hb₂ b) +
          (f' (obj X) (obj Z)).v (degMap j) (degMap d) h₄ (φ₂ X Y Z p q j hj a b))
    -- Arity 3: the binary components are compatible with the compositions.
    (map_composition_composition : ∀ (W X Y Z : Obj) {p q r e e' d j j' b₁ b₃ : β}
      (h : p + q = e) (h' : q + r = e') (h₁ : e + r - degOne = d) (h₂ : p + e' - degOne = d)
      (hj : p + q - degOne = j) (hj' : q + r - degOne = j') (hb₁ : p + 0 = b₁) (hb₃ : r + 0 = b₃)
      (h₃ : degMap j + degMap b₃ = degMap d) (h₄ : degMap b₁ + degMap j' = degMap d)
      (a : (W →ᵍ[R] X) p) (b : (X →ᵍ[R] Y) q) (c : (Y →ᵍ[R] Z) r),
      (sign (r - degOne)).toMul • φ₂ W Y Z e r d h₁ (g W X Y p q e h a b) c +
          φ₂ W X Z p e' d h₂ a (g X Y Z q r e' h' b c) =
        g' (obj W) (obj Y) (obj Z) (degMap j) (degMap b₃) (degMap d) h₃ (φ₂ W X Y p q j hj a b)
            ((φ₁ Y Z).v r b₃ hb₃ c) +
          g' (obj W) (obj X) (obj Z) (degMap b₁) (degMap j') (degMap d) h₄ ((φ₁ W X).v p b₁ hb₁ a)
            (φ₂ X Y Z q r j' hj' b c))
    -- Arity 4: the composite of two binary components vanishes.
    (composition_map_map : ∀ (V W X Y Z : Obj) {p q r s j j' d : β} (hj : p + q - degOne = j)
      (hj' : r + s - degOne = j') (h : degMap j + degMap j' = degMap d) (a : (V →ᵍ[R] W) p)
      (b : (W →ᵍ[R] X) q) (c : (X →ᵍ[R] Y) r) (e : (Y →ᵍ[R] Z) s),
      g' (obj V) (obj X) (obj Z) (degMap j) (degMap j') (degMap d) h (φ₂ V W X p q j hj a b)
        (φ₂ X Y Z r s j' hj' c e) = 0)
    {n : ℕ} [NeZero n] {X : Fin (n + 1) → Obj} {deg : Fin n → β}
    (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) {d : β} (hd : operationTargetDeg deg = d) :
    letI := AInfinityCategoryStruct.ofArityLeTwo f g
    letI := AInfinityCategoryStruct.ofArityLeTwo f' g'
    (ofArityLeTwo obj degMap φ₁ φ₂).mapCompSum a d hd =
      (ofArityLeTwo obj degMap φ₁ φ₂).compMapSum a d hd := by
  let := AInfinityCategoryStruct.ofArityLeTwo f g
  let := AInfinityCategoryStruct.ofArityLeTwo f' g'
  have hm := fun (k : ℕ) [NeZero k] hk X ↦ AInfinityCategoryStruct.ofArityLeTwo.m_eq_zero
    (β := β) (R := R) f g (k := k) hk X
  have hm' := fun (k : ℕ) [NeZero k] hk Y ↦ AInfinityCategoryStruct.ofArityLeTwo.m_eq_zero
    (β := β') (R := R) f' g' (k := k) hk Y
  have hF := fun (k : ℕ) [NeZero k] hk X ↦ ofArityLeTwo_map_eq_zero obj degMap φ₁ φ₂ (n := k) hk X
  rcases n with _ | _ | _ | _ | _ | n
  · exact absurd rfl (NeZero.ne 0)
  · rw [mapCompSum_arity_one, compMapSum_arity_one]
    exact map_differential (X 0) (X 1) _ _ _ _ (a 0)
  · rw [mapCompSum_arity_two, compMapSum_arity_two]
    exact map_composition (X 0) (X 1) (X 2) _ _ _ _ _ _ _ _ _ _ _ (a 0) (a 1)
  · rw [mapCompSum_arity_three_of_arity_notMem _ hm hF,
      compMapSum_arity_three_of_arity_notMem _ hm' hF]
    exact map_composition_composition (X 0) (X 1) (X 2) (X 3) _ _ _ _ _ _ _ _ _ _ (a 0) (a 1) (a 2)
  · rw [mapCompSum_eq_zero_of_four_le _ hm hF le_rfl,
      compMapSum_arity_four_of_arity_notMem _ hm' hF]
    exact (composition_map_map (X 0) (X 1) (X 2) (X 3) (X 4) _ _ _ (a 0) (a 1) (a 2) (a 3)).symm
  · rw [mapCompSum_eq_zero_of_four_le _ hm hF (by omega),
      compMapSum_eq_zero_of_five_le _ hm' hF (by omega)]

end Equations

end AInfinityFunctorData

end AInfinityTheory
