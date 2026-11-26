/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi, Marco David
-/
module

public import AInfinity.CompositionGather
public import AInfinity.FunctorComposition.Defs

/-! # Associativity of the composition of composable multilinear maps

This file proves the three rules relating the composites Φ ∘ F (`ComposableMultilinearMap.comp`)
and Φ ∘ (F | D) (`ComposableMultilinearMap.compMarked`), for an arbitrary composable multilinear
map Φ:

* (AS) `(Φ ∘ G) ∘ F = Φ ∘ (G ∘ F)` (`ComposableMultilinearMap.comp_assoc`);
* (L) `(Φ ∘ (G | E)) ∘ F = Φ ∘ (G ∘ F | E ∘ F)` (`ComposableMultilinearMap.compMarked_comp`);
* (R) `(Φ ∘ G) ∘ (F | D) = Φ ∘ (G ∘ F | G ∘ (F | D))`
  (`ComposableMultilinearMap.comp_compMarked`).

The rules (L) and (R) are the derivatives of (AS) in its middle and in its inner argument: they
are the coefficients of ε in (AS) for G + εE and for F + εD. All three are sums of one identity
between terms
$$\Phi_k(Q_1(P(\dots), \dots, P(\dots)), \dots, Q_k(P(\dots), \dots, P(\dots)))$$
with three levels, for arbitrary choices `Q` and `P` of the middle and of the innermost maps. Such
a term is described either by a composition c of `n` and a composition of `c.length`
(`groupedTerm`), or by a composition of `n` and a composition of each of its blocks
(`blockwiseTerm`). Mathlib's `Composition.sigmaEquivSigmaPi` matches the two descriptions.

Two cases are used in `AInfinity.FunctorComposition.Basic`: for A∞-functor data Φ, (AS) is the
associativity of the composition of A∞-functors; and (AS), (L) and (R), together with the unit
laws of `AInfinity.ComposableMultilinearMap`, show that the composite of two A∞-functors satisfies
the A∞-functor equations.

## Main definitions

* `AInfinityTheory.ComposableMultilinearMap.blockCompTerm`: a term E(P, …, P) on a block of a
  composition.
* `AInfinityTheory.ComposableMultilinearMap.groupedTerm`,
  `AInfinityTheory.ComposableMultilinearMap.blockwiseTerm`: the two descriptions of a term with
  three levels.

## Main results

* `AInfinityTheory.ComposableMultilinearMap.groupedTerm_eq_blockwiseTerm`: the two descriptions
  of a term agree.
* `AInfinityTheory.ComposableMultilinearMap.comp_assoc`,
  `AInfinityTheory.ComposableMultilinearMap.compMarked_comp`,
  `AInfinityTheory.ComposableMultilinearMap.comp_compMarked`: the rules (AS), (L) and (R).

## Implementation notes

The two descriptions of a term are compared in the type `GradedLinearQuiver.Total` of all
morphisms, in which a morphism is bundled with its source, target and degree. There, transports
are invisible, and the congruence `ComposableMultilinearMap.total_map_congr` only compares arities
and inputs. The comparison descends through the three levels to one equality of positions of
inputs, `Composition.gather_embedding_sigmaCompositionAux_embedding`. No equality of objects or of
degrees is stated.

Each rule is first proved as an equality of sums of terms in an arbitrary degree `d`
(`sum_compTerm_comp`, `sum_compTerm_compMarked`, `sum_compTerm_comp_pick`). The two sides of a
rule are composable multilinear maps over `(χ.comp ψ).comp φ` and over `χ.comp (ψ.comp φ)`: these
are equal by `rfl`, but not syntactically, and sums in the two hom spaces cannot be manipulated
together.

In (L), the marked block of the composition of `c.length` corresponds to a marked block of
`c.gather c'`. In (R), the marked block of `c` corresponds, under `Composition.blocksFinEquiv`, to
a marked block of `c.gather c'` and a marked block of the composition of that block; the Koszul
sign splits accordingly (`tailSign_sizeUpTo_embedding_succ`, in
`AInfinity.FunctorComposition.Signs`).
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

open GradedLinearQuiver

variable {n : ℕ}

namespace ComposableMultilinearMap

variable {β β' β'' β''' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] [AddCommGroup β'''] [Grading β'''] {R : Type*} [Semiring R]
  {Obj Obj' Obj'' Obj''' : Type*} [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj']
  [GradedLinearQuiver β'' R Obj''] [GradedLinearQuiver β''' R Obj''']
  {f : Obj → Obj'} {φ : β →+ᵍ β'} {g : Obj' → Obj''} {ψ : β' →+ᵍ β''} {h : Obj'' → Obj'''}
  {χ : β'' →+ᵍ β'''} {s t u : ℤ}

/-! ### Terms with three levels -/

section Terms

variable {X : Fin (n + 1) → Obj} {deg : Fin n → β}

/-- The term E_k(P₁(…), …, P_k(…)) on the `l`-th block of a composition `e` of `n`, indexed by a
composition `τ` of that block into k blocks and a choice `P` of a composable multilinear map for
each of them, as the `l`-th input of an outer map, in any degree `d` equal to its degree. -/
def blockCompTerm (E : ComposableMultilinearMap R g ψ t)
    (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (e : Composition n) (l : Fin e.length)
    (τ : Composition (e.blocksFun l))
    (P : Fin τ.length → Σ u : ℤ, ComposableMultilinearMap R f φ u) (d : β'')
    (hd : ψ (targetDeg t fun q ↦
      φ (targetDeg (P q).1 fun i ↦ deg (e.embedding l (τ.embedding q i)))) = d) :
    ComposableHom β'' R (fun k ↦ g (f (X (e.boundary k)))) l d :=
  homCongr R (congrArg (fun Z ↦ g (f Z)) (e.blockObj_zero X l))
    (congrArg (fun Z ↦ g (f Z)) (e.blockObj_last X l)) rfl
    (E.compTerm (X := e.blockObj X l) (deg := fun i ↦ deg (e.embedding l i))
      (fun i ↦ a (e.embedding l i)) τ P d hd)

variable [NeZero n]

/-- The term Φ(Q₁(P(…), …, P(…)), …, Q_k(P(…), …, P(…))) described by a composition `c` of `n`
into the inputs of the innermost maps, chosen by `P`, and a composition `c'` of `c.length` into
the inputs of the middle maps, chosen by `Q`. -/
def groupedTerm (Φ : ComposableMultilinearMap R h χ s)
    (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (c : Composition n)
    (c' : Composition c.length) (P : Fin c.length → Σ u : ℤ, ComposableMultilinearMap R f φ u)
    (Q : Fin c'.length → Σ u : ℤ, ComposableMultilinearMap R g ψ u) (d₀ : β''')
    (hd₀ : χ (targetDeg s fun l ↦ ψ (targetDeg (Q l).1 fun q ↦
      φ (targetDeg (P (c'.embedding l q)).1 fun i ↦
        deg (c.embedding (c'.embedding l q) i)))) = d₀) (d : β''') (hd : d₀ = d) :
    (h (g (f (X 0))) →ᵍ[R] h (g (f (X (Fin.last n))))) d :=
  homCongr R (congrArg (fun k ↦ h (g (f (X k)))) c.boundary_zero)
    (congrArg (fun k ↦ h (g (f (X k)))) c.boundary_last) hd
    (Φ.compTerm (X := fun k ↦ f (X (c.boundary k))) (fun l ↦ (P l).2.blockMap a c l) c' Q d₀ hd₀)

/-- The term Φ(Q₁(P(…), …, P(…)), …, Q_k(P(…), …, P(…))) described by a composition `e` of `n`
into the inputs of the middle maps, chosen by `Q`, and a composition `τ l` of each of its blocks
into the inputs of the innermost maps, chosen by `P`. -/
def blockwiseTerm (Φ : ComposableMultilinearMap R h χ s)
    (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (e : Composition n)
    (τ : ∀ l : Fin e.length, Composition (e.blocksFun l))
    (P : ∀ l, Fin (τ l).length → Σ u : ℤ, ComposableMultilinearMap R f φ u)
    (Q : Fin e.length → Σ u : ℤ, ComposableMultilinearMap R g ψ u) (dl : Fin e.length → β'')
    (hdl : ∀ l, ψ (targetDeg (Q l).1 fun q ↦
      φ (targetDeg (P l q).1 fun i ↦ deg (e.embedding l ((τ l).embedding q i)))) = dl l)
    (d : β''') (hd : χ (targetDeg s dl) = d) :
    (h (g (f (X 0))) →ᵍ[R] h (g (f (X (Fin.last n))))) d :=
  Φ.applyBlocks (fun Z ↦ g (f Z)) X e
    (fun l ↦ (Q l).2.blockCompTerm a e l (τ l) (P l) (dl l) (hdl l)) d hd

end Terms

/-! ### Matching the two descriptions of a term -/

section Total

variable {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))
  (c : Composition n) (c' : Composition c.length)

/-- The value of `D` on a block of `c`, inside the `l`-th group of blocks given by `c'`, is its
value on the corresponding block of `c.sigmaCompositionAux c'`, inside the `l`-th block of
`c.gather c'`. -/
lemma total_blockMap_embedding (D : ComposableMultilinearMap R f φ t) (l : Fin c'.length)
    (q : Fin (c'.blocksFun l)) :
    Total.of (D.blockMap a c (c'.embedding l q)) =
      Total.of (D.blockMap
        (X := (c.gather c').blockObj X (l.cast (c.length_gather c').symm))
        (fun i ↦ a ((c.gather c').embedding (l.cast (c.length_gather c').symm) i))
        (c.sigmaCompositionAux c' (l.cast (c.length_gather c').symm))
        (q.cast (c.length_sigmaCompositionAux c' l).symm)) := by
  simp only [blockMap, Total.of_homCongr]
  exact D.total_map_congr (c.blocksFun_sigmaCompositionAux c' l q).symm _ _ fun s ↦
    congrArg (fun i ↦ Total.of (a i))
      (c.gather_embedding_sigmaCompositionAux_embedding c' l q s).symm

/-- The value of `E` on the values of the maps chosen by `P` on the `l`-th group, given by `c'`,
of blocks of `c` is a term on the `l`-th block of `c.gather c'`. -/
lemma total_blockMap_blockMap (E : ComposableMultilinearMap R g ψ t)
    (P : Fin c.length → Σ u : ℤ, ComposableMultilinearMap R f φ u) (l : Fin c'.length)
    (d : β'') (hd : _) :
    Total.of (E.blockMap (fun l ↦ (P l).2.blockMap a c l) c' l) =
      Total.of (E.blockCompTerm a (c.gather c') (l.cast (c.length_gather c').symm)
        (c.sigmaCompositionAux c' (l.cast (c.length_gather c').symm))
        (fun q ↦ P (c'.embedding l (q.cast (c.length_sigmaCompositionAux c' l)))) d hd) := by
  simp only [blockMap, blockCompTerm, compTerm, applyBlocks, Total.of_homCongr]
  refine E.total_map_congr (c.length_sigmaCompositionAux c' l).symm _ _ fun q ↦ ?_
  exact total_blockMap_embedding a c c' (P (c'.embedding l q)).2 l q

variable [NeZero n]

/-- The two descriptions of a term Φ(Q(P, …, P), …, Q(P, …, P)) agree: the term described by `c`
and `c'` is the term described by the image `c.gather c'` and `c.sigmaCompositionAux c'` of
`(c, c')` under `Composition.sigmaEquivSigmaPi`. -/
theorem total_groupedTerm (Φ : ComposableMultilinearMap R h χ s)
    (P : Fin c.length → Σ u : ℤ, ComposableMultilinearMap R f φ u)
    (Q : Fin c'.length → Σ u : ℤ, ComposableMultilinearMap R g ψ u) (d₀ : β''') (hd₀ : _)
    (d : β''') (hd : d₀ = d) (dl : Fin (c.gather c').length → β'') (hdl : _) (d' : β''')
    (hd' : _) :
    Total.of (Φ.groupedTerm a c c' P Q d₀ hd₀ d hd) =
      Total.of (Φ.blockwiseTerm a (c.gather c') (c.sigmaCompositionAux c')
        (fun l q ↦ P (c'.embedding (l.cast (c.length_gather c'))
          (q.cast (c.length_sigmaCompositionAux c' (l.cast (c.length_gather c'))))))
        (fun l ↦ Q (l.cast (c.length_gather c'))) dl hdl d' hd') := by
  simp only [groupedTerm, blockwiseTerm, compTerm, applyBlocks, Total.of_homCongr]
  refine Φ.total_map_congr (c.length_gather c').symm _ _ fun l ↦ ?_
  exact total_blockMap_blockMap a c c' (Q l).2 P l _ _

/-- The two descriptions of a term Φ(Q(P, …, P), …, Q(P, …, P)) agree. -/
theorem groupedTerm_eq_blockwiseTerm (Φ : ComposableMultilinearMap R h χ s)
    (P : Fin c.length → Σ u : ℤ, ComposableMultilinearMap R f φ u)
    (Q : Fin c'.length → Σ u : ℤ, ComposableMultilinearMap R g ψ u) (d₀ : β''') (hd₀ : _)
    (d : β''') (hd : d₀ = d) (dl : Fin (c.gather c').length → β'') (hdl : _) (hd' : _) :
    Φ.groupedTerm a c c' P Q d₀ hd₀ d hd =
      Φ.blockwiseTerm a (c.gather c') (c.sigmaCompositionAux c')
        (fun l q ↦ P (c'.embedding (l.cast (c.length_gather c'))
          (q.cast (c.length_sigmaCompositionAux c' (l.cast (c.length_gather c'))))))
        (fun l ↦ Q (l.cast (c.length_gather c'))) dl hdl d hd' :=
  Total.of_inj.1 (total_groupedTerm a c c' Φ P Q d₀ hd₀ d hd dl hdl d hd')

end Total

/-! ### Expanding composites into terms -/

section Expand

variable {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

lemma compTerm_congr [NeZero n] (Φ : ComposableMultilinearMap R g ψ s) (c : Composition n)
    {P P' : Fin c.length → Σ u : ℤ, ComposableMultilinearMap R f φ u} (hP : P = P') (d : β'')
    (hd : _) : Φ.compTerm a c P d hd = Φ.compTerm a c P' d (hP ▸ hd) := by
  subst hP
  rfl

lemma blockwiseTerm_congr [NeZero n] (Φ : ComposableMultilinearMap R h χ s) (e : Composition n)
    (τ : ∀ l : Fin e.length, Composition (e.blocksFun l))
    {P P' : ∀ l, Fin (τ l).length → Σ u : ℤ, ComposableMultilinearMap R f φ u} (hP : P = P')
    {Q Q' : Fin e.length → Σ u : ℤ, ComposableMultilinearMap R g ψ u} (hQ : Q = Q')
    (dl : Fin e.length → β'') (hdl : _) (d : β''') (hd : _) :
    Φ.blockwiseTerm a e τ P Q dl hdl d hd =
      Φ.blockwiseTerm a e τ P' Q' dl (hP ▸ hQ ▸ hdl) d hd := by
  subst hP hQ
  rfl

lemma blockCompTerm_congr (E : ComposableMultilinearMap R g ψ t) (e : Composition n)
    (l : Fin e.length) (τ : Composition (e.blocksFun l))
    {P P' : Fin τ.length → Σ u : ℤ, ComposableMultilinearMap R f φ u} (hP : P = P') (d : β'')
    (hd : _) : E.blockCompTerm a e l τ P d hd = E.blockCompTerm a e l τ P' d (hP ▸ hd) := by
  subst hP
  rfl

/-- The value of E ∘ F on a block of a composition `e` of `n`, as a sum over the compositions of
that block. -/
lemma blockMap_comp (E : ComposableMultilinearMap R g ψ t) (F : ComposableMultilinearMap R f φ 1)
    (e : Composition n) (l : Fin e.length) :
    (E.comp F).blockMap a e l =
      ∑ τ : Composition (e.blocksFun l), E.blockCompTerm a e l τ (fun _ ↦ ⟨1, F⟩) _
        (comp_deg φ ψ (fun i ↦ deg (e.embedding l i)) τ rfl) :=
  (congrArg (homCongr R (congrArg (fun Z ↦ g (f Z)) (e.blockObj_zero X l))
    (congrArg (fun Z ↦ g (f Z)) (e.blockObj_last X l)) rfl)
    (comp_map_v_apply E F (X := e.blockObj X l) (deg := fun i ↦ deg (e.embedding l i))
      (fun i ↦ a (e.embedding l i)) rfl)).trans (map_sum _ _ _)

/-- The value of Φ ∘ (F | D) on a block of a composition `e` of `n`, as a signed sum over the
compositions of that block with one marked block. -/
lemma blockMap_compMarked (Φ : ComposableMultilinearMap R g ψ s)
    (F : ComposableMultilinearMap R f φ 1) (D : ComposableMultilinearMap R f φ 2)
    (hu : s + 1 = u) (e : Composition n) (l : Fin e.length) :
    (Φ.compMarked F D hu).blockMap a e l =
      ∑ τ : Composition (e.blocksFun l), ∑ q : Fin τ.length,
        tailSign (fun i ↦ deg (e.embedding l i)) (τ.sizeUpTo (q + 1)) •
          Φ.blockCompTerm a e l τ (fun q₀ ↦ pick F D (decide (q₀ = q))) _
            (compMarked_deg F D (fun i ↦ deg (e.embedding l i)) τ q hu rfl) := by
  refine (congrArg (homCongr R (congrArg (fun Z ↦ g (f Z)) (e.blockObj_zero X l))
    (congrArg (fun Z ↦ g (f Z)) (e.blockObj_last X l)) rfl)
    (compMarked_map_v_apply Φ F D (X := e.blockObj X l)
      (deg := fun i ↦ deg (e.embedding l i)) (fun i ↦ a (e.embedding l i)) hu rfl)).trans ?_
  simp only [map_sum, Units.smul_def, map_zsmul]
  rfl

variable [NeZero n]

/-- A term of (Φ ∘ G) ∘ P, as a sum over the compositions of its number of blocks. -/
lemma compTerm_comp (Φ : ComposableMultilinearMap R h χ s) (G : ComposableMultilinearMap R g ψ 1)
    (c : Composition n) (P : Fin c.length → Σ u : ℤ, ComposableMultilinearMap R f φ u)
    (d : β''') (hd : _) :
    (Φ.comp G).compTerm a c P d hd =
      ∑ c' : Composition c.length, Φ.groupedTerm a c c' P (fun _ ↦ ⟨1, G⟩) _
        (comp_deg ψ χ (fun l ↦ φ (targetDeg (P l).1 fun i ↦ deg (c.embedding l i))) c' rfl)
        d hd :=
  (congrArg (homCongr R (congrArg (fun k ↦ h (g (f (X k)))) c.boundary_zero)
    (congrArg (fun k ↦ h (g (f (X k)))) c.boundary_last) hd)
    (comp_map_v_apply Φ G (X := fun k ↦ f (X (c.boundary k)))
      (fun l ↦ (P l).2.blockMap a c l) rfl)).trans (map_sum _ _ _)

/-- A term of (Φ ∘ (G | E)) ∘ P, as a signed sum over the compositions of its number of blocks
with one marked block. -/
lemma compTerm_compMarked (Φ : ComposableMultilinearMap R h χ s)
    (G : ComposableMultilinearMap R g ψ 1) (E : ComposableMultilinearMap R g ψ 2)
    (hu : s + 1 = u) (c : Composition n)
    (P : Fin c.length → Σ u : ℤ, ComposableMultilinearMap R f φ u) (d : β''') (hd : _) :
    (Φ.compMarked G E hu).compTerm a c P d hd =
      ∑ c' : Composition c.length, ∑ m : Fin c'.length,
        tailSign (fun l ↦ φ (targetDeg (P l).1 fun i ↦ deg (c.embedding l i)))
            (c'.sizeUpTo (m + 1)) •
          Φ.groupedTerm a c c' P (fun l ↦ pick G E (decide (l = m))) _
            (compMarked_deg G E (fun l ↦ φ (targetDeg (P l).1 fun i ↦ deg (c.embedding l i)))
              c' m hu rfl) d hd := by
  refine (congrArg (homCongr R (congrArg (fun k ↦ h (g (f (X k)))) c.boundary_zero)
    (congrArg (fun k ↦ h (g (f (X k)))) c.boundary_last) hd)
    (compMarked_map_v_apply Φ G E (X := fun k ↦ f (X (c.boundary k)))
      (fun l ↦ (P l).2.blockMap a c l) hu rfl)).trans ?_
  simp only [map_sum, Units.smul_def, map_zsmul]
  rfl

/-- A term of Φ ∘ (Q ∘ F), as a sum over the compositions of its blocks. -/
lemma compTerm_comp_right (Φ : ComposableMultilinearMap R h χ s)
    (F : ComposableMultilinearMap R f φ 1) (e : Composition n)
    (Q : Fin e.length → Σ u : ℤ, ComposableMultilinearMap R g ψ u) (d : β''') (hd : _) :
    Φ.compTerm a e (fun l ↦ ⟨(Q l).1, (Q l).2.comp F⟩) d hd =
      ∑ τ : ∀ l : Fin e.length, Composition (e.blocksFun l),
        Φ.blockwiseTerm a e τ (fun _ _ ↦ ⟨1, F⟩) Q
          (fun l ↦ (ψ.comp φ) (targetDeg (Q l).1 fun i ↦ deg (e.embedding l i)))
          (fun l ↦ comp_deg φ ψ (fun i ↦ deg (e.embedding l i)) (τ l) rfl) d hd := by
  simp only [compTerm, applyBlocks, blockMap_comp, MultilinearMap.map_sum, map_sum]
  rfl

end Expand

/-! ### The associativity of the composition -/

section Assoc

variable (Φ : ComposableMultilinearMap R h χ s) (G : ComposableMultilinearMap R g ψ 1)
  (F : ComposableMultilinearMap R f φ 1)

/-- The terms of (Φ ∘ G) ∘ F and of Φ ∘ (G ∘ F) are the same, reindexed along
`Composition.sigmaEquivSigmaPi`. -/
lemma sum_compTerm_comp [NeZero n] {X : Fin (n + 1) → Obj} {deg : Fin n → β}
    (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (d : β''') (hd : ∀ _ : Composition n, _)
    (hd' : ∀ _ : Composition n, _) :
    ∑ c : Composition n, (Φ.comp G).compTerm a c (fun _ ↦ ⟨1, F⟩) d (hd c) =
      ∑ e : Composition n, Φ.compTerm a e (fun _ ↦ ⟨1, G.comp F⟩) d (hd' e) := by
  refine (Finset.sum_congr rfl fun c _ ↦ compTerm_comp a Φ G c _ _ _).trans ?_
  refine Eq.trans ?_ (Finset.sum_congr rfl fun e _ ↦
    (compTerm_comp_right a Φ F e (fun _ ↦ ⟨1, G⟩) _ _).symm)
  rw [Finset.sum_sigma', Finset.sum_sigma', Finset.univ_sigma_univ, Finset.univ_sigma_univ]
  exact Fintype.sum_equiv (Composition.sigmaEquivSigmaPi n) _ _ fun σ ↦
    groupedTerm_eq_blockwiseTerm a σ.1 σ.2 Φ _ _ _ _ _ _ _ _ _

/-- (AS): the composition of composable multilinear maps is associative. -/
theorem comp_assoc : (Φ.comp G).comp F = Φ.comp (G.comp F) := by
  ext n _ X deg a j hj
  exact (comp_map_v_apply _ F a hj).trans ((sum_compTerm_comp Φ G F a _ _ _).trans
    (comp_map_v_apply Φ (G.comp F) a hj).symm)

end Assoc

/-! ### Composing a marked composite with a map on the right -/

section MarkedLeft

variable (Φ : ComposableMultilinearMap R h χ s) (G : ComposableMultilinearMap R g ψ 1)
  (E : ComposableMultilinearMap R g ψ 2) (F : ComposableMultilinearMap R f φ 1)

omit [GradedLinearQuiver β''' R Obj'''] in
lemma pick_comp (b : Bool) :
    pick (G.comp F) (E.comp F) b = ⟨(pick G E b).1, (pick G E b).2.comp F⟩ := by
  cases b <;> rfl

omit [GradedLinearQuiver β''' R Obj'''] in
lemma pick_comp_fst (b : Bool) : (pick (G.comp F) (E.comp F) b).1 = (pick G E b).1 :=
  congrArg Sigma.fst (pick_comp G E F b)

variable [NeZero n] {X : Fin (n + 1) → Obj} {deg : Fin n → β}
  (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

/-- A term of Φ ∘ (G ∘ F | E ∘ F), as a sum over the compositions of its blocks. -/
lemma compTerm_pick_comp (e : Composition n) (B : Fin e.length → Bool) (d : β''') (hd : _) :
    Φ.compTerm a e (fun l ↦ pick (G.comp F) (E.comp F) (B l)) d hd =
      ∑ τ : ∀ l : Fin e.length, Composition (e.blocksFun l),
        Φ.blockwiseTerm a e τ (fun _ _ ↦ ⟨1, F⟩) (fun l ↦ pick G E (B l))
          (fun l ↦ (ψ.comp φ) (targetDeg (pick G E (B l)).1 fun i ↦ deg (e.embedding l i)))
          (fun l ↦ comp_deg φ ψ (fun i ↦ deg (e.embedding l i)) (τ l) rfl) d
          (by simpa only [pick_comp_fst] using hd) :=
  (compTerm_congr a Φ e (funext fun l ↦ pick_comp G E F (B l)) d hd).trans
    (compTerm_comp_right a Φ F e _ d _)

/-- The terms of (Φ ∘ (G | E)) ∘ F and of Φ ∘ (G ∘ F | E ∘ F) are the same, reindexed along
`Composition.sigmaEquivSigmaPi`. -/
lemma sum_compTerm_compMarked (hu : s + 1 = u) (d : β''') (hd : ∀ _ : Composition n, _)
    (hd' : ∀ (e : Composition n) (_ : Fin e.length), _) :
    ∑ c : Composition n, (Φ.compMarked G E hu).compTerm a c (fun _ ↦ ⟨1, F⟩) d (hd c) =
      ∑ e : Composition n, ∑ m : Fin e.length, tailSign deg (e.sizeUpTo (m + 1)) •
        Φ.compTerm a e (fun l ↦ pick (G.comp F) (E.comp F) (decide (l = m))) d (hd' e m) := by
  refine (Finset.sum_congr rfl fun c _ ↦ compTerm_compMarked a Φ G E hu c _ _ _).trans ?_
  refine Eq.trans ?_ (Finset.sum_congr rfl fun e _ ↦ Finset.sum_congr rfl fun m _ ↦
    congrArg (tailSign deg (e.sizeUpTo (m + 1)) • ·)
      (compTerm_pick_comp Φ G E F a e (fun l ↦ decide (l = m)) d (hd' e m)).symm)
  refine Eq.trans ?_ (Finset.sum_congr rfl fun e _ ↦ Finset.sum_comm.trans
    (Finset.sum_congr rfl fun m _ ↦ Finset.smul_sum.symm))
  conv_lhs => rw [Finset.sum_sigma', Finset.univ_sigma_univ]
  conv_rhs => rw [Finset.sum_sigma', Finset.univ_sigma_univ]
  refine Fintype.sum_equiv (Composition.sigmaEquivSigmaPi n) _ _ fun σ ↦ ?_
  refine Fintype.sum_equiv (finCongr (σ.1.length_gather σ.2).symm) _ _ fun m ↦ ?_
  refine congrArg₂ (· • ·) ((tailSign_targetDeg_embedding φ deg σ.1 _).trans
    (congrArg _ (σ.1.sizeUpTo_gather σ.2 (m + 1)).symm)) ?_
  refine (groupedTerm_eq_blockwiseTerm a σ.1 σ.2 Φ _ _ _ _ _ _ _ _ _).trans
    (blockwiseTerm_congr a Φ _ _ rfl (funext fun l ↦ ?_) _ _ _ _).symm
  exact congrArg (pick G E) (decide_eq_decide.2
    ⟨fun hl ↦ Fin.ext (show (l : ℕ) = m from congrArg Fin.val hl),
      fun hl ↦ Fin.ext (show (l : ℕ) = m from congrArg Fin.val hl)⟩)

/-- (L): composing Φ ∘ (G | E) with `F` on the right composes both `G` and `E` with `F`. -/
theorem compMarked_comp (hu : s + 1 = u) :
    (Φ.compMarked G E hu).comp F = Φ.compMarked (G.comp F) (E.comp F) hu := by
  ext n _ X deg a j hj
  exact (comp_map_v_apply _ F a hj).trans ((sum_compTerm_compMarked Φ G E F a hu _ _ _).trans
    (compMarked_map_v_apply Φ (G.comp F) (E.comp F) a hu hj).symm)

end MarkedLeft

/-! ### Composing a composite with a marked map on the right -/

section MarkedRight

variable (Φ : ComposableMultilinearMap R h χ s) (G : ComposableMultilinearMap R g ψ 1)
  (F : ComposableMultilinearMap R f φ 1) (D : ComposableMultilinearMap R f φ 2)
  {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

variable (e : Composition n)

section Block

variable (l : Fin e.length) (τ : Composition (e.blocksFun l))

/-- The summand, indexed by a composition `τ` of the `l`-th block of a composition `e` of `n`, of
the value of G ∘ F, if `b` is false, or of G ∘ (F | D), if `b` is true, on that block. -/
def markedBlockTerm (b : Bool) :
    ComposableHom β'' R (fun k ↦ g (f (X (e.boundary k)))) l
      ((ψ.comp φ) (targetDeg (pick (G.comp F) (G.compMarked F D one_add_one_eq_two) b).1
        fun i ↦ deg (e.embedding l i))) :=
  match b with
  | false => G.blockCompTerm a e l τ (fun _ ↦ ⟨1, F⟩) _
      (comp_deg φ ψ (fun i ↦ deg (e.embedding l i)) τ rfl)
  | true => ∑ q : Fin τ.length, tailSign (fun i ↦ deg (e.embedding l i)) (τ.sizeUpTo (q + 1)) •
      G.blockCompTerm a e l τ (fun q₀ ↦ pick F D (decide (q₀ = q))) _
        (compMarked_deg F D (fun i ↦ deg (e.embedding l i)) τ q one_add_one_eq_two rfl)

lemma markedBlockTerm_of_false {b : Bool} (hb : b = false) (hd : _) :
    markedBlockTerm G F D a e l τ b = G.blockCompTerm a e l τ (fun _ ↦ ⟨1, F⟩) _ hd := by
  subst hb
  rfl

lemma markedBlockTerm_of_true {b : Bool} (hb : b = true) (hd : ∀ _ : Fin τ.length, _) :
    markedBlockTerm G F D a e l τ b =
      ∑ q : Fin τ.length, tailSign (fun i ↦ deg (e.embedding l i)) (τ.sizeUpTo (q + 1)) •
        G.blockCompTerm a e l τ (fun q₀ ↦ pick F D (decide (q₀ = q))) _ (hd q) := by
  subst hb
  rfl

/-- The value of G ∘ F or of G ∘ (F | D) on a block of a composition `e` of `n`, as a sum over
the compositions of that block. -/
lemma pick_blockMap_eq_sum (b : Bool) :
    (pick (G.comp F) (G.compMarked F D one_add_one_eq_two) b).2.blockMap a e l =
      ∑ τ : Composition (e.blocksFun l), markedBlockTerm G F D a e l τ b := by
  cases b
  · exact blockMap_comp a G F e l
  · exact blockMap_compMarked a G F D one_add_one_eq_two e l

end Block

variable (m : Fin e.length) (τ : ∀ l : Fin e.length, Composition (e.blocksFun l))

lemma one_add_sum_pick_fst_sub_one (q : Fin (τ m).length) (l : Fin e.length) :
    1 + ∑ q₀ : Fin (τ l).length,
      ((pick F D (decide ((⟨l, q₀⟩ : Σ l, Fin (τ l).length) = ⟨m, q⟩))).1 - 1) =
      (pick (G.comp F) (G.compMarked F D one_add_one_eq_two) (decide (l = m))).1 := by
  by_cases hl : l = m
  · subst hl
    simp [pick_fst_sub_one]
  · simp [hl]

/-- A term of G ∘ (F | D) or of G ∘ F on a block has the degree of that composite. -/
lemma markedBlock_deg (q : Fin (τ m).length) (l : Fin e.length) :
    ψ (targetDeg 1 fun q₀ ↦ φ (targetDeg
      (pick F D (decide ((⟨l, q₀⟩ : Σ l, Fin (τ l).length) = ⟨m, q⟩))).1 fun i ↦
        deg (e.embedding l ((τ l).embedding q₀ i)))) =
      (ψ.comp φ) (targetDeg (pick (G.comp F) (G.compMarked F D one_add_one_eq_two)
        (decide (l = m))).1 fun i ↦ deg (e.embedding l i)) :=
  degMap_targetDeg_degMap_targetDeg_embedding φ ψ (fun i ↦ deg (e.embedding l i)) (τ l) _
    (one_add_sum_pick_fst_sub_one G F D e m τ q l) rfl

variable [NeZero n]

/-- A term of Φ ∘ (G ∘ F | G ∘ (F | D)), as a sum over the compositions of its blocks. -/
lemma compTerm_pick_compMarked_eq_sum (B : Fin e.length → Bool) (d : β''') (hd : _) :
    Φ.compTerm a e
        (fun l ↦ pick (G.comp F) (G.compMarked F D one_add_one_eq_two) (B l)) d hd =
      ∑ τ : ∀ l : Fin e.length, Composition (e.blocksFun l),
        Φ.applyBlocks (fun Z ↦ g (f Z)) X e
          (fun l ↦ markedBlockTerm G F D a e l (τ l) (B l)) d hd := by
  simp only [compTerm, applyBlocks, pick_blockMap_eq_sum, MultilinearMap.map_sum, map_sum]

/-- Φ applied to the summands of the values of G ∘ F on the blocks other than `m` and of
G ∘ (F | D) on the block `m`, as a signed sum over the blocks of the composition of the block `m`.
-/
lemma applyBlocks_markedBlockTerm (d : β''') (hd : _) :
    Φ.applyBlocks (fun Z ↦ g (f Z)) X e
        (fun l ↦ markedBlockTerm G F D a e l (τ l) (decide (l = m))) d hd =
      ∑ q : Fin (τ m).length,
        tailSign (fun i ↦ deg (e.embedding m i)) ((τ m).sizeUpTo (q + 1)) •
          Φ.blockwiseTerm a e τ
            (fun l q₀ ↦ pick F D (decide ((⟨l, q₀⟩ : Σ l, Fin (τ l).length) = ⟨m, q⟩)))
            (fun _ ↦ ⟨1, G⟩) _ (markedBlock_deg G F D e m τ q) d hd := by
  have hw := markedBlockTerm_of_true G F D a e m (τ m) (decide_eq_true (rfl : m = m))
    fun q ↦ by simpa using markedBlock_deg G F D e m τ q m
  unfold blockwiseTerm applyBlocks
  rw [MultilinearMap.map_eq_sum_units_smul_update _
    (fun l ↦ markedBlockTerm G F D a e l (τ l) (decide (l = m))) m _ _ hw]
  simp only [map_sum, Units.smul_def, map_zsmul]
  refine Finset.sum_congr rfl fun q _ ↦ congrArg _ (congrArg _ (congrArg _ (funext fun l ↦ ?_)))
  by_cases hl : l = m
  · subst hl
    rw [Function.update_self]
    exact blockCompTerm_congr a G e l (τ l) (funext fun q₀ ↦ by simp) _ _
  · rw [Function.update_of_ne hl, markedBlockTerm_of_false G F D a e l (τ l) (decide_eq_false hl)
      (by simpa [hl] using markedBlock_deg G F D e m τ q l)]
    exact blockCompTerm_congr a G e l (τ l) (funext fun q₀ ↦ by simp [hl]) _ _

/-- A term of Φ ∘ (G ∘ F | G ∘ (F | D)), as a signed sum over the compositions of its blocks and
the blocks of the composition of its marked block. -/
lemma compTerm_pick_compMarked (d : β''') (hd : _) :
    Φ.compTerm a e (fun l ↦ pick (G.comp F) (G.compMarked F D one_add_one_eq_two)
        (decide (l = m))) d hd =
      ∑ τ : ∀ l : Fin e.length, Composition (e.blocksFun l), ∑ q : Fin (τ m).length,
        tailSign (fun i ↦ deg (e.embedding m i)) ((τ m).sizeUpTo (q + 1)) •
          Φ.blockwiseTerm a e τ
            (fun l q₀ ↦ pick F D (decide ((⟨l, q₀⟩ : Σ l, Fin (τ l).length) = ⟨m, q⟩)))
            (fun _ ↦ ⟨1, G⟩) _ (markedBlock_deg G F D e m τ q) d hd :=
  (compTerm_pick_compMarked_eq_sum Φ G F D a e (fun l ↦ decide (l = m)) d hd).trans
    (Finset.sum_congr rfl fun τ _ ↦ applyBlocks_markedBlockTerm Φ G F D a e m τ d hd)

/-- The terms of (Φ ∘ G) ∘ (F | D) and of Φ ∘ (G ∘ F | G ∘ (F | D)) are the same, reindexed along
`Composition.sigmaEquivSigmaPi` and `Composition.blocksFinEquiv`. -/
lemma sum_compTerm_comp_pick (d : β''') (hd : ∀ (c : Composition n) (_ : Fin c.length), _)
    (hd' : ∀ (e : Composition n) (_ : Fin e.length), _) :
    ∑ c : Composition n, ∑ m : Fin c.length, tailSign deg (c.sizeUpTo (m + 1)) •
        (Φ.comp G).compTerm a c (fun l ↦ pick F D (decide (l = m))) d (hd c m) =
      ∑ e : Composition n, ∑ m : Fin e.length, tailSign deg (e.sizeUpTo (m + 1)) •
        Φ.compTerm a e (fun l ↦ pick (G.comp F) (G.compMarked F D one_add_one_eq_two)
          (decide (l = m))) d (hd' e m) := by
  simp only [compTerm_comp, compTerm_pick_compMarked, Finset.smul_sum]
  refine (Finset.sum_congr rfl fun c _ ↦ Finset.sum_comm).trans ?_
  refine Eq.trans ?_ (Finset.sum_congr rfl fun e _ ↦ Finset.sum_comm)
  conv_lhs => rw [Finset.sum_sigma', Finset.univ_sigma_univ]
  conv_rhs => rw [Finset.sum_sigma', Finset.univ_sigma_univ]
  refine Fintype.sum_equiv (Composition.sigmaEquivSigmaPi n) _ _ fun σ ↦ ?_
  obtain ⟨c, c'⟩ := σ
  dsimp only [Composition.sigmaEquivSigmaPi, Equiv.coe_fn_mk]
  refine (c'.blocksFinEquiv.sum_comp _).symm.trans ?_
  refine Eq.trans ?_ (Fintype.sum_sigma' _)
  refine Fintype.sum_equiv (Equiv.sigmaCongr (finCongr (c.length_gather c').symm)
    fun i ↦ finCongr (c.length_sigmaCompositionAux c' i).symm) _ _ fun y ↦ ?_
  obtain ⟨i, j⟩ := y
  rw [smul_smul]
  refine congrArg₂ (· • ·) (tailSign_sizeUpTo_embedding_succ deg c c' i j) ?_
  refine (groupedTerm_eq_blockwiseTerm a c c' Φ _ _ _ _ _ _ _ _ _).trans
    (blockwiseTerm_congr a Φ _ _ (funext fun l ↦ funext fun q₀ ↦ ?_) rfl _ _ _ _).symm
  exact congrArg (pick F D)
    (decide_eq_decide.2 (c.embedding_cast_eq_embedding_iff c' i j l q₀).symm)

/-- (R): composing Φ ∘ G with `F` on the right, with one input replaced by `D`, replaces one input
G ∘ F of Φ by G ∘ (F | D). -/
theorem comp_compMarked (hu : s + 1 = u) :
    (Φ.comp G).compMarked F D hu =
      Φ.compMarked (G.comp F) (G.compMarked F D one_add_one_eq_two) hu := by
  ext n _ X deg a j hj
  exact (compMarked_map_v_apply _ F D a hu hj).trans ((sum_compTerm_comp_pick Φ G F D a _ _ _).trans
    (compMarked_map_v_apply Φ (G.comp F) (G.compMarked F D one_add_one_eq_two) a hu hj).symm)

end MarkedRight

end ComposableMultilinearMap

end AInfinityTheory
