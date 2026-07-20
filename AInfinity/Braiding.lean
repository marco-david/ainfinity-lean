module

public import AInfinity.KLRW
public import AInfinity.AdditiveCompletion
public import AInfinity.BoundedCochainComplex
public import AInfinity.AInfinityFunctor

@[expose] public section

open CategoryTheory AInfinityTheory AInfinityCategoryTheory CochainComplex.HomComplex
open BoundedCochainComplex (FinCochain mOne mTwo mOne_eq mTwo_eq mOne_ofHom)

/-- Tool for addition, allows
operands' types to only be *definitionally* equal. -/
infixl:65 " +≡ " => Add.add


universe u v w
variable {R : Type u} [CommRing R] [CharP R 2] [DecidableEq R] {n : ℕ}
variable [DecidablePred (Limits.IsZero (C := CMat_ (KLRWCategory n R)))]

/-- Over `[CharP R 2]` every Hom-group of the KLRW Hom-complexes is 2-torsion:
componentwise, morphisms are matrices of `DFinsupp`s valued in `R`. This is what
lets the sign-free `FinCochain`-language statements agree with the Koszul-signed
A∞ ones (see `BraidingFunctorData.sf₃_fin`). -/
theorem finCochain_neg_eq_self {X Y : BoundedCochainComplex (CMat_ (KLRWCategory n R))}
    {m : ℤ} (w : FinCochain X Y m) : -w = w := by
  funext p i j
  refine DFinsupp.ext fun k => ?_
  exact (DFinsupp.neg_apply _ _).trans (CharTwo.neg_eq _)

/-- A single degree-`0` KLRW morphism packaged as the argument of the unary
functor component. -/
def klrwSingle {A B : KLRWCategory n R} (f : A ⟶ B) :
    ∀ i : Fin 1, (composableHomType (β := ℤ) (R := R) (klrwHom (R := R) (n := n))
      ![A, B] ![(0 : ℤ)] i) :=
  Fin.cons f fun i => i.elim0

/-- Two composable degree-`0` KLRW morphisms packaged as the argument of the
binary functor component. -/
def klrwPair {A B C : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) :
    ∀ i : Fin 2, (composableHomType (β := ℤ) (R := R) (klrwHom (R := R) (n := n))
      ![A, B, C] ![(0 : ℤ), 0] i) :=
  Fin.cons f (Fin.cons g fun i => i.elim0)

/-- Three composable degree-`0` KLRW morphisms as a functor-component argument. -/
def klrwTriple {A B C D : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    ∀ i : Fin 3, (composableHomType (β := ℤ) (R := R) (klrwHom (R := R) (n := n))
      ![A, B, C, D] ![(0 : ℤ), 0, 0] i) :=
  Fin.cons f (Fin.cons g (Fin.cons h fun i => i.elim0))

/-- Four composable degree-`0` KLRW morphisms as a functor-component argument. -/
def klrwQuad {A B C D E : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (k : D ⟶ E) :
    ∀ i : Fin 4, (composableHomType (β := ℤ) (R := R) (klrwHom (R := R) (n := n))
      ![A, B, C, D, E] ![(0 : ℤ), 0, 0, 0] i) :=
  Fin.cons f (Fin.cons g (Fin.cons h (Fin.cons k fun i => i.elim0)))

/--
The data of a braiding functor: an A∞-functor from the (degenerate) A∞-category
`KLRW` (`klrwAInfinityPreCategory`) to the dg-A∞-category `K^•(Add KLRW)` of
bounded cochain complexes (`bccAInfinityPreCategory`), truncated at level 2:
the components `βₖ` vanish for `k ≥ 3` (`trunc`).

The blueprint's generator data is recovered as `gen₀`/`gen₁`/`gen₂` (the
components evaluated on degree-`0` chains, with target degree normalized), and
the truncated `[SF₁]`–`[SF₄]` axioms — in the A∞ language of `mOne`/`mTwo`, and
in the differential/composition language of `δ_fin`/`comp` — are derived
theorems (`sf₁`–`sf₄`, `sf₁_fin`–`sf₄_fin`).
-/
structure BraidingFunctorData (R : Type u) [CommRing R] [CharP R 2] [DecidableEq R] (n : ℕ)
    [DecidablePred (Limits.IsZero (C := CMat_ (KLRWCategory n R)))] where
  toFunctor :
    AInfinityFunctor (klrwAInfinityPreCategory (R := R) (n := n))
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R)))
  trunc : ∀ (k : ℕ+), 3 ≤ (k : ℕ) →
    ∀ (objs : Fin ((k : ℕ) + 1) → KLRWCategory n R) (deg : Fin (k : ℕ) → ℤ),
      toFunctor.f (n := k) objs deg = 0

namespace BraidingFunctorData

variable (β : BraidingFunctorData R n)

/-- `β₀`: the object map. -/
def gen₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R)) :=
  β.toFunctor.obj

/-- `β₁ f`: the unary component on a degree-`0` chain, as a degree-`0` element
of the Hom-complex. -/
def gen₁ {A B : KLRWCategory n R} (f : A ⟶ B) : FinCochain (β.gen₀ A) (β.gen₀ B) 0 :=
  FinCochain.degCast (R := R) (show functorTargetDeg ![(0 : ℤ)] = 0 by decide)
    (β.toFunctor.f (n := 1) ![A, B] ![(0 : ℤ)] (klrwSingle f))

/-- `β₂ f g`: the binary component on a degree-`(0, 0)` chain, as a
degree-`(-1)` element of the Hom-complex. -/
def gen₂ {A B C : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) :
    FinCochain (β.gen₀ A) (β.gen₀ C) (-1) :=
  FinCochain.degCast (R := R) (show functorTargetDeg ![(0 : ℤ), 0] = -1 by decide)
    (β.toFunctor.f (n := 2) ![A, B, C] ![(0 : ℤ), 0] (klrwPair f g))

/-! ### The truncated SF axioms

`toFunctor.sf` specializes, on degree-`0` chains of arities `1`–`4`, to the
blueprint's `[SF₁]`–`[SF₄]`, first in the language of the target's A∞
operations (`mOne`/`mTwo`, theorems `sf₁`–`sf₄`), then in the language of the
Hom-complex differential and composition (`sf₁_fin`–`sf₄_fin`).

TODO(sf-specialization): the proofs of `sf₁`–`sf₄` below evaluate the two sides
of `toFunctor.sf` at literal arities: expand the insertion sum (`stasheff*`
index machinery) and the partition sum (compositions of `k ≤ 4`), kill the
terms containing `μ₁ = 0`, `μₖ≥₃ = 0` (source), `mₖ≥₃ = 0` (target) or
`fₖ≥₃ = 0` (`trunc`), and identify the survivors with `mOne`/`mTwo`
applications across the degree casts. -/

/-! #### HEq plumbing for the SF specialization proofs

The surviving SF terms and the `mOne`/`mTwo` normal forms differ by cast
towers with *closed* (hence definitionally collapsible) degree endpoints, and
by the chain-index functions, which are pointwise definitionally equal but not
equal as functions (`0 + i` vs `i`). The helpers below strip the casts up to
`HEq` and transport across the index functions. -/

private lemma composition_one_eq (c : Composition 1) : c = Composition.ones 1 :=
  Composition.eq_ones_iff_length.mpr
    (le_antisymm c.length_le (c.length_pos_of_pos one_pos))

private lemma eq_mpr_heq {α β' : Sort _} (h : α = β') (a : β') : (Eq.mpr h a) ≍ a := by
  subst h; rfl

private lemma eq_mp_heq {α β' : Sort _} (h : α = β') (a : α) : (Eq.mp h a) ≍ a := by
  subst h; rfl

private lemma finCochain_degCast_heq {X Y : BoundedCochainComplex (CMat_ (KLRWCategory n R))}
    {d e : ℤ} (h : d = e) (z : FinCochain X Y d) :
    (FinCochain.degCast (R := R) h z) ≍ z := by subst h; rfl

private lemma modcat_eqrec_heq {S : Type*} [CommRing S] {A' B' : ModuleCat S} (h : A' = B')
    (a : ↑A') : (h ▸ a : ↑B') ≍ a := by subst h; rfl

private lemma mlm_apply_congr_heq {S : Type*} [CommRing S] {Obj : Type*}
    (Hom : Obj → Obj → GradedRModule (β := ℤ) (R := S)) {k : ℕ}
    {T : (Fin (k + 1) → Obj) → (Fin k → ℤ) → ModuleCat S}
    (F : ∀ (o : Fin (k + 1) → Obj) (d : Fin k → ℤ),
      MultilinearMap S (fun i => composableHomType Hom o d i) (T o d))
    {o₁ o₂ : Fin (k + 1) → Obj} (ho : o₁ = o₂)
    {d₁ d₂ : Fin k → ℤ} (hd : d₁ = d₂)
    {v₁ : ∀ i, composableHomType Hom o₁ d₁ i}
    {v₂ : ∀ i, composableHomType Hom o₂ d₂ i}
    (hv : v₁ ≍ v₂) :
    F o₁ d₁ v₁ ≍ F o₂ d₂ v₂ := by
  subst ho; subst hd
  cases hv
  rfl

theorem sf₁ {A B : KLRWCategory n R} (f : A ⟶ B) :
    mOne (R := R) (zero_add 1) (β.gen₁ f) = 0 := by
  have h := β.toFunctor.sf 1 ![A, B] ![(0 : ℤ)] (klrwSingle f)
  -- the insertion side vanishes: the only term is f₁(μ₁^KLRW x) with μ₁ = 0
  have hL : indexedSFLeftSum (β := ℤ) (R := R) (n := (1 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      β.toFunctor.obj
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      β.toFunctor.f ![A, B] ![(0 : ℤ)] (klrwSingle f) = 0 := by
    simp only [indexedSFLeftSum]
    apply Finset.sum_eq_zero
    rintro ⟨r, hrm⟩ -
    apply Finset.sum_eq_zero
    rintro ⟨s, hsm⟩ -
    have hv := validStasheffIndices_of_mem_ranges (n := 1) hrm hsm
    suffices hh : indexedSFLeftTerm (β := ℤ) (n := (1 : ℕ+))
        (klrwAInfinityPreCategory (R := R) (n := n)).Hom
        (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
        β.toFunctor.obj
        (klrwAInfinityPreCategory (R := R) (n := n)).m
        β.toFunctor.f ![A, B] ![(0 : ℤ)] (klrwSingle f) r s hv.1 hv.2 = 0 by
      rw [hh, smul_zero]
    have hs1 : s = 1 := by have := hv.1; have := hv.2; omega
    subst hs1
    exact indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
      (fun hh o d => klrwM_one_eq_zero hh o d)
  -- the partition side is the single term at the composition [1]
  have hR : indexedSFRightSum (β := ℤ) (R := R) (n := (1 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      β.toFunctor.obj
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      β.toFunctor.f ![A, B] ![(0 : ℤ)] (klrwSingle f) =
      indexedSFRightTerm (β := ℤ) (R := R) (n := (1 : ℕ+))
        (klrwAInfinityPreCategory (R := R) (n := n)).Hom
        (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
        β.toFunctor.obj
        (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m
        β.toFunctor.f ![A, B] ![(0 : ℤ)] (klrwSingle f) (Composition.ones 1) := by
    simp only [indexedSFRightSum]
    exact Finset.sum_eq_single_of_mem _ (Finset.mem_univ _)
      (fun c _ hc => absurd (composition_one_eq c) hc)
  -- bridge the surviving term to the `mOne` normal form
  calc mOne (R := R) (zero_add 1) (β.gen₁ f)
      = indexedSFRightTerm (β := ℤ) (R := R) (n := (1 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
            (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
            (V := CMat_ (KLRWCategory n R))).m
          β.toFunctor.f ![A, B] ![(0 : ℤ)] (klrwSingle f) (Composition.ones 1) := ?_
    _ = indexedSFRightSum (β := ℤ) (R := R) (n := (1 : ℕ+)) _ _ _ _
          β.toFunctor.f ![A, B] ![(0 : ℤ)] (klrwSingle f) := hR.symm
    _ = 0 := h.symm.trans hL
  · -- both sides are cast towers around μ₁ᵇᶜᶜ applied to (a cast of) the
    -- f₁-value on the chain; the casts strip to HEq and the index functions
    -- match pointwise.
    simp only [indexedSFRightTerm]
    refine eq_of_heq ?_
    refine HEq.trans (finCochain_degCast_heq _ _) ?_
    refine (mlm_apply_congr_heq
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      (fun o d => (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m (n := ⟨1, Nat.one_pos⟩) o d)
      ?_ ?_ ?_).symm
    · exact funext fun j => by fin_cases j <;> rfl
    · exact funext fun j => by fin_cases j <;> rfl
    · -- the input vectors agree up to HEq
      refine Function.hfunext rfl fun a a' haa => ?_
      obtain ⟨av, ha⟩ := a
      obtain ⟨av', ha'⟩ := a'
      have ha2 : av < 1 := ha
      have ha2' : av' < 1 := ha'
      interval_cases av
      interval_cases av'
      refine HEq.trans (eq_mpr_heq _ _) ?_
      refine HEq.trans (eq_mp_heq _ _) ?_
      refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
      refine (mlm_apply_congr_heq (klrwHom (R := R) (n := n))
        (fun o d => β.toFunctor.f (n := ⟨1, Nat.one_pos⟩) o d) ?_ ?_ ?_).symm
      · exact funext fun i => by fin_cases i <;> rfl
      · exact funext fun i => by fin_cases i <;> rfl
      · refine Function.hfunext rfl fun b b' hbb => ?_
        obtain ⟨bv, hb⟩ := b
        obtain ⟨bv', hb'⟩ := b'
        have hb2 : bv < 1 := hb
        have hb2' : bv' < 1 := hb'
        interval_cases bv
        interval_cases bv'
        exact HEq.rfl

private lemma composition_two_cases (c : Composition 2) :
    c = Composition.ones 2 ∨ c = Composition.single 2 (by norm_num) := by
  rcases eq_or_ne c.length 2 with h2 | h2
  · exact Or.inl (Composition.eq_ones_iff_length.mpr h2)
  · refine Or.inr ((Composition.eq_single_iff_length (by norm_num)).mpr ?_)
    have h1 := c.length_le
    have h0 := c.length_pos_of_pos (by norm_num)
    omega

set_option maxHeartbeats 1600000 in
theorem sf₂ {A B C : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) :
    β.gen₁ (f ≫ g) =
      mTwo (R := R) (zero_add 0) (β.gen₁ f) (β.gen₁ g) +
        mOne (R := R) (neg_add_cancel 1) (β.gen₂ f g) := by
  have h := β.toFunctor.sf 2 ![A, B, C] ![(0 : ℤ), 0] (klrwPair f g)
  -- gen₁ (f ≫ g) is the surviving insertion term f₁(μ₂ᴷᴸᴿᵂ(f, g)):
  -- μ₂ᴷᴸᴿᵂ(f, g) collapses definitionally to f ≫ g (closed degrees).
  have e1 : β.gen₁ (f ≫ g) =
      indexedSFLeftTerm (β := ℤ) (R := R) (n := (2 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C] ![(0 : ℤ), 0] (klrwPair f g) 0 2 (by norm_num) (by norm_num) := by
    simp only [indexedSFLeftTerm]
    refine eq_of_heq ?_
    refine HEq.trans (finCochain_degCast_heq _ _) ?_
    refine (mlm_apply_congr_heq (klrwHom (R := R) (n := n))
      (fun o d => β.toFunctor.f (n := ⟨1, Nat.one_pos⟩) o d) ?_ ?_ ?_).symm
    · exact funext fun j => by fin_cases j <;> rfl
    · exact funext fun j => by fin_cases j <;> rfl
    · refine Function.hfunext rfl fun a a' haa => ?_
      obtain ⟨av, ha⟩ := a
      obtain ⟨av', ha'⟩ := a'
      have ha2 : av < 1 := ha
      have ha2' : av' < 1 := ha'
      interval_cases av
      interval_cases av'
      exact HEq.rfl
  -- the insertion sum collapses to that single term (sign +1)
  have e2 : indexedSFLeftSum (β := ℤ) (R := R) (n := (2 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C] ![(0 : ℤ), 0] (klrwPair f g) =
      indexedSFLeftTerm (β := ℤ) (R := R) (n := (2 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C] ![(0 : ℤ), 0] (klrwPair f g) 0 2 (by norm_num) (by norm_num) := by
    simp only [indexedSFLeftSum]
    refine (Finset.sum_eq_single_of_mem ⟨0, by decide⟩ (Finset.mem_attach _ _) ?_).trans
      ((Finset.sum_eq_single_of_mem ⟨2, by decide⟩ (Finset.mem_attach _ _) ?_).trans ?_)
    · rintro ⟨r, hrm⟩ - hne
      apply Finset.sum_eq_zero
      rintro ⟨s, hsm⟩ -
      have hmem := Finset.mem_Ico.mp hsm
      have hr0 : r ≠ 0 := fun hh => hne (Subtype.ext hh)
      have hrr := Finset.mem_range.mp hrm
      have hv := validStasheffIndices_of_mem_ranges (n := 2) hrm hsm
      suffices hh : indexedSFLeftTerm (β := ℤ) (R := R) (n := (2 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C] ![(0 : ℤ), 0] (klrwPair f g) r s hv.1 hv.2 = 0 by
        rw [hh, smul_zero]
      have hs1 : s = 1 := by omega
      subst hs1
      exact indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
        (fun hh o d => klrwM_one_eq_zero hh o d)
    · rintro ⟨s, hsm⟩ - hne
      have hmem := Finset.mem_Ico.mp hsm
      have hs2 : s ≠ 2 := fun hh => hne (Subtype.ext hh)
      have hv := validStasheffIndices_of_mem_ranges (n := 2) (by decide) hsm
      suffices hh : indexedSFLeftTerm (β := ℤ) (R := R) (n := (2 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C] ![(0 : ℤ), 0] (klrwPair f g) 0 s hv.1 hv.2 = 0 by
        rw [hh, smul_zero]
      have hs1 : s = 1 := by omega
      subst hs1
      exact indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
        (fun hh o d => klrwM_one_eq_zero hh o d)
    · exact one_smul ℤ _
  -- the partition sum has exactly the compositions [1,1] and [2]
  have hne2 : Composition.ones 2 ≠ Composition.single 2 (by norm_num) := by decide
  have e3 : indexedSFRightSum (β := ℤ) (R := R) (n := (2 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m
          β.toFunctor.f ![A, B, C] ![(0 : ℤ), 0] (klrwPair f g) =
      indexedSFRightTerm (β := ℤ) (R := R) (n := (2 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m
          β.toFunctor.f ![A, B, C] ![(0 : ℤ), 0] (klrwPair f g) (Composition.ones 2) +
        indexedSFRightTerm (β := ℤ) (R := R) (n := (2 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m
          β.toFunctor.f ![A, B, C] ![(0 : ℤ), 0] (klrwPair f g) (Composition.single 2 (by norm_num)) := by
    simp only [indexedSFRightSum]
    rw [show (Finset.univ : Finset (Composition ((2 : ℕ+) : ℕ))) =
        {Composition.ones 2, Composition.single 2 (by norm_num)} from by
        ext c
        refine ⟨fun _ => ?_, fun _ => Finset.mem_univ c⟩
        rcases composition_two_cases c with rfl | rfl
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)]
    exact Finset.sum_pair hne2
  -- μ₂ᵇᶜᶜ(f₁ f, f₁ g) = mTwo (gen₁ f) (gen₁ g)
  have e4 : indexedSFRightTerm (β := ℤ) (R := R) (n := (2 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m
          β.toFunctor.f ![A, B, C] ![(0 : ℤ), 0] (klrwPair f g) (Composition.ones 2) =
      mTwo (R := R) (zero_add 0) (β.gen₁ f) (β.gen₁ g) := by
    simp only [indexedSFRightTerm]
    refine eq_of_heq ?_
    refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
    refine mlm_apply_congr_heq
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
      (fun o d => (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m (n := ⟨2, Nat.zero_lt_two⟩) o d) ?_ ?_ ?_
    · exact funext fun j => by fin_cases j <;> rfl
    · exact funext fun j => by fin_cases j <;> rfl
    · refine Function.hfunext rfl fun a a' haa => ?_
      obtain ⟨av, ha⟩ := a
      obtain ⟨av', ha'⟩ := a'
      have ha2 : av < 2 := ha
      have ha2' : av' < 2 := ha'
      have hvv : av = av' := congrArg Fin.val (eq_of_heq haa)
      subst hvv
      interval_cases av
      · refine HEq.trans (eq_mpr_heq _ _) ?_
        refine HEq.trans (eq_mp_heq _ _) ?_
        refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
        refine (mlm_apply_congr_heq (klrwHom (R := R) (n := n))
          (fun o d => β.toFunctor.f (n := ⟨1, Nat.one_pos⟩) o d) ?_ ?_ ?_).symm
        · exact funext fun i => by fin_cases i <;> rfl
        · exact funext fun i => by fin_cases i <;> rfl
        · refine Function.hfunext rfl fun b b' hbb => ?_
          obtain ⟨bv, hb⟩ := b
          obtain ⟨bv', hb'⟩ := b'
          have hb2 : bv < 1 := hb
          have hb2' : bv' < 1 := hb'
          have hvv : bv = bv' := by omega
          subst hvv
          interval_cases bv <;> exact HEq.rfl
      · refine HEq.trans (eq_mpr_heq _ _) ?_
        refine HEq.trans (eq_mp_heq _ _) ?_
        refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
        refine (mlm_apply_congr_heq (klrwHom (R := R) (n := n))
          (fun o d => β.toFunctor.f (n := ⟨1, Nat.one_pos⟩) o d) ?_ ?_ ?_).symm
        · exact funext fun i => by fin_cases i <;> rfl
        · exact funext fun i => by fin_cases i <;> rfl
        · refine Function.hfunext rfl fun b b' hbb => ?_
          obtain ⟨bv, hb⟩ := b
          obtain ⟨bv', hb'⟩ := b'
          have hb2 : bv < 1 := hb
          have hb2' : bv' < 1 := hb'
          have hvv : bv = bv' := by omega
          subst hvv
          interval_cases bv <;> exact HEq.rfl
  -- μ₁ᵇᶜᶜ(f₂(f, g)) = mOne (gen₂ f g)
  have e5 : indexedSFRightTerm (β := ℤ) (R := R) (n := (2 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m
          β.toFunctor.f ![A, B, C] ![(0 : ℤ), 0] (klrwPair f g) (Composition.single 2 (by norm_num)) =
      mOne (R := R) (neg_add_cancel 1) (β.gen₂ f g) := by
    simp only [indexedSFRightTerm]
    refine eq_of_heq ?_
    refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
    refine mlm_apply_congr_heq
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
      (fun o d => (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m (n := ⟨1, Nat.one_pos⟩) o d) ?_ ?_ ?_
    · exact funext fun j => by fin_cases j <;> rfl
    · exact funext fun j => by fin_cases j <;> rfl
    · refine Function.hfunext rfl fun a a' haa => ?_
      obtain ⟨av, ha⟩ := a
      obtain ⟨av', ha'⟩ := a'
      have ha2 : av < 1 := ha
      have ha2' : av' < 1 := ha'
      interval_cases av
      interval_cases av'
      refine HEq.trans (eq_mpr_heq _ _) ?_
      refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
      refine (mlm_apply_congr_heq (klrwHom (R := R) (n := n))
        (fun o d => β.toFunctor.f (n := ⟨2, Nat.zero_lt_two⟩) o d) ?_ ?_ ?_).symm
      · exact funext fun i => by fin_cases i <;> rfl
      · exact funext fun i => by fin_cases i <;> rfl
      · refine Function.hfunext rfl fun b b' hbb => ?_
        obtain ⟨bv, hb⟩ := b
        obtain ⟨bv', hb'⟩ := b'
        have hb2 : bv < 2 := hb
        have hb2' : bv' < 2 := hb'
        have hvv : bv = bv' := congrArg Fin.val (eq_of_heq hbb)
        subst hvv
        interval_cases bv <;> exact HEq.rfl
  exact e1.trans (e2.symm.trans (h.trans (e3.trans (congrArg₂ (· + ·) e4 e5))))

-- μₖ = 0 for k ≥ 3 in the bcc target (local restatement of the private bcc fact).
private lemma bccM_zero_of_ge_three {j : ℕ} (hj : 3 ≤ j)
    {obj : Fin (j + 1) → BoundedCochainComplex (CMat_ (KLRWCategory n R))}
    {deg : Fin j → ℤ} :
    BoundedCochainComplex.bccAInfinityPreCategory.m (R := R) (n := ⟨j, by omega⟩)
      obj deg = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
  rfl

private lemma sum_eq_add_of_mem' {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    {s : Finset α} {f : α → M} (a b : α) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hother : ∀ c ∈ s, c ≠ a → c ≠ b → f c = 0) :
    ∑ x ∈ s, f x = f a + f b := by
  classical
  refine ((Finset.sum_subset (show ({a, b} : Finset α) ⊆ s from ?_) ?_).symm).trans
    (Finset.sum_pair hab)
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    · rw [Finset.mem_singleton.mp hx]; exact hb
  · intro x hx hnx
    refine hother x hx ?_ ?_ <;> intro hxx <;> subst hxx <;> exact hnx (by simp)

private lemma composition_three_cases (c : Composition 3) :
    c = Composition.ones 3 ∨ c = (⟨[1, 2], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 3) ∨ c = (⟨[2, 1], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 3) ∨
      c = Composition.single 3 (by norm_num) := by
  obtain ⟨bs, hpos, hsum⟩ := c
  have hsum' : bs.sum = 3 := hsum
  rcases bs with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩
  · simp at hsum'
  · right; right; right
    have ha : a = 3 := by simpa using hsum'
    subst ha
    rfl
  · have hpa : 0 < a := hpos (by simp)
    have hpb : 0 < b := hpos (by simp)
    simp [List.sum_cons] at hsum'
    rcases (by omega : a = 1 ∧ b = 2 ∨ a = 2 ∧ b = 1) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · right; left; rfl
    · right; right; left; rfl
  · left
    have hpa : 0 < a := hpos (by simp)
    have hpb : 0 < b := hpos (by simp)
    have hpd : 0 < d := hpos (by simp)
    simp [List.sum_cons] at hsum'
    obtain ⟨rfl, rfl, rfl⟩ : a = 1 ∧ b = 1 ∧ d = 1 := by omega
    rfl
  · exfalso
    have hpa : 0 < a := hpos (by simp)
    have hpb : 0 < b := hpos (by simp)
    have hpd : 0 < d := hpos (by simp)
    have hpe : 0 < e := hpos (by simp)
    simp [List.sum_cons] at hsum'
    omega

private lemma sf₃_key1 {S : Type*} [CommRing S] {M : ModuleCat S} (T U : M)
    (a b c d : ℤ) :
    a • (0 : M) + ((-1 : ℤ) • T + b • (0 : M)) +
      (c • (0 : M) + (1 : ℤ) • U + (d • (0 : M) + (0 : M))) = (-1 : ℤ) • T + U := by
  simp

private lemma sf₃_key2 {S : Type*} [CommRing S] [CharP S 2] {M : ModuleCat S} (T U : M) :
    U + T = (-1 : ℤ) • T + U := by
  have h2 : ∀ w : M, -w = w := fun w =>
    neg_eq_of_add_eq_zero_left (by rw [← two_smul S w, CharTwo.two_eq_zero, zero_smul])
  rw [neg_smul, one_smul, h2]
  exact add_comm U T

private lemma sf₃_key3 {S : Type*} [CommRing S] {M : ModuleCat S} (T U : M) :
    (0 : M) + (T + (U + 0)) = T + U := by simp

set_option maxHeartbeats 3200000 in
theorem sf₃ {A B C D : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    β.gen₂ f (g ≫ h) + β.gen₂ (f ≫ g) h =
      mTwo (R := R) (zero_add (-1)) (β.gen₁ f) (β.gen₂ g h) +
        mTwo (R := R) (add_zero (-1)) (β.gen₂ f g) (β.gen₁ h) := by
  have hsf := β.toFunctor.sf 3 ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h)
  -- bridges: the two surviving insertion terms are the gen₂'s of composites
  have ebL1 : β.gen₂ f (g ≫ h) =
      indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) 1 2 (by norm_num) (by norm_num) := by
    simp only [indexedSFLeftTerm]
    refine eq_of_heq ?_
    refine HEq.trans (finCochain_degCast_heq _ _) ?_
    refine (mlm_apply_congr_heq (klrwHom (R := R) (n := n))
      (fun o d => β.toFunctor.f (n := ⟨2, Nat.zero_lt_two⟩) o d) ?_ ?_ ?_).symm
    · exact funext fun j => by fin_cases j <;> rfl
    · exact funext fun j => by fin_cases j <;> rfl
    · refine Function.hfunext rfl fun a a' haa => ?_
      obtain ⟨av, ha⟩ := a
      obtain ⟨av', ha'⟩ := a'
      have ha2 : av < 2 := ha
      have ha2' : av' < 2 := ha'
      have hvv : av = av' := congrArg Fin.val (eq_of_heq haa)
      subst hvv
      interval_cases av <;> exact HEq.rfl
  have ebL2 : β.gen₂ (f ≫ g) h =
      indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) 0 2 (by norm_num) (by norm_num) := by
    simp only [indexedSFLeftTerm]
    refine eq_of_heq ?_
    refine HEq.trans (finCochain_degCast_heq _ _) ?_
    refine (mlm_apply_congr_heq (klrwHom (R := R) (n := n))
      (fun o d => β.toFunctor.f (n := ⟨2, Nat.zero_lt_two⟩) o d) ?_ ?_ ?_).symm
    · exact funext fun j => by fin_cases j <;> rfl
    · exact funext fun j => by fin_cases j <;> rfl
    · refine Function.hfunext rfl fun a a' haa => ?_
      obtain ⟨av, ha⟩ := a
      obtain ⟨av', ha'⟩ := a'
      have ha2 : av < 2 := ha
      have ha2' : av' < 2 := ha'
      have hvv : av = av' := congrArg Fin.val (eq_of_heq haa)
      subst hvv
      interval_cases av <;> exact HEq.rfl
  -- the insertion sum expands to the two survivors with signs −1, +1
  have hL : indexedSFLeftSum (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) =
      (-1 : ℤ) • indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) 0 2 (by norm_num) (by norm_num) +
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) 1 2 (by norm_num) (by norm_num) := by
    simp only [indexedSFLeftSum, PNat.val_ofNat]
    rw [show (Finset.range (3 + 1) : Finset ℕ).attach =
        ({⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩} :
          Finset { a // a ∈ Finset.range (3 + 1) }) from by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [show (Finset.Ico 1 (3 - (0 : ℕ) + 1) : Finset ℕ).attach =
        ({⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩} :
          Finset { a // a ∈ (Finset.Ico 1 (3 - (0 : ℕ) + 1) : Finset ℕ) }) from by decide]
    rw [show (Finset.Ico 1 (3 - (1 : ℕ) + 1) : Finset ℕ).attach =
        ({⟨1, by decide⟩, ⟨2, by decide⟩} :
          Finset { a // a ∈ (Finset.Ico 1 (3 - (1 : ℕ) + 1) : Finset ℕ) }) from by decide]
    rw [show (Finset.Ico 1 (3 - (2 : ℕ) + 1) : Finset ℕ).attach =
        ({⟨1, by decide⟩} :
          Finset { a // a ∈ (Finset.Ico 1 (3 - (2 : ℕ) + 1) : Finset ℕ) }) from by decide]
    rw [show (Finset.Ico 1 (3 - (3 : ℕ) + 1) : Finset ℕ).attach =
        (∅ : Finset { a // a ∈ (Finset.Ico 1 (3 - (3 : ℕ) + 1) : Finset ℕ) }) from by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, Finset.sum_insert (by decide), Finset.sum_singleton,
      Finset.sum_singleton, Finset.sum_empty]
    show stasheffSign ![(0 : ℤ), 0, 0] 0 1 (by decide) •
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) 0 1 (by decide) (by decide) +
      ((-1 : ℤ) •
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) 0 2 (by decide) (by decide) +
        stasheffSign ![(0 : ℤ), 0, 0] 0 3 (by decide) •
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) 0 3 (by decide) (by decide)) +
      (stasheffSign ![(0 : ℤ), 0, 0] 1 1 (by decide) •
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) 1 1 (by decide) (by decide) +
        (1 : ℤ) •
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) 1 2 (by decide) (by decide) +
        (stasheffSign ![(0 : ℤ), 0, 0] 2 1 (by decide) •
          indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) 2 1 (by decide) (by decide) +
          0)) = _
    have e01 : ∀ (hs : 1 ≤ 1) (hr : 0 + 1 ≤ 3),
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) 0 1 hs hr = 0 :=
      fun _ _ => indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
        (fun hh o d => klrwM_one_eq_zero hh o d)
    have e11 : ∀ (hs : 1 ≤ 1) (hr : 1 + 1 ≤ 3),
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) 1 1 hs hr = 0 :=
      fun _ _ => indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
        (fun hh o d => klrwM_one_eq_zero hh o d)
    have e21 : ∀ (hs : 1 ≤ 1) (hr : 2 + 1 ≤ 3),
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) 2 1 hs hr = 0 :=
      fun _ _ => indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
        (fun hh o d => klrwM_one_eq_zero hh o d)
    have e03 : ∀ (hs : 1 ≤ 3) (hr : 0 + 3 ≤ 3),
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) 0 3 hs hr = 0 :=
      fun _ _ => indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
        (fun hh o d => klrwM_zero_of_ge_three (by norm_num))
    rw [e01, e11, e21, e03]
    apply sf₃_key1
  -- the partition sum expands to the two surviving compositions [1,2], [2,1]
  have hR : indexedSFRightSum (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) =
      indexedSFRightTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) (⟨[1, 2], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 3) + indexedSFRightTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) (⟨[2, 1], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 3) := by
    simp only [indexedSFRightSum]
    refine sum_eq_add_of_mem' (⟨[1, 2], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 3) (⟨[2, 1], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 3)
      (Finset.mem_univ _) (Finset.mem_univ _) (by decide) ?_
    intro c _ hc1 hc2
    rcases composition_three_cases c with rfl | rfl | rfl | rfl
    · exact indexedSFRightTerm_outer_zero _ _ _ _ _ _ _ _ _
        (fun hh o d => bccM_zero_of_ge_three (Nat.le_refl 3))
    · exact absurd rfl hc1
    · exact absurd rfl hc2
    · exact indexedSFRightTerm_inner_zero _ _ _ _ _ _ _ _ _ ⟨0, Nat.one_pos⟩
        (fun hh o d => β.trunc ⟨_, hh⟩ (Nat.le_refl 3) o d)
  -- bridges: the two surviving partition terms are the mTwo's
  have ebR1 : indexedSFRightTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) (⟨[1, 2], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 3) =
      mTwo (R := R) (zero_add (-1)) (β.gen₁ f) (β.gen₂ g h) := by
    simp only [indexedSFRightTerm]
    refine eq_of_heq ?_
    refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
    refine mlm_apply_congr_heq
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
      (fun o d => (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m (n := ⟨2, Nat.zero_lt_two⟩) o d) ?_ ?_ ?_
    · exact funext fun j => by fin_cases j <;> rfl
    · exact funext fun j => by fin_cases j <;> rfl
    · refine Function.hfunext rfl fun a a' haa => ?_
      obtain ⟨av, ha⟩ := a
      obtain ⟨av', ha'⟩ := a'
      have ha2 : av < 2 := ha
      have ha2' : av' < 2 := ha'
      have hvv : av = av' := congrArg Fin.val (eq_of_heq haa)
      subst hvv
      interval_cases av
      · refine HEq.trans (eq_mpr_heq _ _) ?_
        refine HEq.trans (eq_mp_heq _ _) ?_
        refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
        refine (mlm_apply_congr_heq (klrwHom (R := R) (n := n))
          (fun o d => β.toFunctor.f (n := ⟨1, Nat.one_pos⟩) o d) ?_ ?_ ?_).symm
        · exact funext fun i => by fin_cases i <;> rfl
        · exact funext fun i => by fin_cases i <;> rfl
        · refine Function.hfunext rfl fun b b' hbb => ?_
          obtain ⟨bv, hb⟩ := b
          obtain ⟨bv', hb'⟩ := b'
          have hb2 : bv < 1 := hb
          have hb2' : bv' < 1 := hb'
          have hvv : bv = bv' := congrArg Fin.val (eq_of_heq hbb)
          subst hvv
          interval_cases bv <;> exact HEq.rfl
      · refine HEq.trans (eq_mpr_heq _ _) ?_
        refine HEq.trans (eq_mp_heq _ _) ?_
        refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
        refine (mlm_apply_congr_heq (klrwHom (R := R) (n := n))
          (fun o d => β.toFunctor.f (n := ⟨2, Nat.zero_lt_two⟩) o d) ?_ ?_ ?_).symm
        · exact funext fun i => by fin_cases i <;> rfl
        · exact funext fun i => by fin_cases i <;> rfl
        · refine Function.hfunext rfl fun b b' hbb => ?_
          obtain ⟨bv, hb⟩ := b
          obtain ⟨bv', hb'⟩ := b'
          have hb2 : bv < 2 := hb
          have hb2' : bv' < 2 := hb'
          have hvv : bv = bv' := congrArg Fin.val (eq_of_heq hbb)
          subst hvv
          interval_cases bv <;> exact HEq.rfl
  have ebR2 : indexedSFRightTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m
          β.toFunctor.f ![A, B, C, D] ![(0 : ℤ), 0, 0] (klrwTriple f g h) (⟨[2, 1], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 3) =
      mTwo (R := R) (add_zero (-1)) (β.gen₂ f g) (β.gen₁ h) := by
    simp only [indexedSFRightTerm]
    refine eq_of_heq ?_
    refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
    refine mlm_apply_congr_heq
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
      (fun o d => (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m (n := ⟨2, Nat.zero_lt_two⟩) o d) ?_ ?_ ?_
    · exact funext fun j => by fin_cases j <;> rfl
    · exact funext fun j => by fin_cases j <;> rfl
    · refine Function.hfunext rfl fun a a' haa => ?_
      obtain ⟨av, ha⟩ := a
      obtain ⟨av', ha'⟩ := a'
      have ha2 : av < 2 := ha
      have ha2' : av' < 2 := ha'
      have hvv : av = av' := congrArg Fin.val (eq_of_heq haa)
      subst hvv
      interval_cases av
      · refine HEq.trans (eq_mpr_heq _ _) ?_
        refine HEq.trans (eq_mp_heq _ _) ?_
        refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
        refine (mlm_apply_congr_heq (klrwHom (R := R) (n := n))
          (fun o d => β.toFunctor.f (n := ⟨2, Nat.zero_lt_two⟩) o d) ?_ ?_ ?_).symm
        · exact funext fun i => by fin_cases i <;> rfl
        · exact funext fun i => by fin_cases i <;> rfl
        · refine Function.hfunext rfl fun b b' hbb => ?_
          obtain ⟨bv, hb⟩ := b
          obtain ⟨bv', hb'⟩ := b'
          have hb2 : bv < 2 := hb
          have hb2' : bv' < 2 := hb'
          have hvv : bv = bv' := congrArg Fin.val (eq_of_heq hbb)
          subst hvv
          interval_cases bv <;> exact HEq.rfl
      · refine HEq.trans (eq_mpr_heq _ _) ?_
        refine HEq.trans (eq_mp_heq _ _) ?_
        refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
        refine (mlm_apply_congr_heq (klrwHom (R := R) (n := n))
          (fun o d => β.toFunctor.f (n := ⟨1, Nat.one_pos⟩) o d) ?_ ?_ ?_).symm
        · exact funext fun i => by fin_cases i <;> rfl
        · exact funext fun i => by fin_cases i <;> rfl
        · refine Function.hfunext rfl fun b b' hbb => ?_
          obtain ⟨bv, hb⟩ := b
          obtain ⟨bv', hb'⟩ := b'
          have hb2 : bv < 1 := hb
          have hb2' : bv' < 1 := hb'
          have hvv : bv = bv' := congrArg Fin.val (eq_of_heq hbb)
          subst hvv
          interval_cases bv <;> exact HEq.rfl
  -- assemble over char 2 (the (0,2) insertion sign is −1)
  refine (congrArg₂ (· + ·) ebL1 ebL2).trans ?_
  refine Eq.trans ?_ (hL.symm.trans (hsf.trans (hR.trans (congrArg₂ (· + ·) ebR1 ebR2))))
  apply sf₃_key2

-- A composition of 4 with at most two blocks, all of size ≤ 2, is [2, 2].
private lemma composition_four_eq_two_two (c : Composition 4) (hlen : c.length ≤ 2)
    (hall : ∀ j : Fin c.length, c.blocksFun j ≤ 2) :
    c = ⟨[2, 2], fun hi => by fin_cases hi <;> norm_num, by decide⟩ := by
  obtain ⟨bs, hpos, hsum⟩ := c
  have hlen' : bs.length ≤ 2 := hlen
  have hsum' : bs.sum = 4 := hsum
  rcases bs with _ | ⟨a, _ | ⟨b, _ | ⟨c', t⟩⟩⟩
  · simp at hsum'
  · have ha : a ≤ 2 := hall ⟨0, Nat.one_pos⟩
    simp at hsum'
    omega
  · have ha : a ≤ 2 := hall ⟨0, Nat.zero_lt_two⟩
    have hb : b ≤ 2 := hall ⟨1, Nat.one_lt_two⟩
    simp [List.sum_cons] at hsum'
    have ha2 : a = 2 := by omega
    have hb2 : b = 2 := by omega
    subst ha2
    subst hb2
    rfl
  · exfalso
    have : (a :: b :: c' :: t).length = t.length + 3 := by simp
    omega

/-- Degree arithmetic for `[SF₄]`: `m₂` of two degree `-1` generators lands in
degree `-2`. Kept as a named lemma so the statement of `sf₄` stays readable. -/
lemma neg_one_add_neg_one : (-1 : ℤ) + -1 = -2 := rfl

set_option maxHeartbeats 1600000 in
theorem sf₄ {A B C D E : KLRWCategory n R}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E) :
    mTwo (R := R) neg_one_add_neg_one (β.gen₂ f g) (β.gen₂ h k) = 0 := by
  have hsf := β.toFunctor.sf 4 ![A, B, C, D, E] ![(0 : ℤ), 0, 0, 0] (klrwQuad f g h k)
  -- every insertion term dies: s ≤ 2 → outer component f₃/f₄ = 0 (trunc);
  -- s ≥ 3 → inner μₛᴷᴸᴿᵂ = 0.
  have hL : indexedSFLeftSum (β := ℤ) (R := R) (n := (4 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C, D, E] ![(0 : ℤ), 0, 0, 0] (klrwQuad f g h k) = 0 := by
    simp only [indexedSFLeftSum]
    apply Finset.sum_eq_zero
    rintro ⟨r, hrm⟩ -
    apply Finset.sum_eq_zero
    rintro ⟨s, hsm⟩ -
    have hmem := Finset.mem_Ico.mp hsm
    have hrr := Finset.mem_range.mp hrm
    have hv := validStasheffIndices_of_mem_ranges (n := 4) hrm hsm
    suffices hh : indexedSFLeftTerm (β := ℤ) (R := R) (n := (4 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          β.toFunctor.f ![A, B, C, D, E] ![(0 : ℤ), 0, 0, 0] (klrwQuad f g h k) r s hv.1 hv.2 = 0 by
      rw [hh, smul_zero]
    by_cases hs3 : s ≤ 2
    · exact indexedSFLeftTerm_outer_zero _ _ _ _ _ _ _ _
        (fun hh o d => β.trunc ⟨_, hh⟩ (by show 3 ≤ 4 + 1 - s; omega) o d)
    · push Not at hs3
      exact indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
        (fun hh o d => klrwM_zero_of_ge_three (by omega))
  -- the only surviving partition is [2, 2]
  have hR : indexedSFRightSum (β := ℤ) (R := R) (n := (4 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m
          β.toFunctor.f ![A, B, C, D, E] ![(0 : ℤ), 0, 0, 0] (klrwQuad f g h k) =
      indexedSFRightTerm (β := ℤ) (R := R) (n := (4 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m
          β.toFunctor.f ![A, B, C, D, E] ![(0 : ℤ), 0, 0, 0] (klrwQuad f g h k) (⟨[2, 2], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 4) := by
    simp only [indexedSFRightSum]
    refine Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) ?_
    intro c _ hc
    by_cases hlen : 3 ≤ c.length
    · exact indexedSFRightTerm_outer_zero _ _ _ _ _ _ _ _ _
        (fun hh o d => bccM_zero_of_ge_three hlen)
    by_cases hblk : ∃ j : Fin c.length, 3 ≤ c.blocksFun j
    · obtain ⟨j, hj⟩ := hblk
      exact indexedSFRightTerm_inner_zero _ _ _ _ _ _ _ _ _ j
        (fun hh o d => β.trunc ⟨_, hh⟩ hj o d)
    · exfalso
      apply hc
      push Not at hblk hlen
      exact composition_four_eq_two_two c (by omega) (fun j => Nat.lt_succ_iff.mp (hblk j))
  -- μ₂ᵇᶜᶜ(f₂(f, g), f₂(h, k)) = mTwo (gen₂ f g) (gen₂ h k)
  have hbr : indexedSFRightTerm (β := ℤ) (R := R) (n := (4 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
          β.toFunctor.obj
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m
          β.toFunctor.f ![A, B, C, D, E] ![(0 : ℤ), 0, 0, 0] (klrwQuad f g h k) (⟨[2, 2], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 4) =
      mTwo (R := R) neg_one_add_neg_one (β.gen₂ f g) (β.gen₂ h k) := by
    simp only [indexedSFRightTerm]
    refine eq_of_heq ?_
    refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
    refine mlm_apply_congr_heq
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
      (fun o d => (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m (n := ⟨2, Nat.zero_lt_two⟩) o d) ?_ ?_ ?_
    · exact funext fun j => by fin_cases j <;> rfl
    · exact funext fun j => by fin_cases j <;> rfl
    · refine Function.hfunext rfl fun a a' haa => ?_
      obtain ⟨av, ha⟩ := a
      obtain ⟨av', ha'⟩ := a'
      have ha2 : av < 2 := ha
      have ha2' : av' < 2 := ha'
      have hvv : av = av' := congrArg Fin.val (eq_of_heq haa)
      subst hvv
      interval_cases av
      · refine HEq.trans (eq_mpr_heq _ _) ?_
        refine HEq.trans (eq_mp_heq _ _) ?_
        refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
        refine (mlm_apply_congr_heq (klrwHom (R := R) (n := n))
          (fun o d => β.toFunctor.f (n := ⟨2, Nat.zero_lt_two⟩) o d) ?_ ?_ ?_).symm
        · exact funext fun i => by fin_cases i <;> rfl
        · exact funext fun i => by fin_cases i <;> rfl
        · refine Function.hfunext rfl fun b b' hbb => ?_
          obtain ⟨bv, hb⟩ := b
          obtain ⟨bv', hb'⟩ := b'
          have hb2 : bv < 2 := hb
          have hb2' : bv' < 2 := hb'
          have hvv : bv = bv' := congrArg Fin.val (eq_of_heq hbb)
          subst hvv
          interval_cases bv <;> exact HEq.rfl
      · refine HEq.trans (eq_mpr_heq _ _) ?_
        refine HEq.trans (eq_mp_heq _ _) ?_
        refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
        refine (mlm_apply_congr_heq (klrwHom (R := R) (n := n))
          (fun o d => β.toFunctor.f (n := ⟨2, Nat.zero_lt_two⟩) o d) ?_ ?_ ?_).symm
        · exact funext fun i => by fin_cases i <;> rfl
        · exact funext fun i => by fin_cases i <;> rfl
        · refine Function.hfunext rfl fun b b' hbb => ?_
          obtain ⟨bv, hb⟩ := b
          obtain ⟨bv', hb'⟩ := b'
          have hb2 : bv < 2 := hb
          have hb2' : bv' < 2 := hb'
          have hvv : bv = bv' := congrArg Fin.val (eq_of_heq hbb)
          subst hvv
          interval_cases bv <;> exact HEq.rfl
  exact hbr.symm.trans (hR.symm.trans (hsf.symm.trans hL))

/-! ### The axioms in differential / `FinCochain` language -/

theorem sf₁_fin {A B : KLRWCategory n R} (f : A ⟶ B) :
    (β.gen₁ f).δ_fin = 0 := by
  have h := β.sf₁ f
  rw [mOne_eq] at h
  simpa using h

theorem sf₂_fin {A B C : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) :
    β.gen₁ (f ≫ g) =
      (β.gen₁ f).comp (β.gen₁ g) +≡ (β.gen₂ f g).δ_fin := by
  have h := β.sf₂ f g
  rw [mTwo_eq, mOne_eq] at h
  simpa [Int.negOnePow_zero] using h

theorem sf₃_fin {A B C D : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    β.gen₂ f (g ≫ h) + β.gen₂ (f ≫ g) h =
      FinCochain.zeroComp (β.gen₁ f) (β.gen₂ g h) +
        FinCochain.compZero (β.gen₂ f g) (β.gen₁ h) := by
  have hsf := β.sf₃ f g h
  rw [mTwo_eq, mTwo_eq] at hsf
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Int.negOnePow_zero, one_smul,
    Units.neg_smul, finCochain_neg_eq_self] at hsf
  exact hsf

/-- `[SF₄]` in `FinCochain` language. (Sign-free over any ring: the sign is
absorbed by the vanishing right-hand side.) -/
theorem sf₄_fin {A B C D E : KLRWCategory n R}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E) :
    (β.gen₂ f g).comp (β.gen₂ h k) = 0 := by
  have hsf := β.sf₄ f g h k
  rw [mTwo_eq] at hsf
  simpa using hsf

/-! ### Constructing a datum from generators

`ofGenerators` is the intended entry point for concrete instances: supply the
object map, the unary component as an `R`-linear map on strand spaces, the
binary component as an `R`-bilinear map, and proofs of the four truncated
axioms in the differential/composition language. The constructor packages the
components into the full arity-indexed multilinear family (zero above level
two and off degree-zero chains).

TODO(sf-converse): the `sf` field below — the general `[SFₙ]` equation for the
packaged family — is the converse direction of the specialization theorems
`sf₁`–`sf₄`: on degree-zero chains it reduces to the four supplied axioms
(arities 1–4) and to `0 = 0` (arities ≥ 5, every term containing a `μₖ≥₃`,
`μ₁ᴷᴸᴿᵂ`, or vanishing component); off degree-zero chains every term dies
because the packaged components vanish there by definition and the source
operations vanish away from degree zero. -/

/-- The unary component of `ofGenerators` on a degree-zero chain, as a
multilinear map. -/
def genOneMultilinear
    (g₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R)))
    (g₁ : ∀ {A B : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] FinCochain (g₀ A) (g₀ B) 0)
    (objs : Fin (1 + 1) → KLRWCategory n R) (deg : Fin 1 → ℤ)
    (h1 : deg ⟨0, Nat.one_pos⟩ = 0) :
    MultilinearMap R
      (fun i : Fin 1 => (composableHomType (β := ℤ) (R := R)
        (klrwHom (R := R) (n := n)) objs deg i))
      (FinCochain (g₀ (objs 0)) (g₀ (objs (Fin.last 1))) 0) := by
  exact
    { toFun := fun v =>
        ((g₁ (A := objs 0) (B := objs (Fin.last 1))).comp
          (klrwDegCast (R := R) (A := objs 0) (B := objs (Fin.last 1)) h1))
        (v ⟨0, Nat.one_pos⟩)
      map_update_add' := fun v i x y => by
        fin_cases i
        simpa using map_add ((g₁ (A := objs 0) (B := objs (Fin.last 1))).comp
          (klrwDegCast (R := R) (A := objs 0) (B := objs (Fin.last 1)) h1)) x y
      map_update_smul' := fun v i r x => by
        fin_cases i
        simpa using map_smul ((g₁ (A := objs 0) (B := objs (Fin.last 1))).comp
          (klrwDegCast (R := R) (A := objs 0) (B := objs (Fin.last 1)) h1)) r x }

/-- The binary component of `ofGenerators` on a degree-`(0,0)` chain, as a
multilinear map. -/
def genTwoMultilinear
    (g₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R)))
    (g₂ : ∀ {A B C : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] (B ⟶ C) →ₗ[R] FinCochain (g₀ A) (g₀ C) (-1))
    (objs : Fin (2 + 1) → KLRWCategory n R) (deg : Fin 2 → ℤ)
    (h1 : deg ⟨0, Nat.zero_lt_two⟩ = 0) (h2 : deg ⟨1, Nat.one_lt_two⟩ = 0) :
    MultilinearMap R
      (fun i : Fin 2 => (composableHomType (β := ℤ) (R := R)
        (klrwHom (R := R) (n := n)) objs deg i))
      (FinCochain (g₀ (objs 0)) (g₀ (objs (Fin.last 2))) (-1)) := by
  exact
    { toFun := fun v => (LinearMap.compl₁₂
        (g₂ (A := objs 0) (B := objs 1) (C := objs (Fin.last 2)))
        (klrwDegCast (R := R) (A := objs 0) (B := objs 1) h1)
        (klrwDegCast (R := R) (A := objs 1) (B := objs (Fin.last 2)) h2))
        (v ⟨0, Nat.zero_lt_two⟩) (v ⟨1, Nat.one_lt_two⟩)
      map_update_add' := fun v i x y => by
        fin_cases i
        · simpa using LinearMap.map_add₂ (LinearMap.compl₁₂
        (g₂ (A := objs 0) (B := objs 1) (C := objs (Fin.last 2)))
        (klrwDegCast (R := R) (A := objs 0) (B := objs 1) h1)
        (klrwDegCast (R := R) (A := objs 1) (B := objs (Fin.last 2)) h2)) x y _
        · simpa using map_add ((LinearMap.compl₁₂
        (g₂ (A := objs 0) (B := objs 1) (C := objs (Fin.last 2)))
        (klrwDegCast (R := R) (A := objs 0) (B := objs 1) h1)
        (klrwDegCast (R := R) (A := objs 1) (B := objs (Fin.last 2)) h2)) _) x y
      map_update_smul' := fun v i r x => by
        fin_cases i
        · simpa using LinearMap.map_smul₂ (LinearMap.compl₁₂
        (g₂ (A := objs 0) (B := objs 1) (C := objs (Fin.last 2)))
        (klrwDegCast (R := R) (A := objs 0) (B := objs 1) h1)
        (klrwDegCast (R := R) (A := objs 1) (B := objs (Fin.last 2)) h2)) r x _
        · simpa using map_smul ((LinearMap.compl₁₂
        (g₂ (A := objs 0) (B := objs 1) (C := objs (Fin.last 2)))
        (klrwDegCast (R := R) (A := objs 0) (B := objs 1) h1)
        (klrwDegCast (R := R) (A := objs 1) (B := objs (Fin.last 2)) h2)) _) r x }

/-- The arity-indexed component family of `ofGenerators`: `β₁`/`β₂` on
degree-zero chains of arities one and two, zero elsewhere. -/
def genFamily
    (g₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R)))
    (g₁ : ∀ {A B : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] FinCochain (g₀ A) (g₀ B) 0)
    (g₂ : ∀ {A B C : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] (B ⟶ C) →ₗ[R] FinCochain (g₀ A) (g₀ C) (-1))
    {k : ℕ+} (objs : Fin ((k : ℕ) + 1) → KLRWCategory n R)
    (deg : Fin (k : ℕ) → ℤ) :
    MultilinearMap R
      (fun i : Fin (k : ℕ) => (composableHomType (β := ℤ) (R := R)
        (klrwHom (R := R) (n := n)) objs deg i))
      (functorTargetType (β := ℤ) (R := R)
        (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom g₀ objs deg) := by
  obtain ⟨k, hk⟩ := k
  match k with
  | 0 => exact absurd hk (Nat.lt_irrefl 0)
  | 1 =>
    -- f₁ = β₁ on degree-0 chains, zero elsewhere
    exact
      if h : deg ⟨0, hk⟩ = 0 then
        (FinCochain.degCast (R := R) (A := g₀ (objs 0))
          (B := g₀ (objs (Fin.last 1)))
          (show (0 : ℤ) = functorTargetDeg deg from by
            have h0 : ∀ i, deg i = 0 := fun i => by fin_cases i; exact h
            simp [functorTargetDeg, shift_ofInt_int, h0])).compMultilinearMap
          (genOneMultilinear g₀ @g₁ objs deg h)
      else 0
  | 2 =>
    -- f₂ = β₂ on degree-(0,0) chains, zero elsewhere
    exact
      if h : deg ⟨0, hk⟩ = 0 ∧ deg ⟨1, Nat.lt_succ_self 1⟩ = 0 then
        (FinCochain.degCast (R := R) (A := g₀ (objs 0))
          (B := g₀ (objs (Fin.last 2)))
          (show (-1 : ℤ) = functorTargetDeg deg from by
            have h0 : ∀ i, deg i = 0 := fun i => by
              fin_cases i
              exacts [h.1, h.2]
            simp [functorTargetDeg, shift_ofInt_int, Fin.sum_univ_two,
              h0])).compMultilinearMap
          (genTwoMultilinear g₀ @g₂ objs deg h.1 h.2)
      else 0
  | _ + 3 =>
    -- fₖ = 0 for k ≥ 3
    exact 0

-- The family vanishes at arities ≥ 3 (definitionally).
private lemma genFamily_zero_of_ge_three
    (g₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R)))
    (g₁ : ∀ {A B : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] FinCochain (g₀ A) (g₀ B) 0)
    (g₂ : ∀ {A B C : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] (B ⟶ C) →ₗ[R] FinCochain (g₀ A) (g₀ C) (-1))
    {j : ℕ} (hj : 3 ≤ j)
    {objs : Fin (j + 1) → KLRWCategory n R} {deg : Fin j → ℤ} :
    genFamily g₀ @g₁ @g₂ (k := ⟨j, by omega⟩) objs deg = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
  rfl

-- Arities ≥ 5 of the SF equation: both sides vanish identically.
private lemma sfconv_ge_five
    (g₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R)))
    (g₁ : ∀ {A B : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] FinCochain (g₀ A) (g₀ B) 0)
    (g₂ : ∀ {A B C : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] (B ⟶ C) →ₗ[R] FinCochain (g₀ A) (g₀ C) (-1))
    (j : ℕ)
    (objs : Fin (j + 5 + 1) → KLRWCategory n R)
    (x : ∀ i : Fin (j + 5), composableHomType (β := ℤ) (R := R)
      (klrwHom (R := R) (n := n)) objs (fun _ => (0 : ℤ)) i) :
    indexedSFLeftSum (β := ℤ) (R := R) (n := ⟨j + 5, by omega⟩)
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x =
    indexedSFRightSum (β := ℤ) (R := R) (n := ⟨j + 5, by omega⟩)
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x := by
  have hL : indexedSFLeftSum (β := ℤ) (R := R) (n := ⟨j + 5, by omega⟩)
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x = 0 := by
    simp only [indexedSFLeftSum]
    apply Finset.sum_eq_zero
    rintro ⟨r, hrm⟩ -
    apply Finset.sum_eq_zero
    rintro ⟨s, hsm⟩ -
    have hmem := Finset.mem_Ico.mp hsm
    have hrr := Finset.mem_range.mp hrm
    have hv := validStasheffIndices_of_mem_ranges (n := j + 5) hrm hsm
    suffices hh : indexedSFLeftTerm (β := ℤ) (R := R) (n := ⟨j + 5, by omega⟩)
        (klrwAInfinityPreCategory (R := R) (n := n)).Hom
        (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
        g₀
        (klrwAInfinityPreCategory (R := R) (n := n)).m
        (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x r s hv.1 hv.2 = 0 by
      rw [hh, smul_zero]
    by_cases hs3 : s ≤ 2
    · -- outer arity (j+5)+1−s ≥ 4: the component vanishes by definition
      exact indexedSFLeftTerm_outer_zero _ _ _ _ _ _ _ _
        (fun hh o d => genFamily_zero_of_ge_three g₀ @g₁ @g₂
          (by show 3 ≤ j + 5 + 1 - s; omega))
    · -- inner arity s ≥ 3: the source operation vanishes
      push Not at hs3
      exact indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
        (fun hh o d => klrwM_zero_of_ge_three (by omega))
  have hR : indexedSFRightSum (β := ℤ) (R := R) (n := ⟨j + 5, by omega⟩)
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x = 0 := by
    simp only [indexedSFRightSum]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hlen : 3 ≤ c.length
    · exact indexedSFRightTerm_outer_zero _ _ _ _ _ _ _ _ _
        (fun hh o d => bccM_zero_of_ge_three hlen)
    by_cases hblk : ∃ jj : Fin c.length, 3 ≤ c.blocksFun jj
    · obtain ⟨jj, hjj⟩ := hblk
      exact indexedSFRightTerm_inner_zero _ _ _ _ _ _ _ _ _ jj
        (fun hh o d => genFamily_zero_of_ge_three g₀ @g₁ @g₂ hjj)
    · exfalso
      push Not at hblk hlen
      have hb := Finset.sum_le_card_nsmul Finset.univ c.blocksFun 2
        (fun jj _ => Nat.lt_succ_iff.mp (hblk jj))
      have hs2 : Finset.univ.sum c.blocksFun = j + 5 := c.sum_blocksFun
      simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hb
      omega
  exact hL.trans hR.symm

-- Arity-1 converse: [SF₁] for the packaged family.
private lemma sfconv_one
    (g₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R)))
    (g₁ : ∀ {A B : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] FinCochain (g₀ A) (g₀ B) 0)
    (g₂ : ∀ {A B C : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] (B ⟶ C) →ₗ[R] FinCochain (g₀ A) (g₀ C) (-1))
    (hsf₁ : ∀ {A B : KLRWCategory n R} (f : A ⟶ B), (g₁ f).δ_fin = 0)
    (objs : Fin ((1 : ℕ+).val + 1) → KLRWCategory n R)
    (x : ∀ i : Fin ((1 : ℕ+).val), composableHomType (β := ℤ) (R := R)
      (klrwHom (R := R) (n := n)) objs (fun _ => (0 : ℤ)) i) :
    indexedSFLeftSum (β := ℤ) (R := R) (n := (1 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x =
    indexedSFRightSum (β := ℤ) (R := R) (n := (1 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x := by
  have hL : indexedSFLeftSum (β := ℤ) (R := R) (n := (1 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x = 0 := by
    simp only [indexedSFLeftSum]
    apply Finset.sum_eq_zero
    rintro ⟨r, hrm⟩ -
    apply Finset.sum_eq_zero
    rintro ⟨s, hsm⟩ -
    have hv := validStasheffIndices_of_mem_ranges (n := 1) hrm hsm
    suffices hh : indexedSFLeftTerm (β := ℤ) (R := R) (n := (1 : ℕ+))
        (klrwAInfinityPreCategory (R := R) (n := n)).Hom
        (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
        g₀
        (klrwAInfinityPreCategory (R := R) (n := n)).m
        (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x r s hv.1 hv.2 = 0 by
      rw [hh, smul_zero]
    have hs1 : s = 1 := by have := hv.1; have := hv.2; omega
    subst hs1
    exact indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
      (fun hh o d => klrwM_one_eq_zero hh o d)
  have hR : indexedSFRightSum (β := ℤ) (R := R) (n := (1 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x =
      indexedSFRightTerm (β := ℤ) (R := R) (n := (1 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x (Composition.ones 1) := by
    simp only [indexedSFRightSum]
    exact Finset.sum_eq_single_of_mem _ (Finset.mem_univ _)
      (fun c _ hc => absurd (composition_one_eq c) hc)
  have hbr : indexedSFRightTerm (β := ℤ) (R := R) (n := (1 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x (Composition.ones 1) =
      mOne (R := R) (zero_add 1)
        (g₁ (A := objs 0) (B := objs (Fin.last 1)) (x ⟨0, Nat.one_pos⟩)) := by
    simp only [indexedSFRightTerm]
    refine eq_of_heq ?_
    refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
    refine mlm_apply_congr_heq
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      (fun o d => (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m (n := ⟨1, Nat.one_pos⟩) o d) ?_ ?_ ?_
    · exact funext fun j => by fin_cases j <;> rfl
    · exact funext fun j => by fin_cases j <;> rfl
    · refine Function.hfunext rfl fun a a' haa => ?_
      obtain ⟨av, ha⟩ := a
      obtain ⟨av', ha'⟩ := a'
      have ha2 : av < 1 := ha
      have ha2' : av' < 1 := ha'
      interval_cases av
      interval_cases av'
      refine HEq.trans (eq_mpr_heq _ _) ?_
      refine HEq.trans (eq_mp_heq _ _) ?_
      exact HEq.rfl
  rw [hL, hR, hbr, mOne_eq, hsf₁, map_zero]
  rfl

set_option maxHeartbeats 3200000 in
-- Arity-2 converse: [SF₂] for the packaged family.
private lemma sfconv_two
    (g₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R)))
    (g₁ : ∀ {A B : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] FinCochain (g₀ A) (g₀ B) 0)
    (g₂ : ∀ {A B C : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] (B ⟶ C) →ₗ[R] FinCochain (g₀ A) (g₀ C) (-1))
    (hsf₁ : ∀ {A B : KLRWCategory n R} (f : A ⟶ B),
      (g₁ f).δ_fin = 0)
    (hsf₂ : ∀ {A B C : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C),
      g₁ (f ≫ g) =
        FinCochain.degCast (R := R) (zero_add 0)
          ((g₁ f).comp (g₁ g)) +
        FinCochain.degCast (R := R) (neg_add_cancel 1)
          (g₂ f g).δ_fin)
    (hsf₃ : ∀ {A B C D : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D),
      g₂ f (g ≫ h) + g₂ (f ≫ g) h =
        FinCochain.zeroComp (g₁ f) (g₂ g h) +
          FinCochain.compZero (g₂ f g) (g₁ h))
    (hsf₄ : ∀ {A B C D E : KLRWCategory n R}
      (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E),
      (g₂ f g).comp (g₂ h k) = 0)
    (objs : Fin ((2 : ℕ+).val + 1) → KLRWCategory n R)
    (x : ∀ i : Fin ((2 : ℕ+).val), composableHomType (β := ℤ) (R := R)
      (klrwHom (R := R) (n := n)) objs (fun _ => (0 : ℤ)) i) :
    indexedSFLeftSum (β := ℤ) (R := R) (n := (2 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x =
    indexedSFRightSum (β := ℤ) (R := R) (n := (2 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x := by
  -- the insertion sum collapses to the single term (r, s) = (0, 2), sign +1
  have e2 : indexedSFLeftSum (β := ℤ) (R := R) (n := (2 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x =
      indexedSFLeftTerm (β := ℤ) (R := R) (n := (2 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x 0 2 (by norm_num) (by norm_num) := by
    simp only [indexedSFLeftSum]
    refine (Finset.sum_eq_single_of_mem ⟨0, by decide⟩ (Finset.mem_attach _ _) ?_).trans
      ((Finset.sum_eq_single_of_mem ⟨2, by decide⟩ (Finset.mem_attach _ _) ?_).trans ?_)
    · rintro ⟨r, hrm⟩ - hne
      apply Finset.sum_eq_zero
      rintro ⟨s, hsm⟩ -
      have hmem := Finset.mem_Ico.mp hsm
      have hr0 : r ≠ 0 := fun hh => hne (Subtype.ext hh)
      have hrr := Finset.mem_range.mp hrm
      have hv := validStasheffIndices_of_mem_ranges (n := 2) hrm hsm
      suffices hh : indexedSFLeftTerm (β := ℤ) (R := R) (n := (2 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
            (V := CMat_ (KLRWCategory n R))).Hom
          g₀
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x r s hv.1 hv.2 = 0 by
        rw [hh, smul_zero]
      have hs1 : s = 1 := by omega
      subst hs1
      exact indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
        (fun hh o d => klrwM_one_eq_zero hh o d)
    · rintro ⟨s, hsm⟩ - hne
      have hmem := Finset.mem_Ico.mp hsm
      have hs2 : s ≠ 2 := fun hh => hne (Subtype.ext hh)
      have hv := validStasheffIndices_of_mem_ranges (n := 2) (by decide) hsm
      suffices hh : indexedSFLeftTerm (β := ℤ) (R := R) (n := (2 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
            (V := CMat_ (KLRWCategory n R))).Hom
          g₀
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x 0 s hv.1 hv.2 = 0 by
        rw [hh, smul_zero]
      have hs1 : s = 1 := by omega
      subst hs1
      exact indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
        (fun hh o d => klrwM_one_eq_zero hh o d)
    · exact one_smul ℤ _
  -- that term is g₁ applied to the composite (μ₂ᴷᴸᴿᵂ collapses to ≫)
  have e1 : indexedSFLeftTerm (β := ℤ) (R := R) (n := (2 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x 0 2 (by norm_num) (by norm_num) =
      g₁ (A := objs 0) (B := objs (Fin.last 2))
        (CategoryStruct.comp (X := objs 0) (Y := objs 1) (Z := objs (Fin.last 2))
          (x ⟨0, Nat.zero_lt_two⟩) (x ⟨1, Nat.one_lt_two⟩)) := by
    simp only [indexedSFLeftTerm]
    refine eq_of_heq ?_
    exact HEq.rfl
  -- the partition sum has exactly the compositions [1,1] and [2]
  have hne2 : Composition.ones 2 ≠ Composition.single 2 (by norm_num) := by decide
  have e3 : indexedSFRightSum (β := ℤ) (R := R) (n := (2 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x =
      indexedSFRightTerm (β := ℤ) (R := R) (n := (2 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x (Composition.ones 2) +
        indexedSFRightTerm (β := ℤ) (R := R) (n := (2 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x (Composition.single 2 (by norm_num)) := by
    simp only [indexedSFRightSum]
    rw [show (Finset.univ : Finset (Composition ((2 : ℕ+) : ℕ))) =
        {Composition.ones 2, Composition.single 2 (by norm_num)} from by
        ext c
        refine ⟨fun _ => ?_, fun _ => Finset.mem_univ c⟩
        rcases composition_two_cases c with rfl | rfl
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)]
    exact Finset.sum_pair hne2
  -- μ₂ᵇᶜᶜ(f₁ x₀, f₁ x₁) = mTwo (g₁ x₀) (g₁ x₁)
  have e4 : indexedSFRightTerm (β := ℤ) (R := R) (n := (2 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x (Composition.ones 2) =
      mTwo (R := R) (zero_add 0)
        (g₁ (A := objs 0) (B := objs 1) (x ⟨0, Nat.zero_lt_two⟩))
        (g₁ (A := objs 1) (B := objs (Fin.last 2)) (x ⟨1, Nat.one_lt_two⟩)) := by
    simp only [indexedSFRightTerm]
    refine eq_of_heq ?_
    refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
    refine mlm_apply_congr_heq
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      (fun o d => (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m (n := ⟨2, Nat.zero_lt_two⟩) o d) ?_ ?_ ?_
    · exact funext fun j => by fin_cases j <;> rfl
    · exact funext fun j => by fin_cases j <;> rfl
    · refine Function.hfunext rfl fun a a' haa => ?_
      obtain ⟨av, ha⟩ := a
      obtain ⟨av', ha'⟩ := a'
      have ha2 : av < 2 := ha
      have ha2' : av' < 2 := ha'
      have hvv : av = av' := congrArg Fin.val (eq_of_heq haa)
      subst hvv
      interval_cases av
      · refine HEq.trans (eq_mpr_heq _ _) ?_
        refine HEq.trans (eq_mp_heq _ _) ?_
        exact HEq.rfl
      · refine HEq.trans (eq_mpr_heq _ _) ?_
        refine HEq.trans (eq_mp_heq _ _) ?_
        exact HEq.rfl
  -- μ₁ᵇᶜᶜ(f₂(x₀, x₁)) = mOne (g₂ x₀ x₁)
  have e5 : indexedSFRightTerm (β := ℤ) (R := R) (n := (2 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x (Composition.single 2 (by norm_num)) =
      mOne (R := R) (neg_add_cancel 1)
        (g₂ (A := objs 0) (B := objs 1) (C := objs (Fin.last 2))
          (x ⟨0, Nat.zero_lt_two⟩) (x ⟨1, Nat.one_lt_two⟩)) := by
    simp only [indexedSFRightTerm]
    refine eq_of_heq ?_
    refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
    refine mlm_apply_congr_heq
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      (fun o d => (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m (n := ⟨1, Nat.one_pos⟩) o d) ?_ ?_ ?_
    · exact funext fun j => by fin_cases j <;> rfl
    · exact funext fun j => by fin_cases j <;> rfl
    · refine Function.hfunext rfl fun a a' haa => ?_
      obtain ⟨av, ha⟩ := a
      obtain ⟨av', ha'⟩ := a'
      have ha2 : av < 1 := ha
      have ha2' : av' < 1 := ha'
      interval_cases av
      interval_cases av'
      refine HEq.trans (eq_mpr_heq _ _) ?_
      exact HEq.rfl
  rw [e2, e1, e3, e4, e5, mTwo_eq, mOne_eq, Int.negOnePow_zero, one_smul]
  exact hsf₂ _ _

set_option maxHeartbeats 3200000 in
-- Arity-3 converse: [SF₃] for the packaged family (uses `CharP R 2`).
private lemma sfconv_three
    (g₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R)))
    (g₁ : ∀ {A B : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] FinCochain (g₀ A) (g₀ B) 0)
    (g₂ : ∀ {A B C : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] (B ⟶ C) →ₗ[R] FinCochain (g₀ A) (g₀ C) (-1))
    (hsf₁ : ∀ {A B : KLRWCategory n R} (f : A ⟶ B),
      (g₁ f).δ_fin = 0)
    (hsf₂ : ∀ {A B C : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C),
      g₁ (f ≫ g) =
        FinCochain.degCast (R := R) (zero_add 0)
          ((g₁ f).comp (g₁ g)) +
        FinCochain.degCast (R := R) (neg_add_cancel 1)
          (g₂ f g).δ_fin)
    (hsf₃ : ∀ {A B C D : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D),
      g₂ f (g ≫ h) + g₂ (f ≫ g) h =
        FinCochain.zeroComp (g₁ f) (g₂ g h) +
          FinCochain.compZero (g₂ f g) (g₁ h))
    (hsf₄ : ∀ {A B C D E : KLRWCategory n R}
      (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E),
      (g₂ f g).comp (g₂ h k) = 0)
    (objs : Fin ((3 : ℕ+).val + 1) → KLRWCategory n R)
    (x : ∀ i : Fin ((3 : ℕ+).val), composableHomType (β := ℤ) (R := R)
      (klrwHom (R := R) (n := n)) objs (fun _ => (0 : ℤ)) i) :
    indexedSFLeftSum (β := ℤ) (R := R) (n := (3 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x =
    indexedSFRightSum (β := ℤ) (R := R) (n := (3 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x := by
  -- the insertion sum expands to the two survivors with signs −1, +1
  have hL : indexedSFLeftSum (β := ℤ) (R := R) (n := (3 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x =
      (-1 : ℤ) • indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
        (klrwAInfinityPreCategory (R := R) (n := n)).Hom
        (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
        g₀
        (klrwAInfinityPreCategory (R := R) (n := n)).m
        (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x 0 2 (by norm_num) (by norm_num) +
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
        (klrwAInfinityPreCategory (R := R) (n := n)).Hom
        (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
        g₀
        (klrwAInfinityPreCategory (R := R) (n := n)).m
        (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x 1 2 (by norm_num) (by norm_num) := by
    simp only [indexedSFLeftSum, PNat.val_ofNat]
    rw [show (Finset.range (3 + 1) : Finset ℕ).attach =
        ({⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩} :
          Finset { a // a ∈ Finset.range (3 + 1) }) from by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [show (Finset.Ico 1 (3 - (0 : ℕ) + 1) : Finset ℕ).attach =
        ({⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩} :
          Finset { a // a ∈ (Finset.Ico 1 (3 - (0 : ℕ) + 1) : Finset ℕ) }) from by decide]
    rw [show (Finset.Ico 1 (3 - (1 : ℕ) + 1) : Finset ℕ).attach =
        ({⟨1, by decide⟩, ⟨2, by decide⟩} :
          Finset { a // a ∈ (Finset.Ico 1 (3 - (1 : ℕ) + 1) : Finset ℕ) }) from by decide]
    rw [show (Finset.Ico 1 (3 - (2 : ℕ) + 1) : Finset ℕ).attach =
        ({⟨1, by decide⟩} :
          Finset { a // a ∈ (Finset.Ico 1 (3 - (2 : ℕ) + 1) : Finset ℕ) }) from by decide]
    rw [show (Finset.Ico 1 (3 - (3 : ℕ) + 1) : Finset ℕ).attach =
        (∅ : Finset { a // a ∈ (Finset.Ico 1 (3 - (3 : ℕ) + 1) : Finset ℕ) }) from by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, Finset.sum_insert (by decide), Finset.sum_singleton,
      Finset.sum_singleton, Finset.sum_empty]
    show stasheffSign (fun _ => (0 : ℤ)) 0 1 (by decide) •
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
            (V := CMat_ (KLRWCategory n R))).Hom
          g₀
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x 0 1 (by decide) (by decide) +
      ((-1 : ℤ) •
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
            (V := CMat_ (KLRWCategory n R))).Hom
          g₀
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x 0 2 (by decide) (by decide) +
        stasheffSign (fun _ => (0 : ℤ)) 0 3 (by decide) •
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
            (V := CMat_ (KLRWCategory n R))).Hom
          g₀
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x 0 3 (by decide) (by decide)) +
      (stasheffSign (fun _ => (0 : ℤ)) 1 1 (by decide) •
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
            (V := CMat_ (KLRWCategory n R))).Hom
          g₀
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x 1 1 (by decide) (by decide) +
        (1 : ℤ) •
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
            (V := CMat_ (KLRWCategory n R))).Hom
          g₀
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x 1 2 (by decide) (by decide) +
        (stasheffSign (fun _ => (0 : ℤ)) 2 1 (by decide) •
          indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
            (V := CMat_ (KLRWCategory n R))).Hom
          g₀
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x 2 1 (by decide) (by decide) +
          0)) = _
    have e01 : ∀ (hs : 1 ≤ 1) (hr : 0 + 1 ≤ 3),
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
            (V := CMat_ (KLRWCategory n R))).Hom
          g₀
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x 0 1 hs hr = 0 :=
      fun _ _ => indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
        (fun hh o d => klrwM_one_eq_zero hh o d)
    have e11 : ∀ (hs : 1 ≤ 1) (hr : 1 + 1 ≤ 3),
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
            (V := CMat_ (KLRWCategory n R))).Hom
          g₀
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x 1 1 hs hr = 0 :=
      fun _ _ => indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
        (fun hh o d => klrwM_one_eq_zero hh o d)
    have e21 : ∀ (hs : 1 ≤ 1) (hr : 2 + 1 ≤ 3),
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
            (V := CMat_ (KLRWCategory n R))).Hom
          g₀
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x 2 1 hs hr = 0 :=
      fun _ _ => indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
        (fun hh o d => klrwM_one_eq_zero hh o d)
    have e03 : ∀ (hs : 1 ≤ 3) (hr : 0 + 3 ≤ 3),
        indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
          (klrwAInfinityPreCategory (R := R) (n := n)).Hom
          (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
            (V := CMat_ (KLRWCategory n R))).Hom
          g₀
          (klrwAInfinityPreCategory (R := R) (n := n)).m
          (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x 0 3 hs hr = 0 :=
      fun _ _ => indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
        (fun hh o d => klrwM_zero_of_ge_three (by norm_num))
    rw [e01, e11, e21, e03]
    apply sf₃_key1
  -- the partition sum expands to the two surviving compositions [1,2], [2,1]
  have hR : indexedSFRightSum (β := ℤ) (R := R) (n := (3 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x =
      indexedSFRightTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x (⟨[1, 2], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 3) +
        indexedSFRightTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
        (klrwAInfinityPreCategory (R := R) (n := n)).Hom
        (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
        g₀
        (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).m
        (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x (⟨[2, 1], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 3) := by
    simp only [indexedSFRightSum]
    refine sum_eq_add_of_mem' (⟨[1, 2], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 3) (⟨[2, 1], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 3)
      (Finset.mem_univ _) (Finset.mem_univ _) (by decide) ?_
    intro c _ hc1 hc2
    rcases composition_three_cases c with rfl | rfl | rfl | rfl
    · exact indexedSFRightTerm_outer_zero _ _ _ _ _ _ _ _ _
        (fun hh o d => bccM_zero_of_ge_three (Nat.le_refl 3))
    · exact absurd rfl hc1
    · exact absurd rfl hc2
    · exact indexedSFRightTerm_inner_zero _ _ _ _ _ _ _ _ _ ⟨0, Nat.one_pos⟩
        (fun hh o d => genFamily_zero_of_ge_three g₀ @g₁ @g₂ (Nat.le_refl 3))
  -- bridges: the surviving insertion terms are g₂ of composites
  have ebL1 : indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x 1 2 (by norm_num) (by norm_num) =
      g₂ (A := objs 0) (B := objs 1) (C := objs (Fin.last 3)) (x ⟨0, by decide⟩)
        (CategoryStruct.comp (X := objs 1) (Y := objs 2) (Z := objs (Fin.last 3))
          (x ⟨1, by decide⟩) (x ⟨2, by decide⟩)) := by
    simp only [indexedSFLeftTerm]
    refine eq_of_heq ?_
    exact HEq.rfl
  have ebL2 : indexedSFLeftTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x 0 2 (by norm_num) (by norm_num) =
      g₂ (A := objs 0) (B := objs 2) (C := objs (Fin.last 3))
        (CategoryStruct.comp (X := objs 0) (Y := objs 1) (Z := objs 2)
          (x ⟨0, by decide⟩) (x ⟨1, by decide⟩)) (x ⟨2, by decide⟩) := by
    simp only [indexedSFLeftTerm]
    refine eq_of_heq ?_
    exact HEq.rfl
  -- bridges: the surviving partition terms are the mTwo's
  have ebR1 : indexedSFRightTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x (⟨[1, 2], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 3) =
      mTwo (R := R) (zero_add (-1))
        (g₁ (A := objs 0) (B := objs 1) (x ⟨0, by decide⟩))
        (g₂ (A := objs 1) (B := objs 2) (C := objs (Fin.last 3)) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩)) := by
    simp only [indexedSFRightTerm]
    refine eq_of_heq ?_
    refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
    refine mlm_apply_congr_heq
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      (fun o d => (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m (n := ⟨2, Nat.zero_lt_two⟩) o d) ?_ ?_ ?_
    · exact funext fun j => by fin_cases j <;> rfl
    · exact funext fun j => by fin_cases j <;> rfl
    · refine Function.hfunext rfl fun a a' haa => ?_
      obtain ⟨av, ha⟩ := a
      obtain ⟨av', ha'⟩ := a'
      have ha2 : av < 2 := ha
      have ha2' : av' < 2 := ha'
      have hvv : av = av' := congrArg Fin.val (eq_of_heq haa)
      subst hvv
      interval_cases av
      · refine HEq.trans (eq_mpr_heq _ _) ?_
        refine HEq.trans (eq_mp_heq _ _) ?_
        exact HEq.rfl
      · refine HEq.trans (eq_mpr_heq _ _) ?_
        refine HEq.trans (eq_mp_heq _ _) ?_
        exact HEq.rfl
  have ebR2 : indexedSFRightTerm (β := ℤ) (R := R) (n := (3 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x (⟨[2, 1], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 3) =
      mTwo (R := R) (add_zero (-1))
        (g₂ (A := objs 0) (B := objs 1) (C := objs 2) (x ⟨0, by decide⟩) (x ⟨1, by decide⟩))
        (g₁ (A := objs 2) (B := objs (Fin.last 3)) (x ⟨2, by decide⟩)) := by
    simp only [indexedSFRightTerm]
    refine eq_of_heq ?_
    refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
    refine mlm_apply_congr_heq
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      (fun o d => (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m (n := ⟨2, Nat.zero_lt_two⟩) o d) ?_ ?_ ?_
    · exact funext fun j => by fin_cases j <;> rfl
    · exact funext fun j => by fin_cases j <;> rfl
    · refine Function.hfunext rfl fun a a' haa => ?_
      obtain ⟨av, ha⟩ := a
      obtain ⟨av', ha'⟩ := a'
      have ha2 : av < 2 := ha
      have ha2' : av' < 2 := ha'
      have hvv : av = av' := congrArg Fin.val (eq_of_heq haa)
      subst hvv
      interval_cases av
      · refine HEq.trans (eq_mpr_heq _ _) ?_
        refine HEq.trans (eq_mp_heq _ _) ?_
        exact HEq.rfl
      · refine HEq.trans (eq_mpr_heq _ _) ?_
        refine HEq.trans (eq_mp_heq _ _) ?_
        exact HEq.rfl
  -- the truncated axiom, in mTwo language
  have hkey : g₂ (A := objs 0) (B := objs 1) (C := objs (Fin.last 3)) (x ⟨0, by decide⟩)
        (CategoryStruct.comp (X := objs 1) (Y := objs 2) (Z := objs (Fin.last 3))
          (x ⟨1, by decide⟩) (x ⟨2, by decide⟩)) +
      g₂ (A := objs 0) (B := objs 2) (C := objs (Fin.last 3))
        (CategoryStruct.comp (X := objs 0) (Y := objs 1) (Z := objs 2)
          (x ⟨0, by decide⟩) (x ⟨1, by decide⟩)) (x ⟨2, by decide⟩) =
      mTwo (R := R) (zero_add (-1))
        (g₁ (A := objs 0) (B := objs 1) (x ⟨0, by decide⟩))
        (g₂ (A := objs 1) (B := objs 2) (C := objs (Fin.last 3)) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩)) +
      mTwo (R := R) (add_zero (-1))
        (g₂ (A := objs 0) (B := objs 1) (C := objs 2) (x ⟨0, by decide⟩) (x ⟨1, by decide⟩))
        (g₁ (A := objs 2) (B := objs (Fin.last 3)) (x ⟨2, by decide⟩)) := by
    rw [mTwo_eq, mTwo_eq]
    simp only [Int.negOnePow_neg, Int.negOnePow_one, Int.negOnePow_zero, one_smul,
      Units.neg_smul, finCochain_neg_eq_self]
    exact hsf₃ _ _ _
  -- assemble over char 2 (the (0,2) insertion sign is −1)
  refine hL.trans ?_
  refine ((sf₃_key2 (S := R) _ _).symm).trans ?_
  refine (congrArg₂ (· + ·) ebL1 ebL2).trans ?_
  refine hkey.trans ?_
  exact (congrArg₂ (· + ·) ebR1.symm ebR2.symm).trans hR.symm

set_option maxHeartbeats 1600000 in
-- Arity-4 converse: [SF₄] for the packaged family.
private lemma sfconv_four
    (g₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R)))
    (g₁ : ∀ {A B : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] FinCochain (g₀ A) (g₀ B) 0)
    (g₂ : ∀ {A B C : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] (B ⟶ C) →ₗ[R] FinCochain (g₀ A) (g₀ C) (-1))
    (hsf₁ : ∀ {A B : KLRWCategory n R} (f : A ⟶ B),
      (g₁ f).δ_fin = 0)
    (hsf₂ : ∀ {A B C : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C),
      g₁ (f ≫ g) =
        FinCochain.degCast (R := R) (zero_add 0)
          ((g₁ f).comp (g₁ g)) +
        FinCochain.degCast (R := R) (neg_add_cancel 1)
          (g₂ f g).δ_fin)
    (hsf₃ : ∀ {A B C D : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D),
      g₂ f (g ≫ h) + g₂ (f ≫ g) h =
        FinCochain.zeroComp (g₁ f) (g₂ g h) +
          FinCochain.compZero (g₂ f g) (g₁ h))
    (hsf₄ : ∀ {A B C D E : KLRWCategory n R}
      (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E),
      (g₂ f g).comp (g₂ h k) = 0)
    (objs : Fin ((4 : ℕ+).val + 1) → KLRWCategory n R)
    (x : ∀ i : Fin ((4 : ℕ+).val), composableHomType (β := ℤ) (R := R)
      (klrwHom (R := R) (n := n)) objs (fun _ => (0 : ℤ)) i) :
    indexedSFLeftSum (β := ℤ) (R := R) (n := (4 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x =
    indexedSFRightSum (β := ℤ) (R := R) (n := (4 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x := by
  -- every insertion term dies: s ≤ 2 → outer arity ≥ 3 → component 0;
  -- s ≥ 3 → inner μₛᴷᴸᴿᵂ = 0
  have hL : indexedSFLeftSum (β := ℤ) (R := R) (n := (4 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x = 0 := by
    simp only [indexedSFLeftSum]
    apply Finset.sum_eq_zero
    rintro ⟨r, hrm⟩ -
    apply Finset.sum_eq_zero
    rintro ⟨s, hsm⟩ -
    have hmem := Finset.mem_Ico.mp hsm
    have hrr := Finset.mem_range.mp hrm
    have hv := validStasheffIndices_of_mem_ranges (n := 4) hrm hsm
    suffices hh : indexedSFLeftTerm (β := ℤ) (R := R) (n := (4 : ℕ+))
        (klrwAInfinityPreCategory (R := R) (n := n)).Hom
        (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
        g₀
        (klrwAInfinityPreCategory (R := R) (n := n)).m
        (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x r s hv.1 hv.2 = 0 by
      rw [hh, smul_zero]
    by_cases hs3 : s ≤ 2
    · exact indexedSFLeftTerm_outer_zero _ _ _ _ _ _ _ _
        (fun hh o d => genFamily_zero_of_ge_three g₀ @g₁ @g₂
          (by show 3 ≤ 4 + 1 - s; omega))
    · push Not at hs3
      exact indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
        (fun hh o d => klrwM_zero_of_ge_three (by omega))
  -- the only surviving partition is [2, 2]
  have hR : indexedSFRightSum (β := ℤ) (R := R) (n := (4 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x =
      indexedSFRightTerm (β := ℤ) (R := R) (n := (4 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x (⟨[2, 2], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 4) := by
    simp only [indexedSFRightSum]
    refine Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) ?_
    intro c _ hc
    by_cases hlen : 3 ≤ c.length
    · exact indexedSFRightTerm_outer_zero _ _ _ _ _ _ _ _ _
        (fun hh o d => bccM_zero_of_ge_three hlen)
    by_cases hblk : ∃ j : Fin c.length, 3 ≤ c.blocksFun j
    · obtain ⟨j, hj⟩ := hblk
      exact indexedSFRightTerm_inner_zero _ _ _ _ _ _ _ _ _ j
        (fun hh o d => genFamily_zero_of_ge_three g₀ @g₁ @g₂ hj)
    · exfalso
      apply hc
      push Not at hblk hlen
      exact composition_four_eq_two_two c (by omega) (fun j => Nat.lt_succ_iff.mp (hblk j))
  -- μ₂ᵇᶜᶜ(f₂(x₀, x₁), f₂(x₂, x₃)) = mTwo (g₂ x₀ x₁) (g₂ x₂ x₃)
  have hbr : indexedSFRightTerm (β := ℤ) (R := R) (n := (4 : ℕ+))
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs (fun _ => (0 : ℤ)) x (⟨[2, 2], fun hi => by fin_cases hi <;> norm_num, by decide⟩ : Composition 4) =
      mTwo (R := R) neg_one_add_neg_one
        (g₂ (A := objs 0) (B := objs 1) (C := objs 2)
          (x ⟨0, by decide⟩) (x ⟨1, by decide⟩))
        (g₂ (A := objs 2) (B := objs 3) (C := objs (Fin.last 4))
          (x ⟨2, by decide⟩) (x ⟨3, by decide⟩)) := by
    simp only [indexedSFRightTerm]
    refine eq_of_heq ?_
    refine HEq.trans ?_ (finCochain_degCast_heq _ _).symm
    refine mlm_apply_congr_heq
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      (fun o d => (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m (n := ⟨2, Nat.zero_lt_two⟩) o d) ?_ ?_ ?_
    · exact funext fun j => by fin_cases j <;> rfl
    · exact funext fun j => by fin_cases j <;> rfl
    · refine Function.hfunext rfl fun a a' haa => ?_
      obtain ⟨av, ha⟩ := a
      obtain ⟨av', ha'⟩ := a'
      have ha2 : av < 2 := ha
      have ha2' : av' < 2 := ha'
      have hvv : av = av' := congrArg Fin.val (eq_of_heq haa)
      subst hvv
      interval_cases av
      · refine HEq.trans (eq_mpr_heq _ _) ?_
        refine HEq.trans (eq_mp_heq _ _) ?_
        exact HEq.rfl
      · refine HEq.trans (eq_mpr_heq _ _) ?_
        refine HEq.trans (eq_mp_heq _ _) ?_
        exact HEq.rfl
  rw [hL, hR, hbr, mTwo_eq, hsf₄, map_zero, smul_zero]
  rfl

-- μ₂ᴷᴸᴿᵂ vanishes unless both slot degrees are zero (its defining `dite`).
private lemma klrwM_two_ne
    {obj : Fin 3 → KLRWCategory n R} {deg : Fin 2 → ℤ}
    (hk : 0 < 2) (h : ¬(deg ⟨0, hk⟩ = 0 ∧ deg ⟨1, Nat.lt_succ_self 1⟩ = 0)) :
    klrwAInfinityPreCategory.m (R := R) (n := ⟨2, hk⟩) obj deg = 0 := dif_neg h

-- Evaluations of the collapsed degree chain away from the inserted block.
private lemma stasheffDegOut_lt {m : ℕ} (deg : Fin m → ℤ) {r s : ℕ}
    (hr : r + s ≤ m) {i : Fin (m + 1 - s)} (h : i.val < r) :
    stasheffDegOut (β := ℤ) deg r s hr i = deg ⟨i.val, by omega⟩ := dif_pos h

private lemma stasheffDegOut_gt {m : ℕ} (deg : Fin m → ℤ) {r s : ℕ}
    (hr : r + s ≤ m) {i : Fin (m + 1 - s)} (h1 : ¬ i.val < r) (h2 : ¬ i.val = r) :
    stasheffDegOut (β := ℤ) deg r s hr i = deg ⟨i.val + s - 1, by omega⟩ :=
  (dif_neg h1).trans (dif_neg h2)

-- The packaged family vanishes on any chain with a nonzero degree entry.
private lemma genFamily_zero_of_deg_ne
    (g₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R)))
    (g₁ : ∀ {A B : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] FinCochain (g₀ A) (g₀ B) 0)
    (g₂ : ∀ {A B C : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] (B ⟶ C) →ₗ[R] FinCochain (g₀ A) (g₀ C) (-1))
    {j : ℕ} (hpos : 0 < j)
    {objs : Fin (j + 1) → KLRWCategory n R} {deg : Fin j → ℤ}
    (i : Fin j) (hi : deg i ≠ 0) :
    genFamily g₀ @g₁ @g₂ (k := ⟨j, hpos⟩) objs deg = 0 := by
  obtain _ | _ | _ | jj := j
  · exact absurd hpos (Nat.lt_irrefl 0)
  · exact dif_neg (fun h => hi (by
      rw [show i = (⟨0, Nat.one_pos⟩ : Fin 1) from Fin.ext (by omega)]
      exact h))
  · refine dif_neg (fun hb => ?_)
    fin_cases i
    · exact hi hb.1
    · exact hi hb.2
  · rfl

-- Off degree-zero chains: both sides vanish (the components are zero there
-- by definition, and the source operations vanish away from degree zero).
private lemma sfconv_offdeg
    (g₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R)))
    (g₁ : ∀ {A B : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] FinCochain (g₀ A) (g₀ B) 0)
    (g₂ : ∀ {A B C : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] (B ⟶ C) →ₗ[R] FinCochain (g₀ A) (g₀ C) (-1))
    {k : ℕ+}
    (objs : Fin ((k : ℕ) + 1) → KLRWCategory n R) (deg : Fin (k : ℕ) → ℤ)
    (x : ∀ i : Fin (k : ℕ), composableHomType (β := ℤ) (R := R)
      (klrwHom (R := R) (n := n)) objs deg i)
    (i0 : Fin (k : ℕ)) (hi0 : deg i0 ≠ 0) :
    indexedSFLeftSum (β := ℤ) (R := R) (n := k)
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      (genFamily g₀ @g₁ @g₂) objs deg x =
    indexedSFRightSum (β := ℤ) (R := R) (n := k)
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs deg x := by
  have hi0lt := i0.isLt
  have hL : indexedSFLeftSum (β := ℤ) (R := R) (n := k)
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      (genFamily g₀ @g₁ @g₂) objs deg x = 0 := by
    simp only [indexedSFLeftSum]
    apply Finset.sum_eq_zero
    rintro ⟨r, hrm⟩ -
    apply Finset.sum_eq_zero
    rintro ⟨s, hsm⟩ -
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hsm
    have hrr := Finset.mem_range.mp hrm
    have hv := validStasheffIndices_of_mem_ranges (n := (k : ℕ)) hrm hsm
    suffices hh : indexedSFLeftTerm (β := ℤ) (R := R) (n := k)
        (klrwAInfinityPreCategory (R := R) (n := n)).Hom
        (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
          (V := CMat_ (KLRWCategory n R))).Hom
        g₀
        (klrwAInfinityPreCategory (R := R) (n := n)).m
        (genFamily g₀ @g₁ @g₂) objs deg x r s hv.1 hv.2 = 0 by
      rw [hh, smul_zero]
    by_cases hs3 : 3 ≤ s
    · exact indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
        (fun hh o d => klrwM_zero_of_ge_three hs3)
    by_cases hs1 : s = 1
    · subst hs1
      exact indexedSFLeftTerm_inner_zero _ _ _ _ _ _ _ _
        (fun hh o d => klrwM_one_eq_zero hh o d)
    have hs2 : s = 2 := by omega
    subst hs2
    have hr2 : r + 2 ≤ (k : ℕ) := hv.2
    by_cases houter : 3 ≤ (k : ℕ) + 1 - 2
    · exact indexedSFLeftTerm_outer_zero _ _ _ _ _ _ _ _
        (fun hh o d => genFamily_zero_of_ge_three g₀ @g₁ @g₂ houter)
    by_cases hblock : r ≤ i0.val ∧ i0.val < r + 2
    · -- i0 lies in the inserted pair: μ₂ᴷᴸᴿᵂ dies on its degrees
      refine indexedSFLeftTerm_inner_zero_at _ _ _ _ _ _ _ _ (fun hh => ?_)
      refine klrwM_two_ne hh (fun hcon => hi0 ?_)
      rcases (by omega : i0.val = r ∨ i0.val = r + 1) with hv0 | hv0
      · have h1 : deg ⟨r + 0, by omega⟩ = 0 := hcon.1
        exact (congrArg deg (Fin.ext (by omega))).trans h1
      · have h1 : deg ⟨r + 1, by omega⟩ = 0 := hcon.2
        exact (congrArg deg (Fin.ext (by omega))).trans h1
    · -- i0 survives into the collapsed chain: the outer component dies
      push Not at hblock
      refine indexedSFLeftTerm_outer_zero_at _ _ _ _ _ _ _ _ (fun hh => ?_)
      by_cases hv0 : i0.val < r
      · refine genFamily_zero_of_deg_ne g₀ @g₁ @g₂ hh ⟨i0.val, by omega⟩
          (fun hcon => hi0 ?_)
        rw [stasheffDegOut_lt deg hv.2 (i := ⟨i0.val, by omega⟩) hv0] at hcon
        exact (congrArg deg (Fin.ext rfl)).trans hcon
      · have hv0' : r + 2 ≤ i0.val := hblock (by omega)
        refine genFamily_zero_of_deg_ne g₀ @g₁ @g₂ hh ⟨i0.val - 1, by omega⟩
          (fun hcon => hi0 ?_)
        rw [stasheffDegOut_gt deg hv.2 (i := ⟨i0.val - 1, by omega⟩)
          (show ¬ (i0 : ℕ) - 1 < r by omega)
          (show ¬ (i0 : ℕ) - 1 = r by omega)] at hcon
        exact (congrArg deg (Fin.ext
          (show (i0 : ℕ) = (i0 : ℕ) - 1 + 2 - 1 by omega))).trans hcon
  have hR : indexedSFRightSum (β := ℤ) (R := R) (n := k)
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) objs deg x = 0 := by
    simp only [indexedSFRightSum]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hbig : 3 ≤ c.blocksFun (c.index i0)
    · exact indexedSFRightTerm_inner_zero _ _ _ _ _ _ _ _ _ (c.index i0)
        (fun hh o d => genFamily_zero_of_ge_three g₀ @g₁ @g₂ hbig)
    · have hle := c.sizeUpTo_index_le i0
      have hlt2 : (i0 : ℕ) < c.sizeUpTo ((c.index i0 : ℕ) + 1) :=
        c.lt_sizeUpTo_index_succ i0
      have hsucc := c.sizeUpTo_succ' (c.index i0)
      refine indexedSFRightTerm_inner_zero_at _ _ _ _ _ _ _ _ _ (c.index i0)
        (fun hh => ?_)
      refine genFamily_zero_of_deg_ne g₀ @g₁ @g₂ hh
        ⟨i0.val - c.sizeUpTo (c.index i0).val, by omega⟩ (fun hcon => hi0 ?_)
      exact (congrArg deg (Fin.ext
        (show (i0 : ℕ) = c.sizeUpTo (c.index i0).val +
          ((i0 : ℕ) - c.sizeUpTo (c.index i0).val) by omega))).trans hcon
  exact hL.trans hR.symm

/-- The packaged family satisfies the full A∞-functor equation: on degree-zero
chains the arities `1`–`4` reduce to the four supplied axioms and arities
`≥ 5` vanish; off degree-zero chains everything vanishes. -/
theorem genFamily_satisfiesSF
    (g₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R)))
    (g₁ : ∀ {A B : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] FinCochain (g₀ A) (g₀ B) 0)
    (g₂ : ∀ {A B C : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] (B ⟶ C) →ₗ[R] FinCochain (g₀ A) (g₀ C) (-1))
    (hsf₁ : ∀ {A B : KLRWCategory n R} (f : A ⟶ B),
      (g₁ f).δ_fin = 0)
    (hsf₂ : ∀ {A B C : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C),
      g₁ (f ≫ g) =
        FinCochain.degCast (R := R) (zero_add 0)
          ((g₁ f).comp (g₁ g)) +
        FinCochain.degCast (R := R) (neg_add_cancel 1)
          (g₂ f g).δ_fin)
    (hsf₃ : ∀ {A B C D : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D),
      g₂ f (g ≫ h) + g₂ (f ≫ g) h =
        FinCochain.zeroComp (g₁ f) (g₂ g h) +
          FinCochain.compZero (g₂ f g) (g₁ h))
    (hsf₄ : ∀ {A B C D E : KLRWCategory n R}
      (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E),
      (g₂ f g).comp (g₂ h k) = 0) :
    indexedSatisfiesSF (β := ℤ) (R := R)
      (klrwAInfinityPreCategory (R := R) (n := n)).Hom
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).Hom
      g₀
      (klrwAInfinityPreCategory (R := R) (n := n)).m
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))).m
      (genFamily g₀ @g₁ @g₂) := by
  intro k objs deg x
  by_cases hd : ∀ i, deg i = 0
  · have hdeg : deg = fun _ => 0 := funext hd
    subst hdeg
    obtain ⟨k, hk⟩ := k
    match k with
    | 0 => exact absurd hk (Nat.lt_irrefl 0)
    | 1 => exact sfconv_one g₀ @g₁ @g₂ @hsf₁ objs x
    | 2 => exact sfconv_two g₀ @g₁ @g₂ @hsf₁ @hsf₂ @hsf₃ @hsf₄ objs x
    | 3 => exact sfconv_three g₀ @g₁ @g₂ @hsf₁ @hsf₂ @hsf₃ @hsf₄ objs x
    | 4 => exact sfconv_four g₀ @g₁ @g₂ @hsf₁ @hsf₂ @hsf₃ @hsf₄ objs x
    | j + 5 => exact sfconv_ge_five g₀ @g₁ @g₂ j objs x
  · push Not at hd
    obtain ⟨i0, hi0⟩ := hd
    exact sfconv_offdeg g₀ @g₁ @g₂ objs deg x i0 hi0

set_option maxHeartbeats 1600000 in
/-- Build a `BraidingFunctorData` from the blueprint's generators
`β₀, β₁, β₂` and the four truncated `[SF]` axioms. -/
def ofGenerators
    (g₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R)))
    (g₁ : ∀ {A B : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] FinCochain (g₀ A) (g₀ B) 0)
    (g₂ : ∀ {A B C : KLRWCategory n R},
      (A ⟶ B) →ₗ[R] (B ⟶ C) →ₗ[R] FinCochain (g₀ A) (g₀ C) (-1))
    (hsf₁ : ∀ {A B : KLRWCategory n R} (f : A ⟶ B),
      (g₁ f).δ_fin = 0)
    (hsf₂ : ∀ {A B C : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C),
      g₁ (f ≫ g) =
        FinCochain.degCast (R := R) (zero_add 0)
          ((g₁ f).comp (g₁ g)) +
        FinCochain.degCast (R := R) (neg_add_cancel 1)
          (g₂ f g).δ_fin)
    (hsf₃ : ∀ {A B C D : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D),
      g₂ f (g ≫ h) + g₂ (f ≫ g) h =
        FinCochain.zeroComp (g₁ f) (g₂ g h) +
          FinCochain.compZero (g₂ f g) (g₁ h))
    (hsf₄ : ∀ {A B C D E : KLRWCategory n R}
      (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E),
      (g₂ f g).comp (g₂ h k) = 0) :
    BraidingFunctorData R n where
  toFunctor :=
    { obj := g₀
      f := genFamily g₀ @g₁ @g₂
      sf := genFamily_satisfiesSF g₀ @g₁ @g₂ @hsf₁ @hsf₂ @hsf₃ @hsf₄ }
  trunc := fun k hk3 objs deg => by
    obtain ⟨k, hkpos⟩ := k
    match k with
    | 0 => exact absurd hkpos (Nat.lt_irrefl 0)
    | 1 => exact absurd (show (3 : ℕ) ≤ 1 from hk3) (by decide)
    | 2 => exact absurd (show (3 : ℕ) ≤ 2 from hk3) (by decide)
    | _ + 3 => rfl

structure BraidingFunctorAdd (R : Type u) [CommRing R] [CharP R 2]
[DecidableEq R] (n : ℕ) [DecidablePred (Limits.IsZero (C := CMat_ (KLRWCategory n R)))] where
  add₀ : CMat_ (KLRWCategory n R) → BoundedCochainComplex (CMat_ (KLRWCategory n R))
  add₁ : {A B : CMat_ (KLRWCategory n R)} → (A ⟶ B) → (add₀ A ⟶ add₀ B)
  add₂ : {A B C : CMat_ (KLRWCategory n R)} → (A ⟶ B) → (B ⟶ C) →
    FinCochain (add₀ A) (add₀ C) (-1)

structure BraidingFunctorFull (R : Type u) [CommRing R] [CharP R 2]
[DecidableEq R] (n : ℕ) [DecidablePred (Limits.IsZero (C := CMat_ (KLRWCategory n R)))] where
  full₀ : BoundedCochainComplex (CMat_ (KLRWCategory n R)) → BoundedCochainComplex (CMat_ (KLRWCategory n R))
  full₁ : {A B : BoundedCochainComplex (CMat_ (KLRWCategory n R))} → (A ⟶ B) → (full₀ A ⟶ full₀ B)
  full₂ : {A B C : BoundedCochainComplex (CMat_ (KLRWCategory n R))} → (A ⟶ B) → (B ⟶ C) →
    FinCochain (full₀ A) (full₀ C) (-1)

/-! ### Zero-value lemmas

The zero cochain composes and differentiates to zero; used to discharge the
`[SF]` axioms for a datum whose morphism-level components vanish. -/

lemma finCochain_getV_zero {X Y : BoundedCochainComplex (CMat_ (KLRWCategory n R))}
    {d : ℤ} (p : ℤ) : (0 : FinCochain X Y d).getV p = 0 := by
  by_cases hp : p ∈ BoundedCochainComplex.activePairs X Y d
  · rw [BoundedCochainComplex.FinCochain.getV_of_mem _ hp]; rfl
  · exact BoundedCochainComplex.FinCochain.getV_of_not_mem _ hp

lemma finCochain_comp_zero {X Y Z : BoundedCochainComplex (CMat_ (KLRWCategory n R))}
    {d₁ d₂ : ℤ} :
    FinCochain.comp (0 : FinCochain X Y d₁) (0 : FinCochain Y Z d₂) = 0 := by
  funext p
  obtain ⟨p, hp⟩ := p
  show (0 : FinCochain X Y d₁).getV p ≫ _ = _
  rw [finCochain_getV_zero, Limits.zero_comp]
  rfl

lemma finCochain_zeroComp_zero {X Y Z : BoundedCochainComplex (CMat_ (KLRWCategory n R))}
    {m : ℤ} :
    FinCochain.zeroComp (0 : FinCochain X Y 0) (0 : FinCochain Y Z m) = 0 := by
  funext p
  obtain ⟨p, hp⟩ := p
  show (0 : FinCochain X Y 0).getV p ≫ _ = _
  rw [finCochain_getV_zero, Limits.zero_comp]
  rfl

lemma finCochain_compZero_zero {X Y Z : BoundedCochainComplex (CMat_ (KLRWCategory n R))}
    {m : ℤ} :
    FinCochain.compZero (0 : FinCochain X Y m) (0 : FinCochain Y Z 0) = 0 := by
  funext p
  obtain ⟨p, hp⟩ := p
  show (0 : FinCochain X Y m).getV p ≫ _ = _
  rw [finCochain_getV_zero, Limits.zero_comp]
  rfl

lemma finCochain_δ_fin_zero {X Y : BoundedCochainComplex (CMat_ (KLRWCategory n R))}
    {d : ℤ} : (0 : FinCochain X Y d).δ_fin = 0 := by
  have h := FinCochain.δ_fin_add (0 : FinCochain X Y d) 0
  rw [add_zero] at h
  exact left_eq_add.mp h

/-! ### The braiding functor data

`braidingData` builds the datum from the object action alone: the
morphism-level components `β₁, β₂` are set to zero, which satisfies the four
`[SF]` axioms trivially (everything in sight is zero). NOTE: this is the
degenerate zero-on-morphisms functor — identities are not sent to identity
chain maps — so the morphism data is expected to be upgraded later via
`ofGenerators`, which takes the full `β₁` (linear) and `β₂` (bilinear)
together with the four axiom proofs. -/

/-- The braiding functor datum determined by an action on objects, with zero
morphism-level components. -/
def braidingData
    (β₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R))) :
    BraidingFunctorData R n :=
  BraidingFunctorData.ofGenerators β₀ (fun {_ _} => 0) (fun {_ _ _} => 0)
    (fun {A B} _f => finCochain_δ_fin_zero)
    (fun {A B C} f g => by
      show (0 : FinCochain (β₀ A) (β₀ C) 0) =
        FinCochain.degCast (R := R) (show (0 : ℤ) + 0 = 0 from rfl)
          (FinCochain.comp (0 : FinCochain (β₀ A) (β₀ B) 0)
            (0 : FinCochain (β₀ B) (β₀ C) 0)) +
        FinCochain.degCast (R := R) (show (-1 : ℤ) + 1 = 0 from rfl)
          ((0 : FinCochain (β₀ A) (β₀ C) (-1)).δ_fin)
      rw [finCochain_comp_zero, finCochain_δ_fin_zero, map_zero, map_zero, add_zero])
    (fun {A B C D} f g h => by
      show (0 : FinCochain (β₀ A) (β₀ D) (-1)) + 0 =
        FinCochain.zeroComp (0 : FinCochain (β₀ A) (β₀ B) 0)
          (0 : FinCochain (β₀ B) (β₀ D) (-1)) +
        FinCochain.compZero (0 : FinCochain (β₀ A) (β₀ C) (-1))
          (0 : FinCochain (β₀ C) (β₀ D) 0)
      rw [finCochain_zeroComp_zero, finCochain_compZero_zero])
    (fun {A B C D E} f g h k => finCochain_comp_zero)

/-! ### The braiding action on objects

The braiding of the `i`-th and `(i+1)`-th marked points sends the T-brane at
the braided position (`T_k`, between the two red points) to the two-term
complex `T_{k-1} ⊕ T_{k+1} ⟶ T_k` in degrees `0, 1`, with dotless
differential; every other positioning is unchanged, viewed as a complex
concentrated in degree `0`. -/

/-- A positioning as a one-term cochain complex in degree `0`. -/
def braneCC (A : KLRWCategory n R) : CochainComplex (CMat_ (KLRWCategory n R)) ℤ where
  X i := if i = 0 then [A]ₘ else 𝟎
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := Limits.zero_comp

/-- The two-term complex `[BraneNeg1, Brane1]ₘ ⟶ [A]ₘ` in degrees `0, 1`, with
dotless differential (every matrix entry the unit strand `dots 0`). -/
def braidedBraneCC (BraneNeg1 Brane1 A : KLRWCategory n R) :
    CochainComplex (CMat_ (KLRWCategory n R)) ℤ where
  X i := if i = 0 then [BraneNeg1, Brane1]ₘ else if i = 1 then [A]ₘ else 𝟎
  d i j :=
    if hij : i = 0 ∧ j = 1 then by
      rcases hij with ⟨rfl, rfl⟩
      exact fun _ _ => StrandSpace.dots R 0
    else 0
  shape i j hij := by
    by_cases h01 : i = 0 ∧ j = 1
    · exfalso
      rcases h01 with ⟨rfl, rfl⟩
      exact hij (by simp [ComplexShape.up, ComplexShape.up'])
    · simp [h01]
  -- proof that d^2 = 0
  d_comp_d' i j l hij hjl := by
    by_cases h01 : i = 0 ∧ j = 1
    · rcases h01 with ⟨rfl, rfl⟩
      rw [dif_pos ⟨rfl, rfl⟩,
        dif_neg (show ¬((1 : ℤ) = 0 ∧ l = 1) by norm_num), Limits.comp_zero]
    · rw [dif_neg h01]
      exact Limits.zero_comp

/-- Both are bounded, so it is computable. -/
lemma braneCC_bounded (A : KLRWCategory n R) :
    ∀ i : ℤ, ¬ Limits.IsZero ((braneCC (R := R) A).X i) → i ∈ ({0} : Finset ℤ) := by
  intro i hi
  rw [Finset.mem_singleton]
  by_contra h0
  exact hi (by
    show Limits.IsZero (if i = 0 then _ else _)
    rw [if_neg h0]
    exact isZero_explicitZero)

lemma braidedBraneCC_bounded (BraneNeg1 Brane1 A : KLRWCategory n R) :
    ∀ i : ℤ, ¬ Limits.IsZero ((braidedBraneCC (R := R) BraneNeg1 Brane1 A).X i) →
      i ∈ ({0, 1} : Finset ℤ) := by
  intro i hi
  rw [Finset.mem_insert, Finset.mem_singleton]
  by_contra hmem
  push Not at hmem
  exact hi (by
    show Limits.IsZero (if i = 0 then _ else if i = 1 then _ else _)
    rw [if_neg hmem.1, if_neg hmem.2]
    exact isZero_explicitZero)

/-- A positioning as a bounded one-term complex in degree `0`. -/
def brane (A : KLRWCategory n R) :
    BoundedCochainComplex (CMat_ (KLRWCategory n R)) :=
  BoundedCochainComplex.mkOfBounded (braneCC A)
    (supersetOfSupport := {0}) (braneCC_bounded A)

/-- The braided T-brane as a bounded complex: the two-term complex
`[BraneNeg1, Brane1]ₘ ⟶ [A]ₘ` in degrees `0, 1`. -/
def braidedBrane (BraneNeg1 Brane1 A : KLRWCategory n R) :
    BoundedCochainComplex (CMat_ (KLRWCategory n R)) :=
  BoundedCochainComplex.mkOfBounded (braidedBraneCC BraneNeg1 Brane1 A)
    (supersetOfSupport := {0, 1}) (braidedBraneCC_bounded _ _ _)

/-- The braiding action on objects for the transposition of the `i`-th and
`(i+1)`-th marked points (`i : Fin (n - 1)`, so only genuine transpositions
are expressible): the braided position is `k = i + 1`, whose T-brane becomes
the braided two-term complex `T_{k-1} ⊕ T_{k+1} ⟶ T_k`; every other
positioning is unchanged. -/
def braidingObj (i : Fin (n - 1)) (A : KLRWCategory n R) :
    BoundedCochainComplex (CMat_ (KLRWCategory n R)) :=
  if A.positioning = (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (n + 1)) then
    braidedBrane ⟨⟨i.val, by have := i.isLt; omega⟩⟩
      ⟨⟨i.val + 2, by have := i.isLt; omega⟩⟩ A
  else
    brane A

/-- `β.gen` (blueprint notation): the braiding functor of the transposition of
the `i`-th and `(i+1)`-th marked points, as an A∞-functor from `KLRW` to
`K^•(Add KLRW)`, acting on objects by `braidingObj` (morphism-level components
currently zero, via `braidingData`). -/
def beta_gen (i : Fin (n - 1)) :
    AInfinityFunctor (klrwAInfinityPreCategory (R := R) (n := n))
      (BoundedCochainComplex.bccAInfinityPreCategory (R := R)
        (V := CMat_ (KLRWCategory n R))) :=
  (braidingData (braidingObj i)).toFunctor
