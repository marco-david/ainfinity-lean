module

public import AInfinity.AInfinityCategory

open AInfinityTheory CategoryTheory

universe u v w w'

/-- A (strict) `R`-linear category is an `A∞`-category, for any grading `β`: all morphisms sit in
degree `0`, `m₂` is composition and `m₁ = m₃ = m₄ = ⋯ = 0`. The only nontrivial Stasheff
identity is the one in arity `3`, which says that composition is associative. -/
example (β : Type v) [AddCommGroup β] [GradingType β] (R : Type u) [CommRing R] (C : Type w)
    [Category.{w'} C] [Preadditive C] [Linear R C] : AInfinityCategory β R C where
  Hom X Y i := ↥(⨅ _ : i ≠ 0, (⊥ : Submodule R (X ⟶ Y)))
  m {n} _ obj := if h : n = 2 then by
      subst h
      refine ⟨fun deg i hi => MultilinearMap.codRestrict
        { toFun x := (x 0).1 ≫ (x 1).1
          map_update_add' x j a b := ?_
          map_update_smul' x j c a := ?_ } _ fun x => ?_⟩
      · match j with
        | 0 => simpa using Preadditive.add_comp _ _ _ a.1 b.1 (x 1).1
        | 1 => simpa using Preadditive.comp_add _ _ _ (x 0).1 a.1 b.1
      · match j with
        | 0 => simpa using Linear.smul_comp _ _ _ c a.1 (x 1).1
        | 1 => simpa using Linear.comp_smul _ _ _ (x 0).1 c a.1
      · refine (Submodule.mem_iInf _).2 fun hi' => (Submodule.mem_bot R).2 ?_
        show (x 0).1 ≫ (x 1).1 = 0
        by_cases h0 : deg 0 = 0
        · rw [(Submodule.mem_bot R).1 ((Submodule.mem_iInf _).1 (x 1).2
            (by simp_all [Fin.sum_univ_two]))]
          exact Limits.comp_zero
        · rw [(Submodule.mem_bot R).1 ((Submodule.mem_iInf _).1 (x 0).2 h0), Limits.zero_comp]
    else 0
  stasheff := indexedSatisfiesStasheff_of_arity_two _ (fun _ _ hk _ => dif_neg hk)
    fun obj deg x d hd => by
      apply Subtype.ext
      change stasheffSign deg 0 2 1 rfl • (((x 0).1 ≫ (x 1).1) ≫ (x 2).1) +
        (x 0).1 ≫ (x 1).1 ≫ (x 2).1 = 0
      rw [Category.assoc]
      rcases eq_or_ne (deg 2) 0 with h | h
      · have hs : stasheffSign deg 0 2 1 rfl = -1 := by
          rw [stasheffSign, Fin.prod_univ_one]
          change Additive.toMul (sign (deg 2 - shift 1)) = -1
          rw [h, zero_sub, ← map_neg, sign_shift, Int.negOnePow_neg, Int.negOnePow_one]
          rfl
        rw [hs, Units.neg_smul, one_smul, neg_add_cancel]
      · have h2 : (x 0).1 ≫ (x 1).1 ≫ (x 2).1 = 0 := by
          rw [(Submodule.mem_bot R).1 ((Submodule.mem_iInf _).1 (x 2).2 h)]
          exact (congrArg ((x 0).1 ≫ ·) Limits.comp_zero).trans Limits.comp_zero
        rw [h2, smul_zero, add_zero]
