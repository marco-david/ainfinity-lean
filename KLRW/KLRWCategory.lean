module
public import Mathlib
public import KLRW.KLRWAlgebra
@[expose] public section


namespace KLRW
open CategoryTheory FreeAlgebra


variable {V : Type*} [DecidableEq V] [Fintype V]
variable {parameters : KLRWStructure V}
variable {R : Type*} [CommRing R]



/- -----------------------------------------------------------------------------
   The following are all lemmas connecting the free algebra to quotient algebra.
   ----------------------------------------------------------------------------- -/

section

variable {f g : KLRWFreeAlg R parameters}

/- If f and g are equal by a rule in KLRWImplicit, then f and g are related in KLRWRel. -/

lemma implicit_rel_eq_rel (h : KLRWImplicitConRel f g) : KLRWRel R parameters f g :=
  RingConGen.Rel.of f g (Or.inl h)


/- If f and g are equal by a rule in KLRWExplicit, then f and g are related in KLRWRel. -/

lemma explicit_rel_eq_rel (h : KLRWExplicitConRel f g) : KLRWRel R parameters f g :=
  RingConGen.Rel.of f g (Or.inr h)


/- If f and g are related in KLRWRel, then they are in the same equivalence class. -/

lemma rel_eq_same_con_class {X Y : KLRWFreeAlg R parameters} (h : KLRWRel R parameters X Y) :
    (KLRWRel R parameters).mk' X = (KLRWRel R parameters).mk' Y := by
  exact (KLRWRel R parameters).eq.mpr h


/- Any implicit relation lifts to an equality in the quotient algebra KLRWAlg. -/

lemma implicit_rel_to_quot_eq (h : KLRWImplicitConRel f g) :
    (KLRWRel R parameters).mk' f = (KLRWRel R parameters).mk' g := by
  exact rel_eq_same_con_class (implicit_rel_eq_rel h)


/- Any explicit relation lifts to an equality in the quotient algebra KLRWAlg. -/

lemma explicit_rel_to_quot_eq (h : KLRWExplicitConRel f g) :
    (KLRWRel R parameters).mk' f = (KLRWRel R parameters).mk' g := by
  exact rel_eq_same_con_class (explicit_rel_eq_rel h)

end






/- --------------------------------------------------------------------------
   The following lemmas are all related to properties of idem_morph.
   -------------------------------------------------------------------------- -/

section

variable {X Y Z : KLRWObject parameters}

/- The idempotent morphism in KLRWAlg is idempotent (uses id_left in KLRW Implicit relations). -/

lemma idem_is_idem : idem_morph R X * idem_morph R X = idem_morph R X := by
  apply rel_eq_same_con_class
  apply implicit_rel_eq_rel
  exact KLRWImplicitConRel.idem_left X (.idem X) rfl


/- idem_morph R Y acts as an left identity on cross strand generators lifted to the quotient with codomain Y. -/

lemma idem_mul_cross (i : Fin (totalStrands parameters - 1)) (h_swap : Y = afterCross X i) :
    idem_morph R Y * (KLRWRel R parameters).mk' (ι _ (.cross X i)) =
    (KLRWRel R parameters).mk' (ι _ (.cross X i)) := by
  dsimp [idem_morph]
  apply implicit_rel_to_quot_eq
  subst h_swap
  exact KLRWImplicitConRel.idem_left (afterCross X i) (.cross X i) rfl


/- idem_morph R X acts as an right identity on cross strand generators lifted to the quotient with domain X. -/

lemma cross_mul_idem (i : Fin (totalStrands parameters - 1)) :
    (KLRWRel R parameters).mk' (ι _ (.cross X i)) * idem_morph R X =
    (KLRWRel R parameters).mk' (ι _ (.cross X i)) := by
  dsimp [idem_morph]
  apply implicit_rel_to_quot_eq
  exact KLRWImplicitConRel.idem_right X (.cross X i) rfl


/- idem_morph R X acts as an left identity on dot strand generators lifted to the quotient with domain X. -/

lemma idem_mul_dot (i : Fin (totalStrands parameters)) :
    idem_morph R X * (KLRWRel R parameters).mk' (ι _ (.dot X i)) =
      (KLRWRel R parameters).mk' (ι _ (.dot X i)) := by
  dsimp [idem_morph]
  apply implicit_rel_to_quot_eq
  exact KLRWImplicitConRel.idem_left X (.dot X i) rfl


/- idem_morph R X acts as an right identity on cross strand generators with domain X. -/

lemma dot_mul_idem (i : Fin (totalStrands parameters)) :
    (KLRWRel R parameters).mk' (ι _ (.dot X i)) * idem_morph R X =
    (KLRWRel R parameters).mk' (ι _ (.dot X i)) := by
  dsimp [idem_morph]
  apply implicit_rel_to_quot_eq
  exact KLRWImplicitConRel.idem_right X (.dot X i) rfl




/- --------------------------------------------------------------------------
   The following lemmas are all related to describing membership of KLRWHom.
   -------------------------------------------------------------------------- -/

/- Shows the connection between f ∈ KLRWHom X Y and the idem_moprh . -/

lemma mem_KLRWHom_iff (f : KLRWAlg R parameters) :
    f ∈ KLRWHom R X Y ↔ idem_morph R Y * f * idem_morph R X = f := by
  constructor
  · intro h
    rcases h with ⟨a, rfl⟩
    dsimp at *
    simp [mul_assoc, idem_is_idem]
    simp [← mul_assoc, idem_is_idem]
  · intro h
    use f
    dsimp
    simp only [← mul_assoc]
    exact h


/- Shows idem * f = f, so idem acts as the left identity for KLRWHom R X Y. -/

lemma id_mul_left (f : KLRWAlg R parameters) (hf : f ∈ KLRWHom R X Y) : idem_morph R Y * f = f := by
  obtain ⟨a, ha⟩ := hf
  dsimp [LinearMap.mulLeft, LinearMap.mulRight, LinearMap.comp] at ha
  rw [← ha, ← mul_assoc, idem_is_idem]


/- Shows f * idem = f, so idem acts as the right identity for KLRWHom R X Y. -/

lemma id_mul_right (f : KLRWAlg R parameters) (hf : f ∈ KLRWHom R X Y) : f * idem_morph R X = f := by
  obtain ⟨a, ha⟩ := hf
  dsimp [LinearMap.mulLeft, LinearMap.mulRight, LinearMap.comp] at ha
  rw [← ha, ← mul_assoc, mul_assoc, idem_is_idem]


/- Shows the domain and codomain of the multiplication (composition) of two functions is as expected. -/

lemma KLRWHom_comp_mem {f g : KLRWAlg R parameters} (hf : f ∈ KLRWHom R X Y) (hg : g ∈ KLRWHom R Y Z) :
    g * f ∈ KLRWHom R X Z := by
  rw [mem_KLRWHom_iff, mul_assoc, mul_assoc, id_mul_right f hf]
  rw [← mul_assoc, id_mul_left g hg]


/- The cross strand generator lifted to the quotient is a member of KLRW R X (afterCross X i). -/

lemma cross_mem_KLRWHom (i : Fin (totalStrands parameters - 1)) :
    (KLRWRel R parameters).mk' (ι _ (.cross X i)) ∈ KLRWHom R X (afterCross X i) := by
  rw [mem_KLRWHom_iff]
  rw [idem_mul_cross i, cross_mul_idem i]
  rfl


/- The dot strand generator lifted to the quotient is a member of KLRW R X (afterCross X i). -/

lemma dot_mem_KLRWHom (i : Fin (totalStrands parameters)) :
    (KLRWRel R parameters).mk' (ι _ (.dot X i)) ∈ KLRWHom R X X := by
  rw [mem_KLRWHom_iff]
  rw [idem_mul_dot i, dot_mul_idem i]

end


/- --------------------------------------------------------------------------
   The following section is to define KLRWObject.WithRing and its properties.
   -------------------------------------------------------------------------- -/

/- This adds R to KLRWObject so that user can specify what ring they are working in. -/

structure KLRWObject.WithRing (R : Type*) [CommRing R] (parameters : KLRWStructure V) where
  obj : KLRWObject parameters


/- KLRWObjectR is a category. -/

noncomputable instance : Category (KLRWObject.WithRing R parameters) where

  Hom X Y := ↥(KLRWHom R X.obj Y.obj)

  id X := ⟨idem_morph R X.obj, by
    rw [mem_KLRWHom_iff]
    simp [idem_is_idem]⟩

  comp f g := ⟨g.val * f.val, KLRWHom_comp_mem f.property g.property⟩ -- check order of f * g

  id_comp f := by ext; exact id_mul_right f.val f.property

  comp_id f := by ext; exact id_mul_left f.val f.property

  assoc f g h := by ext; simp [mul_assoc]


/- If two KLRWObjectRs have the same value, then they are equal. -/

@[ext]
lemma KLRWHom.ext {X Y : KLRWObject.WithRing R parameters} {f g : X ⟶ Y} (h : f.val = g.val) : f = g :=
  Subtype.ext h


/- KLRWObjectR is a preadditive category. -/

noncomputable instance : Preadditive (KLRWObject.WithRing R parameters) where

  homGroup X Y := inferInstanceAs (AddCommGroup (KLRWHom R X.obj Y.obj))

  add_comp X Y Z f g h := by
    ext
    change h.val * (f.val + g.val) = h.val * f.val + h.val * g.val
    exact mul_add h.val f.val g.val
  comp_add X Y Z f g h := by
    ext
    change (g.val + h.val) * f.val = g.val * f.val + h.val * f.val
    exact add_mul g.val h.val f.val


/- KLRWObjectR is a linear category. -/

noncomputable instance : CategoryTheory.Linear R (KLRWObject.WithRing R parameters) where

  homModule X Y := inferInstanceAs (Module R (KLRWHom R X.obj Y.obj))

  smul_comp X Y Z r f g := by
    ext
    change g.val * (r • f.val) = r • (g.val * f.val)
    exact mul_smul_comm r g.val f.val

  comp_smul X Y Z f r g := by
    ext
    change (r • g.val) * f.val = r • (g.val * f.val)
    exact smul_mul_assoc r g.val f.val




/- -------------------------------------------------------------------------------------------------
   The following lemmas are all related to strandGenSeq properties in the quotient algebra.
   ------------------------------------------------------------------------------------------------- -/

section

variable (M N : KLRWObject parameters)
variable (ops : List (StrandGenOp parameters))


/-- A strand generator sequence is a valid morphism from its domain M to its calculated ending
    cdomain (strandGenSeqEnd M ops). -/

lemma strandGenSeq_mem_KLRWHom :
    (KLRWRel R parameters).mk' (strandGenSeq M ops) ∈ KLRWHom R M (strandGenSeqEnd M ops) := by

  induction ops generalizing M with
  | nil =>
      change (KLRWRel R parameters).mk' (ι _ (.idem M)) ∈ KLRWHom R M M
      rw [mem_KLRWHom_iff]
      change idem_morph R M * idem_morph R M * idem_morph R M = idem_morph R M
      rw [idem_is_idem, idem_is_idem]

  | cons op ops ih =>
      let M' := strandGenSeqEnd M ops
      let firstOp := StrandGenOp.act M' op
      have htail :
          (KLRWRel R parameters).mk' (strandGenSeq M ops) ∈ KLRWHom R M M' := by
        exact ih M
      have hop :
          (KLRWRel R parameters).mk' (ι _ firstOp.1) ∈ KLRWHom R M' firstOp.2 := by
        cases op with
        | cross i =>
            change (KLRWRel R parameters).mk' (ι _ (.cross M' i)) ∈ KLRWHom R M' (afterCross M' i)
            rw [mem_KLRWHom_iff]
            rw [idem_mul_cross i]
            · rw [cross_mul_idem i]
            · rfl
        | dot i =>
            change (KLRWRel R parameters).mk' (FreeAlgebra.ι _ (.dot M' i)) ∈ KLRWHom R M' M'
            rw [mem_KLRWHom_iff]
            rw [idem_mul_dot i]
            rw [dot_mul_idem i]
        | idem =>
            change (KLRWRel R parameters).mk' (ι _ (.idem M')) ∈ KLRWHom R M' M'
            rw [mem_KLRWHom_iff]
            change idem_morph R M' * idem_morph R M' * idem_morph R M' = idem_morph R M'
            rw [idem_is_idem, idem_is_idem]

      change
        (KLRWRel R parameters).mk' (ι _ firstOp.1 * strandGenSeq M ops) ∈ KLRWHom R M firstOp.2
      simpa only [map_mul] using KLRWHom_comp_mem htail hop


/-- If you know the codomain of the morphism generated by ops is N, then the morphism generated by
    ops is in KLRWHom R M N. -/

lemma strandGenSeq_mem_KLRWHom_of_eq (ops : List (StrandGenOp parameters))
    (h : strandGenSeqEnd M ops = N) :
    (KLRWRel R parameters).mk' (strandGenSeq M ops) ∈ KLRWHom R M N := by
  rw [← h]
  exact strandGenSeq_mem_KLRWHom M ops


/- Idempotent is left identity for strand generator sequence. -/

lemma idem_mul_strandGenSeq : idem_morph R (strandGenSeqEnd M ops) *
    (KLRWRel R parameters).mk' (strandGenSeq (R := R) M ops) =
    (KLRWRel R parameters).mk' (strandGenSeq (R := R) M ops) :=
  id_mul_left _ (strandGenSeq_mem_KLRWHom M ops)


/- Idempotent is right identity for strand generator sequence. -/

lemma strandGenSeq_mul_idem :
    (KLRWRel R parameters).mk' (strandGenSeq (R := R) M ops) * idem_morph R M =
    (KLRWRel R parameters).mk' (strandGenSeq (R := R) M ops) :=
  id_mul_right _ (strandGenSeq_mem_KLRWHom M ops)


/- Adding a strand operation list ops1 to a strand generator sequence's list ops2 is the same as
   multiplying strandGenSeq ops2 on the right by strandGenSeq ops1. -/

lemma strandGenSeq_append (ops₁ ops₂ : List (StrandGenOp parameters)) :
    (KLRWRel R parameters).mk' (strandGenSeq M (ops₁ ++ ops₂)) =
    (KLRWRel R parameters).mk' (strandGenSeq (strandGenSeqEnd M ops₂) ops₁ * strandGenSeq (R := R) M ops₂) := by
  induction ops₁ with
  | nil =>
      simp only [List.nil_append, strandGenSeq]
      symm
      exact idem_mul_strandGenSeq (R := R) M ops₂

  | cons op ops₁ ih =>
      rw [List.cons_append, strandGenSeq_cons]
      rw [map_mul]
      rw [ih]
      rw [strandGenSeq_cons]
      simp [strandGenSeqEnd_append, mul_assoc]


end

end KLRW
