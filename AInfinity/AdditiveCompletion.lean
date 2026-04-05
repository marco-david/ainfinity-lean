import Mathlib

open CategoryTheory

structure CMat_ (C : Type*) where
  ofList ::
    toList : List C

namespace CMat_

section definition
variable {C : Type*} [Category C] [Preadditive C] (M N K : CMat_ C)

/--
Mirrors the API of `CategoryTheory.Mat_.ι`.
This is irreducible because it is effectively irreducible in `Mat_`, and we should mirror the API.
-/
@[irreducible]
def ι : Type := Fin M.toList.length

/- Auxillary definitions that are used to avoid defeq abuse. -/
unseal ι in
def ι.toFin (i : M.ι) : Fin M.toList.length := i
unseal ι in
def ι.ofFin (i : Fin M.toList.length) : M.ι := i

unseal ι in
instance fintype : Fintype M.ι := inferInstanceAs <| Fintype (Fin M.toList.length)
unseal ι in
instance : DecidableEq M.ι := inferInstanceAs <| DecidableEq (Fin M.toList.length)

omit [Category C] [Preadditive C] in
unseal ι in
theorem ι.toFin_ofFin (i : Fin M.toList.length) : (ι.ofFin M i).toFin = i := rfl

omit [Category C] [Preadditive C] in
unseal ι in
theorem ι.ofFin_toFin (i : M.ι) : ι.ofFin M i.toFin = i := rfl

/-- Mirrors the API of `CategoryTheory.Mat_.X` -/
@[irreducible]
def X : M.ι → C := fun i ↦ M.toList[i.toFin]

/-- Mirrors the API of `CategoryTheory.Mat_.Hom` -/
def Hom : Type* := DMatrix M.ι N.ι fun i j => M.X i ⟶ N.X j

/-- Mirrors the API of `CategoryTheory.Mat_.Hom.id` -/
def Hom.id : Hom M M :=
  fun i j => if h : i = j then eqToHom (congr_arg M.X h) else 0

/-- Mirrors the API of `CategoryTheory.Mat_.Hom.comp` -/
def Hom.comp {M N K : CMat_ C} (f : Hom M N) (g : Hom N K) : Hom M K :=
  fun i k => ∑ j : N.ι, f i j ≫ g j k

instance : Category (CMat_ C) where
  Hom := CMat_.Hom
  id := CMat_.Hom.id
  comp f g := f.comp g
  -- These proofs are based on those in `CategoryTheory.Mat_`.
  -- We add more to the simp set because we don't have a `local simp` attribute immediately above.
  id_comp f := by simp +unfoldPartialApp [dite_comp, Hom.id, Hom.comp]
  comp_id f := by simp +unfoldPartialApp [comp_dite, Hom.id, Hom.comp]
  assoc f g h := by
    apply DMatrix.ext
    intros
    simp_rw [Hom.comp, CategoryTheory.Preadditive.sum_comp, CategoryTheory.Preadditive.comp_sum,
      Category.assoc]
    rw [Finset.sum_comm]

-- These theorems and instances are almost directly copied from `CategoryTheory.Mat_`.
@[ext] theorem hom_ext {M N : CMat_ C} (f g : M ⟶ N) (H : ∀ i j, f i j = g i j) : f = g :=
  DMatrix.ext_iff.mp H
theorem id_def (M : CMat_ C) :
    (𝟙 M : Hom M M) = fun i j => if h : i = j then eqToHom (congr_arg M.X h) else 0 := rfl
theorem id_apply (M : CMat_ C) (i j : M.ι) :
    (𝟙 M : Hom M M) i j = if h : i = j then eqToHom (congr_arg M.X h) else 0 := rfl
@[simp] theorem id_apply_self (M : CMat_ C) (i : M.ι) : (𝟙 M : Hom M M) i i = 𝟙 _ := by
  simp [id_apply]
@[simp] theorem id_apply_of_ne (M : CMat_ C) (i j : M.ι) (h : i ≠ j) : (𝟙 M : Hom M M) i j = 0 := by
  simp [id_apply, h]
theorem comp_def {M N K : CMat_ C} (f : M ⟶ N) (g : N ⟶ K) :
    f ≫ g = fun i k => ∑ j : N.ι, f i j ≫ g j k := rfl
@[simp] theorem comp_apply {M N K : CMat_ C} (f : M ⟶ N) (g : N ⟶ K) (i k) :
    (f ≫ g) i k = ∑ j : N.ι, f i j ≫ g j k := rfl
instance : Inhabited (M ⟶ N) := ⟨fun i j => (0 : M.X i ⟶ N.X j)⟩
instance : AddCommGroup (M ⟶ N) := inferInstanceAs <| AddCommGroup (DMatrix M.ι N.ι _)
@[simp] theorem add_apply {M N : CMat_ C} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j := rfl
instance : Preadditive (CMat_ C) where
  add_comp M N K f f' g := by ext; simp [Finset.sum_add_distrib]
  comp_add M N K f g g' := by ext; simp [Finset.sum_add_distrib]

-- Idea: Maybe we can translate the `HasFiniteBiproducts` instance from `CategoryTheory.Mat_` using
-- an equivalence. I don't know if this would make it computable though, which we might need.

-- We split the equivalence into two parts rather than just having a singular
-- `CategoryTheory.Equivalence` structure because one direction is computable.
def toMat_ (C : Type*) [Category C] [Preadditive C] : CMat_ C ⥤ Mat_ C where
  obj M := {
    ι := M.ι
    fintype := M.fintype
    X := M.X
  }
  map f := f
  map_id M := by
    rw [id_def, Mat_.id_def]
    convert rfl

instance : (toMat_ C).Faithful where
  map_injective {M N} f g := by aesop

instance : (toMat_ C).Full where
  map_surjective {M N} f' := by
  -- Aristotle proof
    constructor;
    convert rfl

-- Aristotle generated definition
/-- Given a Mat_ object M', construct the corresponding CMat_ object. -/
noncomputable def ofMat_ (M' : Mat_ C) : CMat_ C :=
  CMat_.ofList (List.ofFn (M'.X ∘ (Fintype.equivFin M'.ι).symm))

-- Aristotle generated definition
unseal ι in
private noncomputable def ofMat_equiv_fin (M' : Mat_ C) :
    (ofMat_ M').ι ≃ Fin (Fintype.card M'.ι) :=
  finCongr (by simp [ofMat_, List.length_ofFn])

-- Aristotle generated definition
private noncomputable def ofMat_equiv (M' : Mat_ C) :
    (ofMat_ M').ι ≃ M'.ι :=
  (ofMat_equiv_fin M').trans (Fintype.equivFin M'.ι).symm

-- Aristotle generated theorem
omit [Category C] [Preadditive C] in
private theorem ofMat_X_equiv (M' : Mat_ C) (i : (ofMat_ M').ι) :
    (ofMat_ M').X i = M'.X (ofMat_equiv M' i) := by
  unfold CMat_.X; simp +decide only [Fin.getElem_fin];
  unfold ofMat_ at *; simp_all +decide only [List.getElem_ofFn, Function.comp_apply] ;
  congr! 1

-- Aristotle generated theorem
omit [Category C] [Preadditive C] in
private theorem ofMat_X_equiv' (M' : Mat_ C) (i : (ofMat_ M').ι) (j : M'.ι)
    (h : ofMat_equiv M' i = j) :
    (ofMat_ M').X i = M'.X j := by
  subst h; exact ofMat_X_equiv M' i

-- Artitotle generated definition
open Classical in
private noncomputable def toMat_ofMat_iso (M' : Mat_ C) :
    (toMat_ C).obj (ofMat_ M') ≅ M' where
  hom := fun i j =>
    if h : ofMat_equiv M' i = j
      then eqToHom (ofMat_X_equiv' M' i j h)
      else 0
  inv := fun j i =>
    if h : ofMat_equiv M' i = j
      then eqToHom (ofMat_X_equiv' M' i j h).symm
      else 0
  hom_inv_id := by
    -- Artistotle had proved this but the proof was causing performance issues so it needs to be
    -- replaced with a better proof
    sorry
  inv_hom_id := by
    ext j k
    simp only [CategoryStruct.comp] at *;
    convert Finset.sum_eq_single ( ( ofMat_equiv M' ).symm j ) _ _ using 1 <;>
      simp +decide only [Equiv.apply_symm_apply, ↓reduceDIte, Preadditive.IsIso.comp_left_eq_zero,
        dite_eq_right_iff]
    · split_ifs with h <;> simp +decide [ h ]
      rw [ eq_comm ] at h ; induction h ; simp +decide [ eqToHom_refl ]
    · intro b hb
      split_ifs with h1 h2
      · intro hab
        exact absurd ((ofMat_equiv M').injective (by rwa [Equiv.apply_symm_apply])) hab
      · simp
      · simp
      · simp
    · exact absurd (Finset.mem_univ _)

noncomputable instance : (toMat_ C).EssSurj where
  -- Aristotle generated proof
  mem_essImage M' := ⟨ofMat_ M', ⟨toMat_ofMat_iso M'⟩⟩

instance : (toMat_ C).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

/-- Computable version of `CategoryTheory.Limits.biprod` -/
def cbiprod : CMat_ C := CMat_.ofList (M.toList ++ N.toList)

@[inherit_doc] infixl:65 " ⊞ₖ " => cbiprod

omit [Category C] [Preadditive C]
theorem cbiprod_assoc : M ⊞ₖ N ⊞ₖ K = M ⊞ₖ (N ⊞ₖ K) := by
  simp [cbiprod]

end definition

section embedding

variable (C : Type*)

/--
This is not a simp lemma because I am worried that this is often an equality of types.
But I think this could work as a simp lemma, I'm just not sure if it would cause defeq issues.
-/
theorem apply_X_ofList_singleton {A : C} (i : (CMat_.ofList [A]).ι) :
    (CMat_.ofList [A]).X i = A := by
  -- Aristotle proof
  simp only [X, List.length_cons, List.length_nil, Nat.reduceAdd, ι.toFin];
  unfold CMat_.ι at i;
  fin_cases i ; rfl

unseal ι in
theorem ofList_singleton_card {A : C} : Fintype.card (CMat_.ofList [A]).ι = 1 := by
  -- Aristotle proof
  simp [CMat_.ι] at *

-- Aristotle proof
unseal ι in
instance ofList_singleton_unique {A : C} : Unique (CMat_.ofList [A]).ι :=
  inferInstanceAs (Unique (Fin 1))

variable [Category C] [Preadditive C]

def embedding : C ⥤ CMat_ C where
  obj X := CMat_.ofList [X]
  map {A B} f i j := cast (by simp [apply_X_ofList_singleton]) f
  map_id f := by
    -- Aristotle proof
    ext i j
    generalize_proofs at *;
    generalize_proofs at *; simp_all +decide only [id_apply, Subsingleton.elim i j, ↓reduceDIte] ;
    simp +decide only [eqToHom, eq_mpr_eq_cast];
    congr! 1
    generalize_proofs at *; -- This should close the goal. If not, it means there's a mistake in the
    -- previous steps. In that case, you need to put in more proof steps.;
    -- all_goals generalize_proofs at *; simp_all +decide [ id_apply, Subsingleton.elim i j ] ;
    congr! 1
    generalize_proofs at *; -- This should close the goal. If not, it means there's a mistake in the
    -- previous steps. In that case, you need to put in more proof steps;
    (generalize_proofs at *; simp_all +decide only [Subsingleton.elim i j] ;);
    exact Eq.symm (apply_X_ofList_singleton C j)
  map_comp f g := by
    -- Aristotle proof
    ext i j; simp +decide only [comp_apply, Finset.univ_unique, Finset.sum_singleton] ;
    unfold CMat_.X at *
    generalize_proofs at *;
    generalize_proofs at *;
    grind +ring

@[simp]
theorem ofList_singleton {A : C} : CMat_.ofList [A] = (embedding C).obj A := rfl

@[simp]
theorem toList_embedding {A : C} : ((embedding C).obj A).toList = [A] := rfl

theorem X_embedding {A : C} (i : ((embedding C).obj A).ι) : ((embedding C).obj A).X i = A :=
  apply_X_ofList_singleton C i

-- Aristotle generated definition
instance {A : C} : Unique ((embedding C).obj A).ι := ofList_singleton_unique C

namespace Embedding

def fullyFaithful : (embedding C).FullyFaithful where
  preimage {A B} f' :=
    -- The default here means 0, and it comes from the `Unique` instance above.
    cast (by simp [X_embedding]) (f' default default)
  map_preimage {A B} f' := by
    -- Aristotle proof
    unfold embedding;
    ext i j; simp only [ofList_singleton, cast_cast];
    exact Eq.symm ( by rw [ show i = default from Subsingleton.elim _ _, show j = default from
      Subsingleton.elim _ _ ] ; rfl )
  preimage_map {A B} f := by
    -- Aristotle proof
    generalize_proofs at *;
    convert cast_cast _ _ _;
    grind +ring

instance : (embedding C).Faithful := (fullyFaithful C).faithful
instance : (embedding C).Full := (fullyFaithful C).full

instance : Functor.Additive (embedding C) where
  map_add {M N f g} := by
    -- Aristotle proof
    ext i j; simp +decide only [add_apply] ;
    convert congr_arg ( fun x : M ⟶ N => x ) rfl using 1;
    rotate_right;
    · exact f + g;
    · exact congr_arg₂ _ ( X_embedding C i ) ( X_embedding C j );
    · (expose_names; exact HEq.symm (heq_of_eqRec_eq (id (Eq.symm e_1)) rfl));
    · congr! 1;
      · congr! 1;
        congr! 1;
        congr! 1;
        congr! 1;
        congr! 1;
        congr! 1;
        · exact X_embedding C i;
        · exact X_embedding C j;
      · unfold embedding; aesop;
      · unfold embedding; aesop;

end Embedding

end embedding

-- TODO: Pick a simp normal form
-- TODO: implement Repr using cibiprod and the embedding

section linear

instance {R : Type*} [Semiring R] (m n : Type*) (α : m → n → Type*)
    [(i : m) → (j : n) → AddCommGroup (α i j)] [(i : m) → (j : n) → Module R (α i j)] :
    Module R (DMatrix m n α) where
  smul r M := fun i j ↦ r • (M i j)
  mul_smul r s M := by ext i j; exact mul_smul r s (M i j)
  one_smul M := by ext i j; exact one_smul R (M i j)
  smul_zero r := by ext i j; exact smul_zero r
  smul_add r M N := by ext i j; exact smul_add r (M i j) (N i j)
  add_smul r s N := by ext i j; exact add_smul r s (N i j)
  zero_smul M := by ext i j; exact zero_smul R (M i j)

variable {R : Type*} [Semiring R]
  {C : Type*} [Category C] [Preadditive C] [Linear R C]

instance : Linear R (CMat_ C) where
  homModule M N := inferInstanceAs <| Module R
    (DMatrix M.ι N.ι fun i j => M.X i ⟶ N.X j)
  smul_comp := by
    -- Aristotle proof
    intros X Y Z r f g
    ext i j
    simp only [comp_apply];
    convert Finset.smul_sum.symm using 2;
    -- Apply the linearity of the composition in the first argument.
    apply Linear.smul_comp
  comp_smul := by
    -- Aristotle proof
    intro X Y Z f r g
    ext i j
    simp only [comp_apply] at *;
    convert Finset.smul_sum.symm using 2
    generalize_proofs at *; -- This should close the goal. If not, it means there's a mistake in the
    -- previous steps. In that case, you need to put in more proof steps.;
    apply Linear.comp_smul

end linear

end CMat_
