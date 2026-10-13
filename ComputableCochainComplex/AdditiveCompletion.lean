module

public import Mathlib
public import ComputableCochainComplex.ComputableCategories
public import Util.Texify

@[expose] public section

open CategoryTheory

structure CMat_ (C : Type*) where
  ofList ::
    toList : List C

instance (C : Type*) [Texify C] : Texify (CMat_ C) where
  texify x := if x.toList = [] then "0" else
    x.toList.map texifyWithBracketsAndParenthesesIfNecessary |> r" \oplus ".intercalate
  requiresParentheses := true

syntax (name := «term[_,]ₘ») "[" withoutPosition(term,*,?) "]ₘ" : term

macro_rules
  | `([ $elems,* ]ₘ) => `(CMat_.ofList [ $elems,* ])

recommended_spelling "empty" for "[]ₘ" in [«term[_,]ₘ»]
recommended_spelling "singleton" for "[x]ₘ" in [«term[_,]ₘ»]

namespace CMat_

section lists
variable {C : Type*} (A : C) (M N K : CMat_ C)

theorem toList_empty : ([]ₘ : CMat_ C).toList = [] := rfl

theorem toList_singleton : [A]ₘ.toList = [A] := rfl

end lists

section indexing

variable {C : Type*} {M : CMat_ C}

/--
Mirrors the API of `CategoryTheory.Mat_.ι`.
This is irreducible because it is effectively irreducible in `Mat_`, and we should mirror the API.
-/
@[irreducible]
def ι (M : CMat_ C) : Type := Fin M.toList.length

/- Auxillary definitions that are used to avoid defeq abuse. -/
unseal ι in
def ι.toFin {M : CMat_ C} (i : M.ι) : Fin M.toList.length := i
unseal ι in
def ι.ofFin {M : CMat_ C} (i : Fin M.toList.length) : M.ι := i

@[simp]
theorem ι.ofFin_toFin {M : CMat_ C} (i : M.ι) : ι.ofFin i.toFin = i := rfl
@[simp]
theorem ι.toFin_ofFin {M : CMat_ C} (i : Fin M.toList.length) : (ι.ofFin i).toFin = i := rfl

def ι.finEquiv {M : CMat_ C} : M.ι ≃ Fin M.toList.length where
  toFun := ι.toFin
  invFun := ι.ofFin
  left_inv i := by dsimp
  right_inv j := by dsimp

unseal ι in
instance fintype : Fintype M.ι := inferInstanceAs <| Fintype (Fin M.toList.length)
unseal ι in
instance : DecidableEq M.ι := inferInstanceAs <| DecidableEq (Fin M.toList.length)

/-- Mirrors the API of `CategoryTheory.Mat_.X` -/
@[irreducible]
def X : M.ι → C := fun i ↦ M.toList[i.toFin]

end indexing

section category

variable {C : Type*} [Category C] [Preadditive C] (M N K : CMat_ C)

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

instance [∀ (X Y : C), Texify (X ⟶ Y)] (M N : CMat_ C) :
    Texify (CMat_.Hom M N) where
  texify x :=
    if M.toList.length = 0 ∨ N.toList.length = 0 then
      "0"
    else
      let getEntry (i : Fin N.toList.length) (j : Fin M.toList.length) : String :=
        texifyWithBrackets (x (CMat_.ι.ofFin j) (CMat_.ι.ofFin i))
      let getRow (i : Fin N.toList.length) : String :=
        Finset.univ.sort.map (getEntry i) |> " & ".intercalate
      let entries : String := Finset.univ.sort.map getRow |> r" \\ ".intercalate
      r"\begin{pmatrix} " ++ entries ++ r" \end{pmatrix}"
  requiresParentheses := false

instance [∀ (X Y : C), Texify (X ⟶ Y)] (M N : CMat_ C) :
    Texify (M ⟶ N) := inferInstanceAs (Texify (CMat_.Hom M N))

unseal ι X in
/--
Constructor for explicit morphisms, e.g. in interactive use
-/
def Hom.ofFin {C : Type*} [Category C] [Preadditive C] (xs ys : List C)
    (f : Π (i : Fin xs.length) (j : Fin ys.length), xs[i] ⟶ ys[j]) :
    ofList xs ⟶ ofList ys := f

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

def cbiprod : CMat_ C := .ofList (M.toList ++ N.toList)

def cbiprod_ι_equiv' {M N : CMat_ C} : (M.cbiprod N).ι ≃ M.ι ⊕ N.ι :=
  have : (CMat_.ofList (M.toList ++ N.toList)).toList.length = M.toList.length + N.toList.length
    := by simp
  ι.finEquiv |>.trans (finCongr this) |>.trans finSumFinEquiv.symm
    |>.trans (ι.finEquiv.symm.sumCongr ι.finEquiv.symm)

omit [Category C] [Preadditive C] in
/-- Looking up a left summand in the concatenation recovers the original object. -/
theorem X_symm_cbiprod_ι_equiv'_inl (i : M.ι) :
    (M.cbiprod N).X (cbiprod_ι_equiv'.symm (.inl i)) = M.X i := by
  unfold X
  exact List.getElem_append_left i.toFin.isLt

omit [Category C] [Preadditive C] in
/-- Looking up a right summand in the concatenation recovers the original object. -/
theorem X_symm_cbiprod_ι_equiv'_inr (i : N.ι) :
    (M.cbiprod N).X (cbiprod_ι_equiv'.symm (.inr i)) = N.X i := by
  unfold X
  simpa only [Nat.add_comm] using (List.getElem_append_right' M.toList i.toFin.isLt).symm

/-- The projection from the concatenation onto its left summands. -/
def cbiprod.fst : M.cbiprod N ⟶ M :=
  (Equiv.piCongrLeft' (fun i => ∀ j, (M.cbiprod N).X i ⟶ M.X j) cbiprod_ι_equiv').symm
    (fun k => match k with
      | .inl i => fun j => eqToHom (X_symm_cbiprod_ι_equiv'_inl M N i) ≫ (𝟙 M) i j
      | .inr _ => fun _ => 0)

/-- The projection from the concatenation onto its right summands. -/
def cbiprod.snd : M.cbiprod N ⟶ N :=
  (Equiv.piCongrLeft' (fun i => ∀ j, (M.cbiprod N).X i ⟶ N.X j) cbiprod_ι_equiv').symm
    (fun k => match k with
      | .inl _ => fun _ => 0
      | .inr i => fun j => eqToHom (X_symm_cbiprod_ι_equiv'_inr M N i) ≫ (𝟙 N) i j)

/-- Pair two matrices by concatenating their columns. -/
def cbiprod.pair {M N K : CMat_ C} (f : K ⟶ M) (g : K ⟶ N) : K ⟶ M.cbiprod N :=
  fun i => (Equiv.piCongrLeft' (fun j => K.X i ⟶ (M.cbiprod N).X j) cbiprod_ι_equiv').symm
    (fun k => match k with
      | .inl j => f i j ≫ eqToHom (X_symm_cbiprod_ι_equiv'_inl M N j).symm
      | .inr j => g i j ≫ eqToHom (X_symm_cbiprod_ι_equiv'_inr M N j).symm)

/-- Composing with the left projection extracts a column from the left block. -/
theorem cbiprod.comp_fst_apply {M N K : CMat_ C} (h : K ⟶ M.cbiprod N) (i j) :
    (h ≫ cbiprod.fst M N) i j =
      h i (cbiprod_ι_equiv'.symm (.inl j)) ≫ eqToHom (X_symm_cbiprod_ι_equiv'_inl M N j) := by
  rw [comp_apply, ← cbiprod_ι_equiv'.symm.sum_comp, Fintype.sum_sum_type]
  simp only [cbiprod.fst, Equiv.piCongrLeft'_symm_apply_apply, Limits.comp_zero,
    Finset.sum_const_zero, add_zero, id_apply, comp_dite, Finset.sum_dite_eq',
    Finset.mem_univ, ite_true, eqToHom_refl, Category.comp_id]

/-- Composing with the right projection extracts a column from the right block. -/
theorem cbiprod.comp_snd_apply {M N K : CMat_ C} (h : K ⟶ M.cbiprod N) (i j) :
    (h ≫ cbiprod.snd M N) i j =
      h i (cbiprod_ι_equiv'.symm (.inr j)) ≫ eqToHom (X_symm_cbiprod_ι_equiv'_inr M N j) := by
  rw [comp_apply, ← cbiprod_ι_equiv'.symm.sum_comp, Fintype.sum_sum_type]
  simp only [cbiprod.snd, Equiv.piCongrLeft'_symm_apply_apply, Limits.comp_zero,
    Finset.sum_const_zero, zero_add, id_apply, comp_dite, Finset.sum_dite_eq',
    Finset.mem_univ, ite_true, eqToHom_refl, Category.comp_id]

/-- Concatenation of lists gives computable binary biproducts of matrices. -/
instance : ComputableBinaryBiproduct (CMat_ C) where
  computableBinaryBiproductData P Q := .mkOfProduct P Q (pt := P.cbiprod Q)
    (fst := cbiprod.fst P Q) (snd := cbiprod.snd P Q) (pair := fun _ => cbiprod.pair)
    (pair_fst := by
      intro R f g
      ext i j
      simp only [cbiprod.comp_fst_apply, cbiprod.pair, Equiv.piCongrLeft'_symm_apply_apply,
        Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
    (pair_snd := by
      intro R f g
      ext i j
      simp only [cbiprod.comp_snd_apply, cbiprod.pair, Equiv.piCongrLeft'_symm_apply_apply,
        Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
    (pair_eta := by
      intro R h
      ext i j
      obtain ⟨j, rfl⟩ := cbiprod_ι_equiv'.symm.surjective j
      cases j <;>
        simp only [cbiprod.pair, Equiv.piCongrLeft'_symm_apply_apply,
          cbiprod.comp_fst_apply, cbiprod.comp_snd_apply,
          Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])

/--
Same as `cbiprod_ι_equiv` but expressed with proper notation and thus with types
-/
def cbiprod_ι_equiv {M N : CMat_ C} : (M ⊞ᶜ N).ι ≃ M.ι ⊕ N.ι := cbiprod_ι_equiv'

instance : IsEmpty ([]ₘ : CMat_ C).ι where
  false i := isEmptyElim (by simpa using i.toFin)

theorem hom_from_empty_eq_zero (h : []ₘ ⟶ M) : h = 0 := by
  ext i j
  exact isEmptyElim i

theorem hom_to_empty_eq_zero (h : M ⟶ []ₘ) : h = 0 := by
  ext i j
  exact isEmptyElim j

instance : HasExplicitZeroObject (CMat_ C) := .mkOfPreadditive (CMat_ C) []ₘ
  hom_from_empty_eq_zero hom_to_empty_eq_zero

/-- A matrix object is zero exactly when each of its summands is zero. -/
theorem isZero_iff (M : CMat_ C) : Limits.IsZero M ↔ ∀ i, Limits.IsZero (M.X i) := by
  constructor
  · intro h i
    rw [Limits.IsZero.iff_id_eq_zero] at h ⊢
    simpa only [id_apply_self] using congrFun (congrFun h i) i
  · intro h
    rw [Limits.IsZero.iff_id_eq_zero]
    ext i j
    by_cases hij : i = j
    · subst j
      simpa only [id_apply_self] using (Limits.IsZero.iff_id_eq_zero _).mp (h i)
    · exact id_apply_of_ne M i j hij

/-- A matrix object is zero exactly when all objects in its list are zero. -/
theorem isZero_iff_forall_mem (M : CMat_ C) :
    Limits.IsZero M ↔ ∀ X ∈ M.toList, Limits.IsZero X := by
  rw [isZero_iff]
  constructor
  · intro h X hX
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hX
    simpa only [X, ι.toFin_ofFin] using h (ι.ofFin ⟨i, hi⟩)
  · intro h i
    simpa only [CMat_.X] using h _ (List.getElem_mem i.toFin.isLt)

/-- Decide whether a matrix object is zero by checking its finitely many summands. -/
instance {V : Type*} [Category V] [Preadditive V] [DecidablePred (Limits.IsZero : V → Prop)] :
    DecidablePred (Limits.IsZero : CMat_ V → Prop) := fun M ↦
  decidable_of_iff (∀ X ∈ M.toList, Limits.IsZero X) (isZero_iff_forall_mem M).symm

-- Idea: Maybe we can translate the `HasFiniteBiproducts` instance from `CategoryTheory.Mat_` using
-- an equivalence. I don't know if this would make it computable though, which we might need.
-- This would show existence of finite biproducts but it would make them noncomputable. --Annie

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
  -- Cleaned-up Aristotle proof
  map_surjective {M N} f' := by constructor; rfl

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

-- Cleaned-up Aristotle generated theorem
omit [Category C] [Preadditive C] in
private theorem ofMat_X_equiv (M' : Mat_ C) (i : (ofMat_ M').ι) :
    (ofMat_ M').X i = M'.X (ofMat_equiv M' i) := by
  simp only [CMat_.X, Fin.getElem_fin, ofMat_, List.getElem_ofFn, Function.comp_apply]
  rfl

-- Cleaned-up Aristotle generated theorem
omit [Category C] [Preadditive C] in
private theorem ofMat_X_equiv' (M' : Mat_ C) (i : (ofMat_ M').ι) (j : M'.ι)
    (h : ofMat_equiv M' i = j) :
    (ofMat_ M').X i = M'.X j := by subst h; exact ofMat_X_equiv M' i

open Classical in
/-- Reindexing by `ofMat_equiv` identifies the reconstructed list with the original matrix
object. -/
private noncomputable def toMat_ofMat_iso (M' : Mat_ C) :
    (toMat_ C).obj (ofMat_ M') ≅ M' where
  hom := fun i j ↦ if h : ofMat_equiv M' i = j then eqToHom (ofMat_X_equiv' M' i j h) else 0
  inv := fun j i ↦ if h : ofMat_equiv M' i = j then eqToHom (ofMat_X_equiv' M' i j h).symm else 0
  hom_inv_id := by
    ext i k
    simp only [Mat_.comp_apply, dite_comp, comp_dite, Limits.zero_comp, Limits.comp_zero,
      Finset.sum_dite_eq, Finset.mem_univ, ite_true]
    by_cases hik : i = k
    · subst k
      simp only [↓reduceDIte, eqToHom_trans, eqToHom_refl, Mat_.id_apply_self]
    · rw [dif_neg ((ofMat_equiv M').injective.ne hik), Mat_.id_apply_of_ne _ _ _ hik]
  inv_hom_id := by
    ext j k
    rw [Mat_.comp_apply]
    erw [← (ofMat_equiv M').symm.sum_comp]
    simp only [Equiv.apply_symm_apply, dite_comp, comp_dite, Limits.zero_comp, Limits.comp_zero,
      Finset.sum_dite_eq', Finset.mem_univ, ite_true]
    by_cases hjk : j = k
    · subst k
      simp only [↓reduceDIte, eqToHom_trans, eqToHom_refl, Mat_.id_apply_self]
    · rw [dif_neg (Ne.symm hjk), Mat_.id_apply_of_ne _ _ _ hjk]

noncomputable instance : (toMat_ C).EssSurj where
  -- Aristotle generated proof
  mem_essImage M' := ⟨ofMat_ M', ⟨toMat_ofMat_iso M'⟩⟩

instance : (toMat_ C).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

end category

section embedding

variable (C : Type*)

/--
This is not a simp lemma because I am worried that this is often an equality of types.
But I think this could work as a simp lemma, I'm just not sure if it would cause defeq issues.
-/
theorem apply_X_ofList_singleton {A : C} (i : [A]ₘ.ι) :
    (CMat_.ofList [A]).X i = A := by
  -- Cleaned-up Aristotle proof
  simp only [X, List.length_cons, List.length_nil, Nat.reduceAdd, ι.toFin]
  unfold CMat_.ι at i
  fin_cases i
  rfl

unseal ι in
theorem singleton_ι_card {A : C} : Fintype.card [A]ₘ.ι = 1 := by
  -- Cleaned-up Aristotle proof
  simp [CMat_.ι]

-- Aristotle proof
unseal ι in
instance singleton_ι_unique {A : C} : Unique [A]ₘ.ι :=
  inferInstanceAs (Unique (Fin 1))

variable [Category C] [Preadditive C]

def embedding : C ⥤ CMat_ C where
  obj X := CMat_.ofList [X]
  map {A B} f i j := cast (by simp [apply_X_ofList_singleton]) f
  map_id f := by
    -- Cleaned-up Aristotle proof
    ext i j
    simp only [id_apply, Subsingleton.elim i j, ↓reduceDIte, eqToHom, eq_mpr_eq_cast]
    congr! 2
    exact (apply_X_ofList_singleton C j).symm
  map_comp f g := by
    -- Cleaned-up Aristotle proof
    ext i j
    simp only [comp_apply, Finset.univ_unique]
    unfold CMat_.X at *
    grind

@[simp]
theorem ofList_singleton {A : C} : CMat_.ofList [A] = (embedding C).obj A := rfl

@[simp]
theorem toList_embedding {A : C} : ((embedding C).obj A).toList = [A] := rfl

theorem X_embedding {A : C} (i : ((embedding C).obj A).ι) : ((embedding C).obj A).X i = A :=
  apply_X_ofList_singleton C i

-- Aristotle generated definition
instance {A : C} : Unique ((embedding C).obj A).ι := singleton_ι_unique C

namespace Embedding

def fullyFaithful : (embedding C).FullyFaithful where
  preimage {A B} f' :=
    -- The default here means 0, and it comes from the `Unique` instance above.
    cast (by simp [X_embedding]) (f' default default)
  map_preimage {A B} f' := by
    -- Cleaned-up Aristotle proof
    unfold embedding
    ext i j
    simp only [cast_cast]
    rw [Subsingleton.elim i default, Subsingleton.elim j default]
    rfl
  preimage_map {A B} f := by
    -- Cleaned-up Aristotle proof
    generalize_proofs
    convert cast_cast _ _ _;
    grind

instance : (embedding C).Faithful := (fullyFaithful C).faithful
instance : (embedding C).Full := (fullyFaithful C).full

instance : Functor.Additive (embedding C) where
  map_add {M N f g} := by
    -- Cleaned-up Aristotle proof
    ext i j
    convert congr_arg (fun x : M ⟶ N ↦ x) rfl using 1
    rotate_right
    · exact f + g
    · exact congr_arg₂ _ (X_embedding C i) (X_embedding C j)
    · rename_i h
      exact HEq.symm (heq_of_eqRec_eq h.symm rfl)
    · unfold embedding
      simp only [add_apply]
      congr! 1
      · congr!
        · exact X_embedding C i
        · exact X_embedding C j
      · aesop
      · aesop

end Embedding

end embedding

section lift

variable {C : Type*} [Category C] [Preadditive C]
variable {D : Type*} [Category D] [Preadditive D]

section extension

open CategoryTheory.Limits

variable [ComputableBinaryBiproduct D] [HasExplicitZeroObject D]

omit [Preadditive C] in
/-- The computed bicone for the image summands has the expected list-fold object. -/
theorem extendBicone_pt_eq (F : C ⥤ D) (M : CMat_ C) :
    (finCBicone (fun i : Fin M.toList.length => F.obj (M.X (ι.ofFin i)))).pt =
      (M.toList.map F.obj).cbiprod := by
  rw [finCBicone_pt]
  congr 1
  simp only [X, ι.toFin_ofFin, Fin.getElem_fin]
  exact List.ofFn_getElem_eq_map M.toList F.obj

/-- The explicit finite bicone of the images of the summands of a matrix object. -/
def extendBicone (F : C ⥤ D) (M : CMat_ C) :
    Limits.Bicone (fun i : M.ι => F.obj (M.X i)) where
  pt := (M.toList.map F.obj).cbiprod
  π i := eqToHom (extendBicone_pt_eq F M).symm ≫
    (finCBicone (fun i : Fin M.toList.length => F.obj (M.X (ι.ofFin i)))).π i.toFin
  ι i := (finCBicone (fun i : Fin M.toList.length => F.obj (M.X (ι.ofFin i)))).ι i.toFin ≫
    eqToHom (extendBicone_pt_eq F M)
  ι_π i j := by
    classical
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    split_ifs with hij
    · subst j
      exact bicone_ι_π_self _ i.toFin
    · exact bicone_ι_π_ne _ (ι.finEquiv.injective.ne hij)

omit [Preadditive C] in
/-- The explicit image bicone resolves the identity as a sum of its projections. -/
theorem extendBicone_total (F : C ⥤ D) (M : CMat_ C) :
    ∑ i, (extendBicone F M).π i ≫ (extendBicone F M).ι i = 𝟙 (extendBicone F M).pt := by
  let b := finCBicone (fun i : Fin M.toList.length => F.obj (M.X (ι.ofFin i)))
  have hsum : ∑ i : M.ι, b.π i.toFin ≫ b.ι i.toFin = 𝟙 b.pt :=
    (ι.finEquiv.sum_comp _).trans (finCBicone_total _)
  simpa only [extendBicone, b, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc,
    Category.id_comp, eqToHom_trans, eqToHom_refl] using
    congrArg (fun h => eqToHom (extendBicone_pt_eq F M).symm ≫ h ≫
      eqToHom (extendBicone_pt_eq F M)) hsum

/-- The explicit image bicone is a biproduct. -/
def extendBiconeIsBilimit (F : C ⥤ D) (M : CMat_ C) : (extendBicone F M).IsBilimit :=
  isBilimitOfTotal _ (extendBicone_total F M)

/-- Send a matrix to the morphism between the explicit sums of its image summands. -/
def extendMap (F : C ⥤ D) {M N : CMat_ C} (f : M ⟶ N) :
    (extendBicone F M).pt ⟶ (extendBicone F N).pt :=
  (extendBiconeIsBilimit F M).isColimit.desc
    (Cofan.mk _ fun i => ∑ j, F.map (f i j) ≫ (extendBicone F N).ι j)

/-- Restricting the extended map to one summand gives its row of image morphisms. -/
theorem ι_extendMap (F : C ⥤ D) {M N : CMat_ C} (f : M ⟶ N) (i : M.ι) :
    (extendBicone F M).ι i ≫ extendMap F f =
      ∑ j, F.map (f i j) ≫ (extendBicone F N).ι j :=
  (extendBiconeIsBilimit F M).isColimit.fac
    (Cofan.mk _ fun i => ∑ j, F.map (f i j) ≫ (extendBicone F N).ι j) ⟨i⟩

/-- The entries of the extended map are the images of the original matrix entries. -/
theorem ι_extendMap_π (F : C ⥤ D) {M N : CMat_ C} (f : M ⟶ N) (i : M.ι) (j : N.ι) :
    (extendBicone F M).ι i ≫ extendMap F f ≫ (extendBicone F N).π j = F.map (f i j) := by
  rw [← Category.assoc, ι_extendMap]
  erw [Preadditive.sum_comp Finset.univ]
  simp only [Category.assoc, (extendBicone F N).ι_π, comp_dite, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, ite_true, eqToHom_refl, Category.comp_id]

omit [Preadditive C] in
/-- Maps between explicit image sums are determined by their matrix entries. -/
theorem extendBicone_hom_ext (F : C ⥤ D) {M N : CMat_ C}
    {f g : (extendBicone F M).pt ⟶ (extendBicone F N).pt}
    (h : ∀ i j, (extendBicone F M).ι i ≫ f ≫ (extendBicone F N).π j =
      (extendBicone F M).ι i ≫ g ≫ (extendBicone F N).π j) : f = g := by
  apply (extendBiconeIsBilimit F M).isColimit.hom_ext
  intro i
  apply (extendBiconeIsBilimit F N).isLimit.hom_ext
  intro j
  simpa only [Limits.Bicone.toCocone_ι_app, Limits.Bicone.toCone_π_app, ← Category.assoc]
    using h i.as j.as

variable (F : C ⥤ D) [F.Additive]

/-- The extension sends identity matrices to identity morphisms. -/
theorem extendMap_id (M : CMat_ C) : extendMap F (𝟙 M) = 𝟙 (extendBicone F M).pt := by
  apply extendBicone_hom_ext F
  intro i j
  rw [ι_extendMap_π]
  by_cases hij : i = j
  · subst j
    simpa only [id_apply_self, F.map_id, Category.id_comp] using
      (bicone_ι_π_self (extendBicone F M) i).symm
  · simpa only [id_apply_of_ne M i j hij, F.map_zero, Category.id_comp] using
      (bicone_ι_π_ne (extendBicone F M) hij).symm

/-- The extension sends matrix multiplication to composition. -/
theorem extendMap_comp {M N K : CMat_ C} (f : M ⟶ N) (g : N ⟶ K) :
    extendMap F (f ≫ g) = extendMap F f ≫ extendMap F g := by
  apply extendBicone_hom_ext F
  intro i k
  simp only [Category.assoc, ι_extendMap_π, comp_apply, F.map_sum, F.map_comp]
  rw [← Category.assoc ((extendBicone F M).ι i) (extendMap F f), ι_extendMap]
  erw [Preadditive.sum_comp Finset.univ]
  simp only [Category.assoc, ι_extendMap_π]

/-- The extension respects addition of matrices. -/
theorem extendMap_add {M N : CMat_ C} (f g : M ⟶ N) :
    extendMap F (f + g) = extendMap F f + extendMap F g := by
  apply extendBicone_hom_ext F
  intro i j
  simp only [Preadditive.comp_add, Preadditive.add_comp, ι_extendMap_π, add_apply, F.map_add]

/-- Extend an additive functor to finite formal sums using the chosen computable biproducts. -/
def extend : CMat_ C ⥤ D where
  obj M := (M.toList.map F.obj).cbiprod
  map f := extendMap F f
  map_id := extendMap_id F
  map_comp := extendMap_comp F

instance : (extend F).Additive where
  map_add {_ _ f g} := extendMap_add F f g

/-- The extension evaluates objects using the chosen list biproduct. -/
@[simp]
theorem extend_obj (M : CMat_ C) : (extend F).obj M = (M.toList.map F.obj).cbiprod := rfl

/-- Matrix entries of the functor can be computed without unfolding its construction. -/
@[reassoc (attr := simp)]
theorem ι_extend_map_π {M N : CMat_ C} (f : M ⟶ N) (i : M.ι) (j : N.ι) :
    (extendBicone F M).ι i ≫ (extend F).map f ≫ (extendBicone F N).π j = F.map (f i j) :=
  ι_extendMap_π F f i j

end extension

/-- Flatten a formal sum of formal sums using the computable biproducts in `CMat_ C`. -/
def bind : CMat_ (CMat_ C) ⥤ CMat_ C := extend (𝟭 (CMat_ C))

/-- Apply an additive functor to formal sums and their matrices of morphisms. -/
def mapCMat_ (F : C ⥤ D) [F.Additive] : CMat_ C ⥤ CMat_ D := extend (F ⋙ embedding D)

end lift

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
    -- Cleaned-up Aristotle proof
    intros
    ext i j
    rw [comp_apply]
    convert Finset.smul_sum.symm
    apply Linear.smul_comp
  comp_smul := by
    -- Cleaned-up Aristotle proof
    intros
    ext i j
    rw [comp_apply]
    convert Finset.smul_sum.symm
    apply Linear.comp_smul

end linear

end CMat_
