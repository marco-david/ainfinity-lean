/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Data.Matrix.DMatrix
public import Mathlib.Data.Finset.Sort
public import ComputableCochainComplex.ComputableCategories
public import Util.Texify

/-!
# Computable additive completion

Objects are finite lists and morphisms are matrices of morphisms in a preadditive category.
List concatenation supplies binary biproducts; the empty list supplies the zero object.
`extend` evaluates formal sums through an additive functor using explicit target biproducts.
These constructions support bounded categorical complexes and their module realizations.
-/

@[expose] public section

open CategoryTheory

/-- A finite formal sum with a supplied order, so morphisms have executable matrix coordinates. -/
structure CMat_ (C : Type*) where
  ofList ::
    /-- Ordered summands, retained explicitly for computation. -/
    toList : List C

/-- Render a formal sum using its ordered list of summands, with the empty sum displayed as zero. -/
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

section indexing

variable {C : Type*} {M : CMat_ C}

/--
Mirrors the API of `CategoryTheory.Mat_.ι`.
This is irreducible because it is effectively irreducible in `Mat_`, and we should mirror the API.
-/
@[irreducible]
def ι (M : CMat_ C) : Type := Fin M.toList.length

unseal ι in
/-- Read an abstract summand index as a list position for executable lookup. -/
def ι.toFin {M : CMat_ C} (i : M.ι) : Fin M.toList.length := i
unseal ι in
/-- Construct a summand index from a list position when building explicit matrices. -/
def ι.ofFin {M : CMat_ C} (i : Fin M.toList.length) : M.ι := i

/-- Converting an abstract summand index to a list position and back changes nothing. -/
@[simp]
theorem ι.ofFin_toFin {M : CMat_ C} (i : M.ι) : ι.ofFin i.toFin = i := rfl
/-- Converting a list position to an abstract summand index and back changes nothing. -/
@[simp]
theorem ι.toFin_ofFin {M : CMat_ C} (i : Fin M.toList.length) : (ι.ofFin i).toFin = i := rfl

/-- Identify summand indices with list positions for finite reindexing and summation. -/
def ι.finEquiv {M : CMat_ C} : M.ι ≃ Fin M.toList.length where
  toFun := ι.toFin
  invFun := ι.ofFin
  left_inv i := by dsimp
  right_inv j := by dsimp

unseal ι in
/-- Enumerate the finitely many summands for matrix multiplication. -/
instance fintype : Fintype M.ι := inferInstanceAs <| Fintype (Fin M.toList.length)
unseal ι in
/-- Decide index equality when constructing identity matrices. -/
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

/-- Matrix identities and matrix multiplication form the additive-completion category. -/
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

/-- Render a morphism matrix with target summands as rows and source summands as columns. -/
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

/-- Expose matrix rendering through categorical morphism notation. -/
instance [∀ (X Y : C), Texify (X ⟶ Y)] (M N : CMat_ C) :
    Texify (M ⟶ N) := inferInstanceAs (Texify (CMat_.Hom M N))

unseal ι X in
/--
Constructor for explicit morphisms, e.g. in interactive use
-/
def Hom.ofFin {C : Type*} [Category C] [Preadditive C] (xs ys : List C)
    (f : Π (i : Fin xs.length) (j : Fin ys.length), xs[i] ⟶ ys[j]) :
    ofList xs ⟶ ofList ys := f

/-- Equality of matrix entries determines a morphism, enabling entrywise categorical proofs. -/
@[ext] theorem hom_ext {M N : CMat_ C} (f g : M ⟶ N) (H : ∀ i j, f i j = g i j) : f = g :=
  DMatrix.ext_iff.mp H
/-- Expand an identity matrix entry for the biproduct and functor proofs. -/
theorem id_apply (M : CMat_ C) (i j : M.ι) :
    (𝟙 M : Hom M M) i j = if h : i = j then eqToHom (congr_arg M.X h) else 0 := rfl
/-- A diagonal identity entry is the identity of its summand. -/
@[simp] theorem id_apply_self (M : CMat_ C) (i : M.ι) : (𝟙 M : Hom M M) i i = 𝟙 _ := by
  simp [id_apply]
/-- An off-diagonal identity entry is zero. -/
@[simp] theorem id_apply_of_ne (M : CMat_ C) (i j : M.ι) (h : i ≠ j) : (𝟙 M : Hom M M) i j = 0 := by
  simp [id_apply, h]
/-- Composition is the finite sum of entrywise compositions. -/
@[simp] theorem comp_apply {M N K : CMat_ C} (f : M ⟶ N) (g : N ⟶ K) (i k) :
    (f ≫ g) i k = ∑ j : N.ι, f i j ≫ g j k := rfl
/-- Zero entries provide a default morphism matrix. -/
instance : Inhabited (M ⟶ N) := ⟨fun i j => (0 : M.X i ⟶ N.X j)⟩
/-- Add and subtract morphism matrices entrywise, reusing the dependent-function instance. -/
instance : AddCommGroup (M ⟶ N) := inferInstanceAs <| AddCommGroup (DMatrix M.ι N.ι _)
/-- Expose entrywise addition when proving additivity of realization. -/
@[simp] theorem add_apply {M N : CMat_ C} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j := rfl
/-- Finite sums distribute over matrix composition, so the completion is preadditive. -/
instance : Preadditive (CMat_ C) where
  add_comp M N K f f' g := by ext; simp [Finset.sum_add_distrib]
  comp_add M N K f g g' := by ext; simp [Finset.sum_add_distrib]

/-- Concatenate summand lists to compute a binary sum without choosing categorical limits. -/
def cbiprod : CMat_ C := .ofList (M.toList ++ N.toList)

/-- Split concatenated-list indices into their left and right blocks for the biproduct maps. -/
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

/-- The empty formal sum has no matrix indices. -/
instance : IsEmpty ([]ₘ : CMat_ C).ι where
  false i := isEmptyElim (by simpa using i.toFin)

/-- No source entries remain for the empty sum, certifying it as a zero object. -/
theorem hom_from_empty_eq_zero (h : []ₘ ⟶ M) : h = 0 := by
  ext i j
  exact isEmptyElim i

/-- The empty list is an explicit zero object in the additive completion. -/
instance : HasExplicitZeroObject (CMat_ C) where
  zero := []ₘ
  isZero := (Limits.IsZero.iff_id_eq_zero _).mpr (hom_from_empty_eq_zero _ _)

end category

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

/-- The realization of formal sums preserves matrix addition. -/
instance : (extend F).Additive where
  map_add {_ _ f g} := extendMap_add F f g

end extension

end lift

section linear

variable {R : Type*} [Semiring R]
  {C : Type*} [Category C] [Preadditive C] [Linear R C]

/-- Scalar multiplication is entrywise and commutes with matrix composition. -/
instance : Linear R (CMat_ C) where
  homModule M N := inferInstanceAs <| Module R
    (∀ (i : M.ι) (j : N.ι), M.X i ⟶ N.X j)
  smul_comp _ _ _ r f g := by
    ext i j
    change (∑ k, (r • f i k) ≫ g k j) = r • ∑ k, f i k ≫ g k j
    simp only [Linear.smul_comp, Finset.smul_sum]
  comp_smul _ _ _ f r g := by
    ext i j
    change (∑ k, f i k ≫ (r • g k j)) = r • ∑ k, f i k ≫ g k j
    simp only [Linear.comp_smul, Finset.smul_sum]

end linear

end CMat_
