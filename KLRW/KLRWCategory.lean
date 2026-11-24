/-
Copyright (c) 2026 Lillian Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lillian Liu, Marco David
-/
module
public import Mathlib
public import KLRW.KLRWAlgebra

/-!
# The KLRW category

The objects of the KLRW category are KLRW objects, and the morphisms from `X` to `Y`
are the elements of `klrwHom u ℏ X Y`, i.e. the elements `e_Y * a * e_X` of the KLRW
algebra. Composition is multiplication in the algebra, and the identity of `X` is its
idempotent `e_X`.

## Main definitions

* `KLRW.KLRWCat u ℏ P`: the KLRW category with coefficients in `S` and parameters `u ℏ : S`.
  Its objects are the KLRW objects of `P`; `KLRWCat.of u ℏ X` is the object given by `X`.
* The `Category`, `Preadditive` and `Linear S` instances on `KLRWCat u ℏ P`.
* `KLRW.KLRWCat.homOfOps`: the morphism given by a list of operations.

## Main results

* `KLRW.isIdempotentElem_idemMorph`: each `e_X` is idempotent.
* `KLRW.mem_klrwHom_iff`: `f` is a morphism from `X` to `Y` exactly when `e_Y * f * e_X = f`.
* `KLRW.mul_mem_klrwHom`: morphisms compose.
* `KLRW.generator_mem_klrwHom`: every strand generator is a morphism in klrwHom from its domain 
    (starting object) to its codomain (ending object).
* `KLRW.strandGenSeq_mem_klrwHom`: the product described by a list of strand operations is a
  morphism in klrwHom from its starting object to its end object.
* `KLRW.strandGenSeq_append`: splitting a list of operations splits its product. Running
  `ops₁ ++ ops₂` from `M` (that is, `ops₂` first, then `ops₁`) gives the product of the element
  for `ops₁`, started where `ops₂` ends, with the element for `ops₂`, started at `M`.
* `KLRW.KLRWCat.homOfOps_comp`: the morphism of `ops₂` followed by the morphism of `ops₁` is the
  morphism of `ops₁ ++ ops₂`.

## Implementation notes

* `f ≫ g` (first `f`, then `g`) is the product `g * f` in the algebra.
* Naming: `M` is the object a list of operations starts from (as in `strandGenSeq S M ops`) and
  `N` the object it ends at; `X Y Z` are objects in general hom-space statements; `f g` are
  elements of the free algebra or of the KLRW algebra.
* The parameters `u ℏ` are implicit in the lemmas, where the statement determines them, and
  explicit in `KLRWCat u ℏ P` and `KLRWCat.of u ℏ X`, where nothing else does. They are declared
  in two sections rather than at namespace level, so that `KLRWCat` can take them explicitly
  without shadowing an implicit `{u ℏ}`.
-/

@[expose] public section

namespace KLRW
open CategoryTheory FreeAlgebra

variable {V : Type*} [DecidableEq V] [Fintype V] {P : KLRWStructure V}
variable {S : Type*} [CommRing S]

section Lemmas

variable {u ℏ : S}

/-! ## From relations to equalities in the KLRW algebra -/

section RelationLemmas

variable {f g : KLRWFreeAlg S P}

/-- An implicit relation holds in `klrwRel`. -/
lemma klrwRel_of_implicit (h : KLRWImplicitConRel f g) : klrwRel u ℏ P f g :=
  RingConGen.Rel.of f g (Or.inl h)

/-- An explicit relation holds in `klrwRel`. -/
lemma klrwRel_of_explicit (h : KLRWExplicitConRel u ℏ f g) : klrwRel u ℏ P f g :=
  RingConGen.Rel.of f g (Or.inr h)

/-- Elements related by `klrwRel` are equal in the KLRW algebra. -/
lemma mk'_eq_of_klrwRel (h : klrwRel u ℏ P f g) :
    (klrwRel u ℏ P).mk' f = (klrwRel u ℏ P).mk' g :=
  (klrwRel u ℏ P).eq.mpr h

/-- An implicit relation becomes an equality in the KLRW algebra. -/
lemma mk'_eq_of_implicit (h : KLRWImplicitConRel f g) :
    (klrwRel u ℏ P).mk' f = (klrwRel u ℏ P).mk' g :=
  mk'_eq_of_klrwRel (klrwRel_of_implicit h)

/-- An explicit relation becomes an equality in the KLRW algebra. -/
lemma mk'_eq_of_explicit (h : KLRWExplicitConRel u ℏ f g) :
    (klrwRel u ℏ P).mk' f = (klrwRel u ℏ P).mk' g :=
  mk'_eq_of_klrwRel (klrwRel_of_explicit h)

end RelationLemmas

/-! ## Idempotents -/

/-- The idempotent of the codomain is a left identity for a generator. -/
lemma idemMorph_mul_generator (f : StrandGenerator P) :
    idemMorph u ℏ f.codomain * (klrwRel u ℏ P).mk' (ι _ f) = (klrwRel u ℏ P).mk' (ι _ f) :=
  mk'_eq_of_implicit (KLRWImplicitConRel.idem_left f.codomain f rfl)

/-- The idempotent of the domain is a right identity for a generator. -/
lemma generator_mul_idemMorph (f : StrandGenerator P) :
    (klrwRel u ℏ P).mk' (ι _ f) * idemMorph u ℏ f.domain = (klrwRel u ℏ P).mk' (ι _ f) :=
  mk'_eq_of_implicit (KLRWImplicitConRel.idem_right f.domain f rfl)

/-- The idempotent `e_X` is idempotent. -/
lemma isIdempotentElem_idemMorph (X : KLRWObject P) : IsIdempotentElem (idemMorph u ℏ X) :=
  idemMorph_mul_generator (.idem X)

/-! ## Hom-spaces -/

section HomSpaces

variable {X Y Z : KLRWObject P}

/-- `f` is a morphism from `X` to `Y` exactly when `e_Y * f * e_X = f`. -/
lemma mem_klrwHom_iff (f : KLRWAlg u ℏ P) :
    f ∈ klrwHom u ℏ X Y ↔ idemMorph u ℏ Y * f * idemMorph u ℏ X = f := by
  simp only [klrwHom, LinearMap.mem_range, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply]
  constructor
  · rintro ⟨a, rfl⟩
    rw [← mul_assoc (idemMorph u ℏ Y), (isIdempotentElem_idemMorph Y).eq, mul_assoc,
      mul_assoc, (isIdempotentElem_idemMorph X).eq]
  · intro h
    exact ⟨f, by rw [← mul_assoc, h]⟩

/-- The idempotent of the codomain is a left identity for any morphism. -/
lemma idemMorph_mul_of_mem (f : KLRWAlg u ℏ P) (hf : f ∈ klrwHom u ℏ X Y) :
    idemMorph u ℏ Y * f = f := by
  rw [← (mem_klrwHom_iff f).1 hf, ← mul_assoc, ← mul_assoc, (isIdempotentElem_idemMorph Y).eq]

/-- The idempotent of the domain is a right identity for any morphism. -/
lemma mul_idemMorph_of_mem (f : KLRWAlg u ℏ P) (hf : f ∈ klrwHom u ℏ X Y) :
    f * idemMorph u ℏ X = f := by
  rw [← (mem_klrwHom_iff f).1 hf, mul_assoc, (isIdempotentElem_idemMorph X).eq]

/-- Morphisms compose: if `f : X ⟶ Y` and `g : Y ⟶ Z`, then `g * f : X ⟶ Z`. -/
lemma mul_mem_klrwHom {f g : KLRWAlg u ℏ P} (hf : f ∈ klrwHom u ℏ X Y)
    (hg : g ∈ klrwHom u ℏ Y Z) : g * f ∈ klrwHom u ℏ X Z := by
  rw [mem_klrwHom_iff, mul_assoc, mul_assoc, mul_idemMorph_of_mem f hf]
  rw [← mul_assoc, idemMorph_mul_of_mem g hg]

/-- The idempotent of `X` is a morphism from `X` to `X`. -/
lemma idemMorph_mem_klrwHom : idemMorph u ℏ X ∈ klrwHom u ℏ X X := by
  rw [mem_klrwHom_iff, (isIdempotentElem_idemMorph X).eq, (isIdempotentElem_idemMorph X).eq]

/-- A generator is a klrwHom morphism from its domain to its codomain. -/
lemma generator_mem_klrwHom (f : StrandGenerator P) :
    (klrwRel u ℏ P).mk' (ι _ f) ∈ klrwHom u ℏ f.domain f.codomain := by
  rw [mem_klrwHom_iff, mul_assoc, generator_mul_idemMorph, idemMorph_mul_generator]

end HomSpaces

/-! ## Products of operation lists as morphisms -/

section StrandGenSeqLemmas

variable (M N : KLRWObject P)
variable (ops : List (StrandGenOp P))

/-- A strand generator sequence is a morphism from `M` to `strandGenSeqEnd M ops`. -/
lemma strandGenSeq_mem_klrwHom :
    (klrwRel u ℏ P).mk' (strandGenSeq S M ops) ∈ klrwHom u ℏ M (strandGenSeqEnd M ops) := by
  induction ops generalizing M with
  | nil => exact idemMorph_mem_klrwHom
  | cons op ops ih =>
      have hop :=
        generator_mem_klrwHom (u := u) (ℏ := ℏ) (op.toGenerator (strandGenSeqEnd M ops))
      rw [StrandGenOp.domain_toGenerator, StrandGenOp.codomain_toGenerator] at hop
      rw [strandGenSeq_cons, map_mul]
      exact mul_mem_klrwHom (ih M) hop

/-- If the operations `ops` take `M` to `N`, then their product is a morphism from `M`
to `N`. -/
lemma strandGenSeq_mem_klrwHom_of_eq (h : strandGenSeqEnd M ops = N) :
    (klrwRel u ℏ P).mk' (strandGenSeq S M ops) ∈ klrwHom u ℏ M N :=
  h ▸ strandGenSeq_mem_klrwHom M ops

/-- The idempotent of the end object is a left identity for a strand generator sequence. -/
lemma idemMorph_mul_strandGenSeq : idemMorph u ℏ (strandGenSeqEnd M ops) *
    (klrwRel u ℏ P).mk' (strandGenSeq S M ops) = (klrwRel u ℏ P).mk' (strandGenSeq S M ops) :=
  idemMorph_mul_of_mem _ (strandGenSeq_mem_klrwHom M ops)

/-- The idempotent of the start object is a right identity for a strand generator sequence. -/
lemma strandGenSeq_mul_idemMorph :
    (klrwRel u ℏ P).mk' (strandGenSeq S M ops) * idemMorph u ℏ M =
      (klrwRel u ℏ P).mk' (strandGenSeq S M ops) :=
  mul_idemMorph_of_mem _ (strandGenSeq_mem_klrwHom M ops)

/-- Splitting a list of operations splits its product: running `ops₁ ++ ops₂` from `M`
(`ops₂` first, then `ops₁`) gives the element for `ops₁`, started where `ops₂` ends, times the
element for `ops₂`, started at `M`. -/
lemma strandGenSeq_append (ops₁ ops₂ : List (StrandGenOp P)) :
    (klrwRel u ℏ P).mk' (strandGenSeq S M (ops₁ ++ ops₂)) =
      (klrwRel u ℏ P).mk' (strandGenSeq S (strandGenSeqEnd M ops₂) ops₁) *
        (klrwRel u ℏ P).mk' (strandGenSeq S M ops₂) := by
  induction ops₁ with
  | nil =>
      simp only [List.nil_append, strandGenSeq]
      symm
      exact idemMorph_mul_strandGenSeq M ops₂
  | cons op ops₁ ih =>
      rw [List.cons_append, strandGenSeq_cons, map_mul, ih, strandGenSeq_cons]
      simp [strandGenSeqEnd_append, mul_assoc]

end StrandGenSeqLemmas

end Lemmas

/-! ## The category structure -/

/-- The KLRW category with coefficients in `S` and parameters `u ℏ : S`. An object is a KLRW
object; the type records `u` and `ℏ` so that its morphisms know which KLRW algebra they live
in. -/
structure KLRWCat (u ℏ : S) (P : KLRWStructure V) where
  /-- The underlying KLRW object. -/
  toKLRWObject : KLRWObject P

/-- The object of the KLRW category corresponding to the KLRW object `X`. -/
abbrev KLRWCat.of (u ℏ : S) (X : KLRWObject P) : KLRWCat u ℏ P := ⟨X⟩

section CategoryInstances

variable {u ℏ : S}

/-- The KLRW category: morphisms from `X` to `Y` are the elements of
`klrwHom u ℏ X.toKLRWObject Y.toKLRWObject`, and `f ≫ g` (first `f`, then `g`) is the product
`g * f`. -/
instance : Category (KLRWCat u ℏ P) where
  Hom X Y := ↥(klrwHom u ℏ X.toKLRWObject Y.toKLRWObject)
  id X := ⟨idemMorph u ℏ X.toKLRWObject, idemMorph_mem_klrwHom⟩
  comp f g := ⟨g.val * f.val, mul_mem_klrwHom f.property g.property⟩
  id_comp f := by ext; exact mul_idemMorph_of_mem f.val f.property
  comp_id f := by ext; exact idemMorph_mul_of_mem f.val f.property
  assoc f g h := by ext; simp [mul_assoc]

/-- Two morphisms of the KLRW category are equal if their underlying algebra elements are. -/
@[ext]
lemma KLRWCat.hom_ext {X Y : KLRWCat u ℏ P} {f g : X ⟶ Y} (h : f.val = g.val) : f = g :=
  Subtype.ext h

/-- The algebra element of a composite: `f ≫ g` is `g * f`. -/
@[simp]
lemma KLRWCat.comp_val {X Y Z : KLRWCat u ℏ P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val = g.val * f.val := rfl

/-- The algebra element of the identity of `X` is the idempotent `e_X`. -/
@[simp]
lemma KLRWCat.id_val (X : KLRWCat u ℏ P) :
    (𝟙 X : X ⟶ X).val = idemMorph u ℏ X.toKLRWObject := rfl

/-- The morphism of the KLRW category given by a list of operations `ops` that takes
`X.toKLRWObject` to `Y.toKLRWObject`. -/
def KLRWCat.homOfOps {X Y : KLRWCat u ℏ P} (ops : List (StrandGenOp P))
    (h : strandGenSeqEnd X.toKLRWObject ops = Y.toKLRWObject) : X ⟶ Y :=
  (⟨(klrwRel u ℏ P).mk' (strandGenSeq S X.toKLRWObject ops),
    strandGenSeq_mem_klrwHom_of_eq _ _ _ h⟩ :
    ↥(klrwHom u ℏ X.toKLRWObject Y.toKLRWObject))

/-- The algebra element of `homOfOps ops h` is the product described by `ops`. -/
@[simp]
lemma KLRWCat.homOfOps_val {X Y : KLRWCat u ℏ P} (ops : List (StrandGenOp P))
    (h : strandGenSeqEnd X.toKLRWObject ops = Y.toKLRWObject) :
    (KLRWCat.homOfOps ops h).val = (klrwRel u ℏ P).mk' (strandGenSeq S X.toKLRWObject ops) :=
  rfl

/-- The morphism of `ops₂` followed by the morphism of `ops₁` is the morphism of
`ops₁ ++ ops₂`. -/
lemma KLRWCat.homOfOps_comp {X Y Z : KLRWCat u ℏ P} (ops₁ ops₂ : List (StrandGenOp P))
    (h₁ : strandGenSeqEnd Y.toKLRWObject ops₁ = Z.toKLRWObject)
    (h₂ : strandGenSeqEnd X.toKLRWObject ops₂ = Y.toKLRWObject) :
    KLRWCat.homOfOps ops₂ h₂ ≫ KLRWCat.homOfOps ops₁ h₁ =
      KLRWCat.homOfOps (ops₁ ++ ops₂) (by rw [strandGenSeqEnd_append, h₂, h₁]) := by
  ext
  simp only [KLRWCat.comp_val, KLRWCat.homOfOps_val]
  rw [strandGenSeq_append, h₂]

/-- The KLRW category is preadditive: the morphisms from `X` to `Y` form the additive group
`klrwHom u ℏ X.toKLRWObject Y.toKLRWObject`, and composition distributes over addition because
multiplication in the algebra does. -/
instance : Preadditive (KLRWCat u ℏ P) where
  homGroup X Y := inferInstanceAs (AddCommGroup (klrwHom u ℏ X.toKLRWObject Y.toKLRWObject))
  add_comp f g h := KLRWCat.hom_ext (mul_add h.val f.val g.val)
  comp_add f g h := KLRWCat.hom_ext (add_mul g.val h.val f.val)

/-- The KLRW category is `S`-linear: each hom-space is an `S`-module, and scalars move through
composition because the algebra is an `S`-algebra. -/
instance : Linear S (KLRWCat u ℏ P) where
  homModule X Y := inferInstanceAs (Module S (klrwHom u ℏ X.toKLRWObject Y.toKLRWObject))
  smul_comp r f g := KLRWCat.hom_ext (mul_smul_comm r g.val f.val)
  comp_smul f r g := KLRWCat.hom_ext (smul_mul_assoc r g.val f.val)

end CategoryInstances

end KLRW
