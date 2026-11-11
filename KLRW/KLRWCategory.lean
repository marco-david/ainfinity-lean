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

* `KLRW.KLRWObject.WithRing u ℏ P`: KLRW objects tagged with the coefficient ring `S` and the
  parameters `u ℏ : S`; this is the type that carries the category structure.
* The `Category`, `Preadditive` and `Linear S` instances on `KLRWObject.WithRing u ℏ P`.

## Main results

* `KLRW.mul_mem_klrwHom`: morphisms compose.
* `KLRW.mem_klrwHom_iff`: `f` is a morphism from `X` to `Y` exactly when `e_Y * f * e_X = f`.
* `KLRW.generator_mem_klrwHom`: every generator is a morphism from its domain to its codomain.
* `KLRW.strandGenSeq_mem_klrwHom`: the product described by a list of operations is a
  morphism from its starting object to its end object.
* `KLRW.strandGenSeq_append`: the product for `ops₁ ++ ops₂` is the composite of the products
  for `ops₂` and `ops₁`.

## Implementation notes

* `f ≫ g` (first `f`, then `g`) is the product `g * f` in the algebra.
-/

@[expose] public section

namespace KLRW
open CategoryTheory FreeAlgebra

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {P : KLRWStructure V}
variable {S : Type*} [CommRing S] {u ℏ : S}

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
lemma mk'_eq_of_klrwRel {X Y : KLRWFreeAlg S P} (h : klrwRel u ℏ P X Y) :
    (klrwRel u ℏ P).mk' X = (klrwRel u ℏ P).mk' Y :=
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

section Idempotents

/-- The idempotent of the codomain is a left identity for a generator. -/
lemma idemMorph_mul_generator (f : StrandGenerator P) :
    idemMorph u ℏ f.codomain * (klrwRel u ℏ P).mk' (ι _ f) = (klrwRel u ℏ P).mk' (ι _ f) :=
  mk'_eq_of_implicit (KLRWImplicitConRel.idem_left f.codomain f rfl)

/-- The idempotent of the domain is a right identity for a generator. -/
lemma generator_mul_idemMorph (f : StrandGenerator P) :
    (klrwRel u ℏ P).mk' (ι _ f) * idemMorph u ℏ f.domain = (klrwRel u ℏ P).mk' (ι _ f) :=
  mk'_eq_of_implicit (KLRWImplicitConRel.idem_right f.domain f rfl)

/-- The idempotent `e_X` is idempotent. -/
lemma idemMorph_mul_idemMorph {X : KLRWObject P} :
    idemMorph u ℏ X * idemMorph u ℏ X = idemMorph u ℏ X :=
  idemMorph_mul_generator (.idem X)

end Idempotents

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
    rw [← mul_assoc (idemMorph u ℏ Y), idemMorph_mul_idemMorph, mul_assoc, mul_assoc,
      idemMorph_mul_idemMorph]
  · intro h
    exact ⟨f, by rw [← mul_assoc, h]⟩

/-- The idempotent of the codomain is a left identity for any morphism. -/
lemma idemMorph_mul_of_mem (f : KLRWAlg u ℏ P) (hf : f ∈ klrwHom u ℏ X Y) :
    idemMorph u ℏ Y * f = f := by
  obtain ⟨a, ha⟩ := hf
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply] at ha
  rw [← ha, ← mul_assoc, idemMorph_mul_idemMorph]

/-- The idempotent of the domain is a right identity for any morphism. -/
lemma mul_idemMorph_of_mem (f : KLRWAlg u ℏ P) (hf : f ∈ klrwHom u ℏ X Y) :
    f * idemMorph u ℏ X = f := by
  obtain ⟨a, ha⟩ := hf
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply] at ha
  rw [← ha, ← mul_assoc, mul_assoc, idemMorph_mul_idemMorph]

/-- Morphisms compose: if `f : X ⟶ Y` and `g : Y ⟶ Z`, then `g * f : X ⟶ Z`. -/
lemma mul_mem_klrwHom {f g : KLRWAlg u ℏ P} (hf : f ∈ klrwHom u ℏ X Y)
    (hg : g ∈ klrwHom u ℏ Y Z) : g * f ∈ klrwHom u ℏ X Z := by
  rw [mem_klrwHom_iff, mul_assoc, mul_assoc, mul_idemMorph_of_mem f hf]
  rw [← mul_assoc, idemMorph_mul_of_mem g hg]

/-- The idempotent of `X` is a morphism from `X` to `X`. -/
lemma idemMorph_mem_klrwHom : idemMorph u ℏ X ∈ klrwHom u ℏ X X := by
  rw [mem_klrwHom_iff, idemMorph_mul_idemMorph, idemMorph_mul_idemMorph]

/-- A generator is a morphism from its domain to its codomain. -/
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
    (klrwRel u ℏ P).mk' (strandGenSeq M ops) ∈ klrwHom u ℏ M (strandGenSeqEnd M ops) := by
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
    (klrwRel u ℏ P).mk' (strandGenSeq M ops) ∈ klrwHom u ℏ M N := by
  rw [← h]
  exact strandGenSeq_mem_klrwHom M ops

/-- The idempotent of the end object is a left identity for a strand generator sequence. -/
lemma idemMorph_mul_strandGenSeq : idemMorph u ℏ (strandGenSeqEnd M ops) *
    (klrwRel u ℏ P).mk' (strandGenSeq (S := S) M ops) =
    (klrwRel u ℏ P).mk' (strandGenSeq (S := S) M ops) :=
  idemMorph_mul_of_mem _ (strandGenSeq_mem_klrwHom M ops)

/-- The idempotent of the start object is a right identity for a strand generator sequence. -/
lemma strandGenSeq_mul_idemMorph :
    (klrwRel u ℏ P).mk' (strandGenSeq (S := S) M ops) * idemMorph u ℏ M =
    (klrwRel u ℏ P).mk' (strandGenSeq (S := S) M ops) :=
  mul_idemMorph_of_mem _ (strandGenSeq_mem_klrwHom M ops)

/-- The sequence for `ops₁ ++ ops₂` is the sequence for `ops₂` followed by the sequence for
`ops₁`, started where `ops₂` ends. -/
lemma strandGenSeq_append (ops₁ ops₂ : List (StrandGenOp P)) :
    (klrwRel u ℏ P).mk' (strandGenSeq M (ops₁ ++ ops₂)) =
      (klrwRel u ℏ P).mk'
        (strandGenSeq (strandGenSeqEnd M ops₂) ops₁ * strandGenSeq (S := S) M ops₂) := by
  induction ops₁ with
  | nil =>
      simp only [List.nil_append, strandGenSeq]
      symm
      exact idemMorph_mul_strandGenSeq (S := S) M ops₂
  | cons op ops₁ ih =>
      rw [List.cons_append, strandGenSeq_cons, map_mul, ih, strandGenSeq_cons]
      simp [strandGenSeqEnd_append, mul_assoc]

end StrandGenSeqLemmas

/-! ## The category structure -/

/-- KLRW objects tagged with the coefficient ring `S` and the parameters `u`, `ℏ`, so that the
category structure knows which KLRW algebra its morphisms live in. -/
structure KLRWObject.WithRing (u ℏ : S) (P : KLRWStructure V) where
  /-- The underlying KLRW object. -/
  obj : KLRWObject P

/-- The KLRW category: morphisms from `X` to `Y` are the elements of `klrwHom u ℏ X.obj Y.obj`,
and `f ≫ g` (first `f`, then `g`) is the product `g * f`. -/
instance : Category (KLRWObject.WithRing u ℏ P) where
  Hom X Y := ↥(klrwHom u ℏ X.obj Y.obj)
  id X := ⟨idemMorph u ℏ X.obj, idemMorph_mem_klrwHom⟩
  comp f g := ⟨g.val * f.val, mul_mem_klrwHom f.property g.property⟩
  id_comp f := by ext; exact mul_idemMorph_of_mem f.val f.property
  comp_id f := by ext; exact idemMorph_mul_of_mem f.val f.property
  assoc f g h := by ext; simp [mul_assoc]

/-- Two morphisms of the KLRW category are equal if their underlying algebra elements are. -/
@[ext]
lemma KLRWObject.WithRing.hom_ext {X Y : KLRWObject.WithRing u ℏ P} {f g : X ⟶ Y}
    (h : f.val = g.val) : f = g :=
  Subtype.ext h

/-- The algebra element of a composite: `f ≫ g` is `g * f`. -/
@[simp]
lemma KLRWObject.WithRing.comp_val {X Y Z : KLRWObject.WithRing u ℏ P} (f : X ⟶ Y)
    (g : Y ⟶ Z) : (f ≫ g).val = g.val * f.val := rfl

/-- The algebra element of the identity of `X` is the idempotent `e_X`. -/
@[simp]
lemma KLRWObject.WithRing.id_val (X : KLRWObject.WithRing u ℏ P) :
    (𝟙 X : X ⟶ X).val = idemMorph u ℏ X.obj := rfl

/-- The KLRW category is preadditive: the morphisms from `X` to `Y` form the additive group
`klrwHom u ℏ X.obj Y.obj`, and composition distributes over addition because multiplication
in the algebra does. -/
noncomputable instance : Preadditive (KLRWObject.WithRing u ℏ P) where
  homGroup X Y := inferInstanceAs (AddCommGroup (klrwHom u ℏ X.obj Y.obj))
  add_comp X Y Z f g h := by
    ext
    change h.val * (f.val + g.val) = h.val * f.val + h.val * g.val
    exact mul_add h.val f.val g.val
  comp_add X Y Z f g h := by
    ext
    change (g.val + h.val) * f.val = g.val * f.val + h.val * f.val
    exact add_mul g.val h.val f.val

/-- The KLRW category is `S`-linear: each `klrwHom u ℏ X.obj Y.obj` is an `S`-module, and
scalars move through composition because the algebra is an `S`-algebra. -/
noncomputable instance : Linear S (KLRWObject.WithRing u ℏ P) where
  homModule X Y := inferInstanceAs (Module S (klrwHom u ℏ X.obj Y.obj))
  smul_comp X Y Z r f g := by
    ext
    change g.val * (r • f.val) = r • (g.val * f.val)
    exact mul_smul_comm r g.val f.val
  comp_smul X Y Z f r g := by
    ext
    change (r • g.val) * f.val = r • (g.val * f.val)
    exact smul_mul_assoc r g.val f.val

end KLRW
