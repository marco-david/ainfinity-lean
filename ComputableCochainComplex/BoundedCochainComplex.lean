module

public import Mathlib
public import ComputableCochainComplex.AdditiveCompletion

@[expose] public section

open CategoryTheory Limits

/-!
# Bounded Cochain Complexes

A computable version of `CochainComplex` backed by an explicit `Finset ℤ`
containing the cohomological support, analogous to `CMat_` vs `Mat_`.
The stored bound may include degrees whose objects are zero, so constructing a
bounded complex does not require deciding whether an object is zero.
The compatibility constructor `of` accepts an exact-support certificate, while
`mkOfBounded` retains any supplied bound. When `IsZero` is decidable,
`withExactSupport` returns the same complex with its exact support as the stored bound.
-/

/-- A cochain complex with a finite bound on its support. Objects outside `support`
are zero; objects inside it are allowed to be zero as well. -/
structure BoundedCochainComplex (V : Type*) [Category V] [HasZeroObject V] [Preadditive V]
    extends CochainComplex V ℤ where
  support : Finset ℤ
  isZero_of_notMem_support : ∀ i : ℤ, i ∉ support → IsZero (X i)

namespace BoundedCochainComplex

variable {V : Type*} [Category V] [HasZeroObject V] [Preadditive V]

/-- Every degree with a nonzero object belongs to the stored support bound. -/
lemma mem_support_of_not_isZero (c : BoundedCochainComplex V) {i : ℤ}
    (hi : ¬ IsZero (c.X i)) : i ∈ c.support := by
  by_contra h
  exact hi (c.isZero_of_notMem_support i h)

/-- The width of the stored support bound, or zero if the bound is empty.
This depends on the supplied bound and can overestimate the width of the true support. -/
def supportWidth (c : BoundedCochainComplex V) : ℤ :=
  if h : c.support.Nonempty then c.support.max' h - c.support.min' h else 0

/-- The morphisms in `BoundedCochainComplex V` are the morphisms in `CochainComplex V ℤ`
between the underlying complexes, packaged in a one-field structure (mirroring
`CategoryTheory.InducedCategory.Hom`). -/
@[ext]
structure Hom (c₁ c₂ : BoundedCochainComplex V) where
  hom : c₁.toHomologicalComplex ⟶ c₂.toHomologicalComplex

/-- The component of a bounded cochain map in degree `i`. -/
abbrev Hom.f {c₁ c₂ : BoundedCochainComplex V} (h : Hom c₁ c₂) (i : ℤ) : c₁.X i ⟶ c₂.X i :=
  h.hom.f i

instance : Category (BoundedCochainComplex V) where
  Hom := Hom
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.hom ≫ g.hom⟩

@[simp] lemma id_hom (c : BoundedCochainComplex V) :
    (𝟙 c : Hom c c).hom = 𝟙 c.toHomologicalComplex := rfl

@[simp] lemma comp_hom {c₁ c₂ c₃ : BoundedCochainComplex V}
    (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- Construct a morphism in `BoundedCochainComplex V` from a morphism in
`CochainComplex V ℤ` between the underlying complexes. -/
@[simps] def homMk {c₁ c₂ : BoundedCochainComplex V}
    (f : c₁.toHomologicalComplex ⟶ c₂.toHomologicalComplex) : c₁ ⟶ c₂ :=
  ⟨f⟩

/-- Morphisms in `BoundedCochainComplex V` identify with morphisms in `CochainComplex V ℤ`
between the underlying complexes. -/
@[simps]
def homEquiv {c₁ c₂ : BoundedCochainComplex V} :
    (c₁ ⟶ c₂) ≃ (c₁.toHomologicalComplex ⟶ c₂.toHomologicalComplex) where
  toFun := Hom.hom
  invFun := homMk
  left_inv := fun ⟨_⟩ => rfl
  right_inv _ := rfl

/-- The forgetful functor from bounded cochain complexes to ordinary cochain complexes. -/
@[simps]
def embed : BoundedCochainComplex V ⥤ CochainComplex V ℤ where
  obj c := c.toHomologicalComplex
  map f := f.hom

/-- `embed` is fully faithful — its action on hom-sets is the identification `homEquiv`. -/
def fullyFaithfulEmbed : (embed (V := V)).FullyFaithful where
  preimage f := homMk f

instance : (embed (V := V)).Faithful :=
  fullyFaithfulEmbed.faithful

instance : (embed (V := V)).Full :=
  fullyFaithfulEmbed.full

instance : Preadditive (BoundedCochainComplex V) :=
  Preadditive.ofFullyFaithful fullyFaithfulEmbed

variable {R : Type*} [Semiring R] [Linear R V] in
instance : Linear R (BoundedCochainComplex V) where
  homModule c₁ c₂ := Equiv.module R (homEquiv (c₁ := c₁) (c₂ := c₂))
  smul_comp _ _ _ r f g := Hom.ext (Linear.smul_comp _ _ _ r f.hom g.hom)
  comp_smul _ _ _ f r g := Hom.ext (Linear.comp_smul _ _ _ f.hom r g.hom)

/-- Construct a bounded complex from its objects, consecutive differentials, and
an exact-support certificate, preserving the original constructor interface.
For a support bound that need not be exact, use `mkOfBounded`. -/
def of
    (X : ℤ → V) (support : Finset ℤ)
    (h : ∀ i : ℤ, ¬ IsZero (X i) ↔ i ∈ support)
    (d : ∀ i : ℤ, X i ⟶ X (i + 1))
    (hd : ∀ i : ℤ, d i ≫ d (i + 1) = 0) : BoundedCochainComplex V :=
  ⟨CochainComplex.of X d hd, support, fun i hi =>
    not_not.mp (fun hn => hi ((h i).mp hn))⟩

/-- Construct a map between complexes built by `of`, retaining their exact-support
certificates and the component maps commuting with the differentials. -/
def ofHom
    (X : ℤ → V) (support_X : Finset ℤ) (d_X : ∀ i : ℤ, X i ⟶ X (i + 1))
    (h_X : ∀ i : ℤ, ¬ IsZero (X i) ↔ i ∈ support_X)
    (sq_X : ∀ i : ℤ, d_X i ≫ d_X (i + 1) = 0)
    (Y : ℤ → V) (support_Y : Finset ℤ) (d_Y : ∀ i : ℤ, Y i ⟶ Y (i + 1))
    (h_Y : ∀ i : ℤ, ¬ IsZero (Y i) ↔ i ∈ support_Y)
    (sq_Y : ∀ i : ℤ, d_Y i ≫ d_Y (i + 1) = 0)
    (f : ∀ i : ℤ, X i ⟶ Y i)
    (comm : ∀ i : ℤ, f i ≫ d_Y i = d_X i ≫ f (i + 1))
    : of X support_X h_X d_X sq_X ⟶ of Y support_Y h_Y d_Y sq_Y :=
  ⟨CochainComplex.ofHom X d_X sq_X Y d_Y sq_Y f comm⟩

/-- The map constructed by `ofHom` has the prescribed components. -/
@[simp] theorem ofHom_f
    (X : ℤ → V) (support_X : Finset ℤ) (d_X : ∀ i : ℤ, X i ⟶ X (i + 1))
    (h_X : ∀ i : ℤ, ¬ IsZero (X i) ↔ i ∈ support_X)
    (sq_X : ∀ i : ℤ, d_X i ≫ d_X (i + 1) = 0)
    (Y : ℤ → V) (support_Y : Finset ℤ) (d_Y : ∀ i : ℤ, Y i ⟶ Y (i + 1))
    (h_Y : ∀ i : ℤ, ¬ IsZero (Y i) ↔ i ∈ support_Y)
    (sq_Y : ∀ i : ℤ, d_Y i ≫ d_Y (i + 1) = 0)
    (f : ∀ i : ℤ, X i ⟶ Y i)
    (comm : ∀ i : ℤ, f i ≫ d_Y i = d_X i ≫ f (i + 1)) (i : ℤ)
    : (ofHom X support_X d_X h_X sq_X Y support_Y d_Y h_Y sq_Y f comm).f i = f i :=
  CochainComplex.ofHom_f X d_X sq_X Y d_Y sq_Y f comm i

/-- Build a `BoundedCochainComplex` from a `CochainComplex` together with a finite
superset of its true support, retaining the supplied bound unchanged. -/
def mkOfBounded
    (c : CochainComplex V ℤ) {supersetOfSupport : Finset ℤ}
    (h : ∀ i : ℤ, i ∉ supersetOfSupport → IsZero (c.X i)) :
    BoundedCochainComplex V where
  toHomologicalComplex := c
  support := supersetOfSupport
  isZero_of_notMem_support := h

/-- Adding a support bound leaves the underlying complex unchanged. -/
@[simp] lemma mkOfBounded_toHomologicalComplex
    (c : CochainComplex V ℤ) {s : Finset ℤ}
    (h : ∀ i : ℤ, i ∉ s → IsZero (c.X i)) :
    (mkOfBounded c h).toHomologicalComplex = c := rfl

/-- `mkOfBounded` stores exactly the supplied bound. -/
@[simp] lemma mkOfBounded_support
    (c : CochainComplex V ℤ) {s : Finset ℤ}
    (h : ∀ i : ℤ, i ∉ s → IsZero (c.X i)) :
    (mkOfBounded c h).support = s := rfl

/-- Different support bounds on the same complex give canonically isomorphic
bounded complexes, although their stored bounds need not be equal. -/
def mkOfBoundedIso (c : CochainComplex V ℤ)
    {s₁ s₂ : Finset ℤ}
    (h₁ : ∀ i : ℤ, i ∉ s₁ → IsZero (c.X i))
    (h₂ : ∀ i : ℤ, i ∉ s₂ → IsZero (c.X i)) :
    mkOfBounded c h₁ ≅ mkOfBounded c h₂ :=
  fullyFaithfulEmbed.preimageIso (Iso.refl c)

section ExactSupport

variable [DecidablePred (IsZero : V → Prop)]

/-- Replace the stored bound by exact support by discarding degrees with zero objects.
The underlying complex is unchanged; computing the exact support requires a zero test. -/
def withExactSupport (c : BoundedCochainComplex V) : BoundedCochainComplex V where
  toHomologicalComplex := c.toHomologicalComplex
  support := c.support.filter (fun i => ¬ IsZero (c.X i))
  isZero_of_notMem_support i hi := by
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨c.mem_support_of_not_isZero h, h⟩)

/-- Replacing the bound by exact support preserves the underlying complex. -/
@[simp] lemma withExactSupport_toHomologicalComplex (c : BoundedCochainComplex V) :
    c.withExactSupport.toHomologicalComplex = c.toHomologicalComplex := rfl

/-- The exact support is obtained by filtering the supplied bound. -/
lemma withExactSupport_support (c : BoundedCochainComplex V) :
    c.withExactSupport.support = c.support.filter (fun i => ¬ IsZero (c.X i)) := rfl

/-- A degree belongs to the exact support exactly when its object is nonzero. -/
@[simp] lemma mem_withExactSupport_support (c : BoundedCochainComplex V) (i : ℤ) :
    i ∈ c.withExactSupport.support ↔ ¬ IsZero (c.X i) := by
  rw [withExactSupport_support, Finset.mem_filter]
  exact ⟨And.right, fun hi => ⟨c.mem_support_of_not_isZero hi, hi⟩⟩

/-- Replacing an already exact support bound leaves the bounded complex unchanged. -/
lemma withExactSupport_eq_self (c : BoundedCochainComplex V)
    (h : ∀ i : ℤ, ¬ IsZero (c.X i) ↔ i ∈ c.support) : c.withExactSupport = c := by
  cases c
  simp only [withExactSupport, mk.injEq, true_and]
  exact Finset.filter_eq_self.mpr fun i hi => (h i).mpr hi

/-- Replacing the bound by exact support twice is the same as doing so once. -/
@[simp] lemma withExactSupport_idem (c : BoundedCochainComplex V) :
    c.withExactSupport.withExactSupport = c.withExactSupport := by
  apply withExactSupport_eq_self
  intro i
  exact (mem_withExactSupport_support c i).symm

/-- Replacing different bounds on the same complex by exact support gives equal objects. -/
lemma withExactSupport_mkOfBounded_eq (c : CochainComplex V ℤ) {s₁ s₂ : Finset ℤ}
    (h₁ : ∀ i : ℤ, i ∉ s₁ → IsZero (c.X i))
    (h₂ : ∀ i : ℤ, i ∉ s₂ → IsZero (c.X i)) :
    (mkOfBounded c h₁).withExactSupport = (mkOfBounded c h₂).withExactSupport := by
  suffices hs : (mkOfBounded c h₁).withExactSupport.support =
      (mkOfBounded c h₂).withExactSupport.support by
    simpa only [withExactSupport, mkOfBounded, mk.injEq, true_and] using hs
  ext i
  simp only [mem_withExactSupport_support, mkOfBounded_toHomologicalComplex]

/-- The complex with exact support is isomorphic to the original via the identity. -/
def withExactSupportIso (c : BoundedCochainComplex V) : c.withExactSupport ≅ c :=
  fullyFaithfulEmbed.preimageIso (Iso.refl c.toHomologicalComplex)

end ExactSupport

section LiftEndofunctor

/-- Lift an endofunctor `H : CochainComplex V ℤ ⥤ CochainComplex V ℤ` to a functor
`BoundedCochainComplex V ⥤ BoundedCochainComplex V`, given a Finset-valued bound
`b : BoundedCochainComplex V → Finset ℤ` such that for every `X`, the support of
`H.obj (embed.obj X)` is contained in `b X`. -/
@[simps]
def liftEndofunctor
    (H : CochainComplex V ℤ ⥤ CochainComplex V ℤ)
    (b : BoundedCochainComplex V → Finset ℤ)
    (hb : ∀ (X : BoundedCochainComplex V) (i : ℤ),
            i ∉ b X → IsZero ((H.obj (embed.obj X)).X i)) :
    BoundedCochainComplex V ⥤ BoundedCochainComplex V where
  obj X := mkOfBounded (H.obj (embed.obj X)) (hb X)
  map {_ _} f := homMk (H.map f.hom)
  map_id X := Hom.ext (by simp [embed])
  map_comp f g := Hom.ext (by simp [embed])

/-- The lifted functor commutes with the embedding to `CochainComplex V ℤ`. -/
@[simps!]
def liftEndofunctorCompEmbed
    (H : CochainComplex V ℤ ⥤ CochainComplex V ℤ)
    (b : BoundedCochainComplex V → Finset ℤ)
    (hb : ∀ (X : BoundedCochainComplex V) (i : ℤ),
            i ∉ b X → IsZero ((H.obj (embed.obj X)).X i)) :
    liftEndofunctor H b hb ⋙ embed ≅ embed ⋙ H :=
  Iso.refl _

end LiftEndofunctor

/-- Shift a bounded cochain complex by `n`, translating its stored support bound by `-n`. -/
def shiftFunctor (n : ℤ) :
    BoundedCochainComplex V ⥤ BoundedCochainComplex V :=
  liftEndofunctor (CochainComplex.shiftFunctor V n) (fun A ↦ A.support.image (· - n)) <| by
    intro X i hi
    change IsZero (X.X (i + n))
    apply X.isZero_of_notMem_support
    intro h
    exact hi (Finset.mem_image.mpr ⟨i + n, h, add_sub_cancel_right i n⟩)

/-- Render the objects and differentials in an interval, including any zero objects
inside the stored support bound. -/
def toTexRow {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
    [Texify C] [∀ (X Y : C), Texify (X ⟶ Y)] (A : BoundedCochainComplex C)
    (leftmost rightmost : ℤ) (placeDifferentialsBelow : Bool := false) : String := Id.run do
    let mut res := ""
    for i in leftmost...rightmost do
      if placeDifferentialsBelow then
        res := res ++ s!"{texifyWithBrackets (A.X i)} @>>{texifyWithBrackets (A.d i (i + 1))}>"
      else
        res := res ++ s!"{texifyWithBrackets (A.X i)} @>{texifyWithBrackets (A.d i (i + 1))}>>"
    res := res ++ s!"{texifyWithBrackets (A.X rightmost)}"
    return res

/-- Render the components of a bounded cochain map over an interval. -/
def Hom.toTexRow {C : Type*} [Category C] [Preadditive C]
    [Limits.HasZeroObject C] [Texify C] [∀ (X Y : C), Texify (X ⟶ Y)]
    {A B : BoundedCochainComplex C}
    (h : A ⟶ B) (leftmost rightmost : ℤ) : String := Id.run do
    let mut res := ""
    for i in leftmost...=rightmost do
      res := res ++ s!"@V{texifyWithBrackets (h.f i)}VV"
    return res

instance (C : Type*) [Category C] [Preadditive C] [Limits.HasZeroObject C] [Texify C]
  [∀ (X Y : C), Texify (X ⟶ Y)] : Texify (BoundedCochainComplex C) where
  texify A := Id.run do
    let (leftmost, rightmost) := if h : A.support.Nonempty then
      (A.support.min' h - 1, A.support.max' h + 1)
    else (-1, 1)
    return r"\begin{CD}" ++ A.toTexRow leftmost rightmost ++ r"\end{CD}"
  requiresParentheses := true

instance (C : Type*) [Category C] [Preadditive C] [Limits.HasZeroObject C] [Texify C]
  [∀ (X Y : C), Texify (X ⟶ Y)] (A B : BoundedCochainComplex C) : Texify (A ⟶ B) where
  texify h := Id.run do
    let (leftmostA, rightmostA) := if h : A.support.Nonempty then
      (A.support.min' h - 1, A.support.max' h + 1)
    else (-1, 1)
    let (leftmostB, rightmostB) := if h : B.support.Nonempty then
      (B.support.min' h - 1, B.support.max' h + 1)
    else (-1, 1)
    let leftmost := min leftmostA leftmostB
    let rightmost := max rightmostA rightmostB
    return r"\begin{CD}" ++ A.toTexRow leftmost rightmost ++ r"\\" ++ h.toTexRow leftmost rightmost
      ++ r"\\" ++ B.toTexRow leftmost rightmost true ++ r"\end{CD}"
  requiresParentheses := true

end BoundedCochainComplex
