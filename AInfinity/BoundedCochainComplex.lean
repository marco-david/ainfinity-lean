module

public import Mathlib
public import AInfinity.AdditiveCompletion

@[expose] public section

open CategoryTheory Limits

/-!
# Bounded Cochain Complexes

A computable version of `CochainComplex` backed by an explicit `Finset ℤ`
of cohomological degrees in the support, analogous to `CMat_` vs `Mat_`.
-/


structure BoundedCochainComplex (V : Type*) [Category V] [HasZeroObject V] [Preadditive V]
    extends CochainComplex V ℤ where
  support : Finset ℤ
  not_isZero_iff_mem_support : ∀ i : ℤ, ¬ IsZero (X i) ↔ i ∈ support

namespace BoundedCochainComplex

variable {V : Type*} [Category V] [HasZeroObject V] [Preadditive V]

def length (c : BoundedCochainComplex V) : ℤ :=
  if h : c.support.Nonempty then c.support.max' h - c.support.min' h else 0

/-- The morphisms in `BoundedCochainComplex V` are the morphisms in `CochainComplex V ℤ`
between the underlying complexes, packaged in a one-field structure (mirroring
`CategoryTheory.InducedCategory.Hom`). -/
@[ext]
structure Hom (c₁ c₂ : BoundedCochainComplex V) where
  hom : c₁.toHomologicalComplex ⟶ c₂.toHomologicalComplex

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

def of [DecidablePred (IsZero : V → Prop)]
    (X : ℤ → V) (support : Finset ℤ)
    (h : ∀ i : ℤ, ¬ IsZero (X i) ↔ i ∈ support)
    (d : ∀ i : ℤ, X i ⟶ X (i + 1))
    (hd : ∀ i : ℤ, d i ≫ d (i + 1) = 0) : BoundedCochainComplex V :=
  ⟨CochainComplex.of X d hd, support, h⟩

def ofHom [DecidablePred (IsZero : V → Prop)]
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

/-- Build a `BoundedCochainComplex` from a `CochainComplex` together with a finite
superset of its true support. -/
def mkOfBounded
    [DecidablePred (IsZero : V → Prop)]
    (c : CochainComplex V ℤ) {supersetOfSupport : Finset ℤ}
    (h : ∀ i : ℤ, ¬ IsZero (c.X i) → i ∈ supersetOfSupport) :
    BoundedCochainComplex V where
  toHomologicalComplex := c
  support := {i ∈ supersetOfSupport | ¬ IsZero (c.X i)}
  not_isZero_iff_mem_support i := by
    simp only [Finset.mem_filter]
    refine ⟨fun hi => ⟨h i hi, hi⟩, fun ⟨_, hi⟩ => hi⟩

@[simp] lemma mkOfBounded_toHomologicalComplex
    [DecidablePred (IsZero : V → Prop)]
    (c : CochainComplex V ℤ) {s : Finset ℤ}
    (h : ∀ i : ℤ, ¬ IsZero (c.X i) → i ∈ s) :
    (mkOfBounded c h).toHomologicalComplex = c := rfl

theorem mkOfBounded_eq
    [DecidablePred (IsZero : V → Prop)] (c : CochainComplex V ℤ)
    {s₁ s₂ : Finset ℤ}
    (h₁ : ∀ i : ℤ, ¬ IsZero (c.X i) → i ∈ s₁)
    (h₂ : ∀ i : ℤ, ¬ IsZero (c.X i) → i ∈ s₂) :
    mkOfBounded c h₁ = mkOfBounded c h₂ := by
  have hsupp : ({i ∈ s₁ | ¬ IsZero (c.X i)} : Finset ℤ) = {i ∈ s₂ | ¬ IsZero (c.X i)} := by
    ext i
    simp only [Finset.mem_filter]
    refine ⟨fun ⟨_, hi⟩ => ⟨h₂ i hi, hi⟩, fun ⟨_, hi⟩ => ⟨h₁ i hi, hi⟩⟩
  unfold mkOfBounded
  congr! 1

section LiftEndofunctor

variable [DecidablePred (IsZero : V → Prop)]

/-- Lift an endofunctor `H : CochainComplex V ℤ ⥤ CochainComplex V ℤ` to a functor
`BoundedCochainComplex V ⥤ BoundedCochainComplex V`, given a Finset-valued bound
`b : BoundedCochainComplex V → Finset ℤ` such that for every `X`, the support of
`H.obj (embed.obj X)` is contained in `b X`. -/
@[simps]
def liftEndofunctor
    (H : CochainComplex V ℤ ⥤ CochainComplex V ℤ)
    (b : BoundedCochainComplex V → Finset ℤ)
    (hb : ∀ (X : BoundedCochainComplex V) (i : ℤ),
            ¬ IsZero ((H.obj (embed.obj X)).X i) → i ∈ b X) :
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
            ¬ IsZero ((H.obj (embed.obj X)).X i) → i ∈ b X) :
    liftEndofunctor H b hb ⋙ embed ≅ embed ⋙ H :=
  Iso.refl _

end LiftEndofunctor

end BoundedCochainComplex
