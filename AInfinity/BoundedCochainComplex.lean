module

public import Mathlib
public import AInfinity.AdditiveCompletion
public import AInfinity.AInfinityCategory

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

theorem ofHom_f [DecidablePred (IsZero : V → Prop)]
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

def shiftFunctor [DecidablePred (IsZero : V → Prop)] (n : ℤ) :
    BoundedCochainComplex V ⥤ BoundedCochainComplex V :=
  liftEndofunctor (CochainComplex.shiftFunctor V n) (fun A ↦ A.support.image (· - n)) <| by
    intro X i hi
    rw [Finset.mem_image]
    refine ⟨i + n, ?_, by abel⟩
    exact (X.not_isZero_iff_mem_support (i + n)).mp (by simpa using hi)

section FinCochainSection

/-- The finset of source degrees p where a degree-n cochain A → B can be nonzero:
those p in A's support whose target degree p + n lies in B's support. -/
def activePairs (A B : BoundedCochainComplex V) (n : ℤ) : Finset ℤ :=
  A.support.filter fun p => p + n ∈ B.support

namespace activePairs

variable {A B : BoundedCochainComplex V} {n : ℤ} {p : ℤ}

@[simp] lemma mem_iff : p ∈ activePairs A B n ↔ p ∈ A.support ∧ p + n ∈ B.support :=
  Finset.mem_filter

lemma mem_left (h : p ∈ activePairs A B n) : p ∈ A.support := (mem_iff.mp h).1

lemma mem_right (h : p ∈ activePairs A B n) : p + n ∈ B.support := (mem_iff.mp h).2

end activePairs

/-- A computable cochain of degree n from A to B: a morphism `A.X p ⟶ B.X (p + n)`
for each active source degree p (i.e. p ∈ A.support with p + n ∈ B.support).
Outside the active pairs both source and target are zero objects, so the morphism
is uniquely zero and carries no data. -/
abbrev FinCochain (A B : BoundedCochainComplex V) (n : ℤ) : Type _ :=
  ∀ p : {p : ℤ // p ∈ activePairs A B n}, A.X ↑p ⟶ B.X (↑p + n)

namespace FinCochain

variable {A B : BoundedCochainComplex V} {n : ℤ}

instance instAddCommGroup : AddCommGroup (FinCochain A B n) := inferInstance

variable {R : Type*} [CommRing R] [Linear R V] in
instance instModule : Module R (FinCochain A B n) := inferInstance

/-- Access the component of a FinCochain at an active source degree. -/
def v (z : FinCochain A B n) {p : ℤ} (hp : p ∈ activePairs A B n) : A.X p ⟶ B.X (p + n) :=
  z ⟨p, hp⟩

@[simp] lemma v_add (z w : FinCochain A B n) {p : ℤ} (hp : p ∈ activePairs A B n) :
    (z + w).v hp = z.v hp + w.v hp := rfl

@[simp] lemma v_zero {p : ℤ} (hp : p ∈ activePairs A B n) :
    (0 : FinCochain A B n).v hp = 0 := rfl

@[simp] lemma v_neg (z : FinCochain A B n) {p : ℤ} (hp : p ∈ activePairs A B n) :
    (-z).v hp = -z.v hp := rfl

variable {R : Type*} [CommRing R] [Linear R V] in
@[simp] lemma v_smul (r : R) (z : FinCochain A B n) {p : ℤ} (hp : p ∈ activePairs A B n) :
    (r • z).v hp = r • z.v hp := rfl

/-- Retrieve a component, returning zero when p is outside the active support. -/
def getV (z : FinCochain A B n) (p : ℤ) : A.X p ⟶ B.X (p + n) :=
  if hp : p ∈ activePairs A B n then z.v hp else 0

@[simp] lemma getV_of_mem (z : FinCochain A B n) {p : ℤ} (hp : p ∈ activePairs A B n) :
    z.getV p = z.v hp := dif_pos hp

@[simp] lemma getV_of_not_mem (z : FinCochain A B n) {p : ℤ} (hp : p ∉ activePairs A B n) :
    z.getV p = 0 := dif_neg hp

lemma getV_add (z w : FinCochain A B n) (p : ℤ) :
    (z + w).getV p = z.getV p + w.getV p := by
  simp only [getV]
  split_ifs with h <;> simp [v_add]

lemma getV_zero (p : ℤ) : (0 : FinCochain A B n).getV p = 0 := by
  simp [getV]

variable {R : Type*} [CommRing R] [Linear R V] in
lemma getV_smul (r : R) (z : FinCochain A B n) (p : ℤ) :
    (r • z).getV p = r • z.getV p := by
  simp only [getV]
  split_ifs with h <;> simp [v_smul]

/-- The differential on `FinCochain`, raising the degree by 1. Matches the formula
of `CochainComplex.HomComplex.δ` restricted to active pairs:
  `(δ_fin z).v ⟨p,_⟩ = z.getV p ≫ B.d (p+n) (p+(n+1)) + (n+1).negOnePow • (A.d p (p+1) ≫ z.getV (p+1))`
The `eqToHom` accounts for `(p+1)+n = p+(n+1)`. -/
def δ_fin {n : ℤ} (z : FinCochain A B n) : FinCochain A B (n + 1) :=
  fun ⟨p, _⟩ =>
    z.getV p ≫ B.d (p + n) (p + (n + 1)) +
    (n + 1).negOnePow • (A.d p (p + 1) ≫ z.getV (p + 1) ≫
      eqToHom (congr_arg B.X (show (p + 1) + n = p + (n + 1) from by ring)))

lemma δ_fin_add {n : ℤ} (z w : FinCochain A B n) :
    δ_fin (z + w) = δ_fin z + δ_fin w := by
  funext ⟨p, _⟩
  simp only [δ_fin, Pi.add_apply, getV_add, Preadditive.add_comp, Preadditive.comp_add,
    smul_add]
  abel

variable {R : Type*} [CommRing R] [Linear R V] in
lemma δ_fin_smul {n : ℤ} (r : R) (z : FinCochain A B n) :
    δ_fin (r • z) = r • δ_fin z := by
  funext ⟨p, _⟩
  simp only [δ_fin, Pi.smul_apply, getV_smul, Linear.comp_smul, Linear.smul_comp, smul_add,
    smul_comm r]

/-- The differential as an `R`-linear map. -/
def δ_finLinear {R : Type*} [CommRing R] [Linear R V] (A B : BoundedCochainComplex V)
    (n : ℤ) : FinCochain A B n →ₗ[R] FinCochain A B (n + 1) where
  toFun := δ_fin
  map_add' := δ_fin_add
  map_smul' := δ_fin_smul

-- Step 4: δ_fin ∘ δ_fin = 0
-- Step 5: FinCochain A B n ≃ Cochain A.toHC B.toHC n

private lemma isZero_X_of_not_mem {C : BoundedCochainComplex V} {p : ℤ} (hp : p ∉ C.support) :
    IsZero (C.X p) := by
  have h := (C.not_isZero_iff_mem_support p).not
  simp only [not_not] at h
  exact h.mpr hp

/-- `eqToHom (congr_arg C.X h) ≫ C.d b c = C.d a c` when `h : a = b`. -/
@[simp] private lemma eqToHom_d_comp {C : BoundedCochainComplex V} {a b c : ℤ} {h : a = b} :
    eqToHom (congr_arg C.X h) ≫ C.d b c = C.d a c := by subst h; simp

/-- `C.d a b ≫ eqToHom (congr_arg C.X h) = C.d a c` when `h : b = c`. -/
@[simp] private lemma d_comp_eqToHom {C : BoundedCochainComplex V} {a b c : ℤ} {h : b = c} :
    C.d a b ≫ eqToHom (congr_arg C.X h) = C.d a c := by subst h; simp

/-- `δ_fin z` extends the formula to all `p : ℤ` via `getV`, returning 0 off-support. -/
lemma getV_δ_fin {n : ℤ} (z : FinCochain A B n) (p : ℤ) :
    (δ_fin z).getV p =
      z.getV p ≫ B.d (p + n) (p + (n + 1)) +
      (n + 1).negOnePow • (A.d p (p + 1) ≫ z.getV (p + 1) ≫
        eqToHom (congr_arg B.X (show (p + 1) + n = p + (n + 1) from by ring))) := by
  by_cases h : p ∈ activePairs A B (n + 1)
  · simp only [getV_of_mem _ h, v, δ_fin]
  · rw [getV_of_not_mem _ h]
    symm
    by_cases hA : p ∈ A.support
    · have hB : p + (n + 1) ∉ B.support :=
        fun hB => h (activePairs.mem_iff.mpr ⟨hA, hB⟩)
      have hZ := isZero_X_of_not_mem hB
      have h1 : B.d (p + n) (p + (n + 1)) = 0 := hZ.eq_of_tgt _ 0
      have h2 : z.getV (p + 1) ≫
          eqToHom (congr_arg B.X (show (p + 1) + n = p + (n + 1) from by ring)) = 0 :=
        hZ.eq_of_tgt _ 0
      simp [h1, h2]
    · have hZ := isZero_X_of_not_mem hA
      have h1 : z.getV p = 0 := hZ.eq_of_src _ 0
      have h2 : A.d p (p + 1) = 0 := hZ.eq_of_src _ 0
      simp [h1, h2]

/-- The square of `δ_fin` is zero: `δ_fin (δ_fin z) = 0`. -/
lemma δ_fin_δ_fin {n : ℤ} (z : FinCochain A B n) : δ_fin (δ_fin z) = 0 := by
  funext ⟨p, _⟩
  simp only [δ_fin, Pi.zero_apply, getV_δ_fin, Preadditive.add_comp, Preadditive.comp_add,
    Preadditive.neg_comp, Preadditive.comp_neg,
    Category.assoc, smul_add, Linear.units_smul_comp, Linear.comp_units_smul,
    HomologicalComplex.d_comp_d, HomologicalComplex.d_comp_d_assoc,
    comp_zero, zero_comp, smul_zero, zero_add, Int.negOnePow_succ, Units.neg_smul]
  rw [eqToHom_d_comp, d_comp_eqToHom]
  · simp only [Units.smul_def, neg_zero, smul_zero]; abel
  · ring
  · ring

/-- The degree-`0` `FinCochain` underlying a morphism of bounded cochain complexes.
The `eqToHom` accounts for `p = p + 0`. -/
def ofHom {A B : BoundedCochainComplex V} (h : A ⟶ B) : FinCochain A B 0 :=
  fun ⟨p, _⟩ => h.f p ≫ eqToHom (congr_arg B.X (add_zero p).symm)

/-- Composition of `FinCochain`s at degree n₁ and n₂, producing degree n₁+n₂.
The `eqToHom` accounts for `(p + n₁) + n₂ = p + (n₁ + n₂)`. -/
def comp {A B C : BoundedCochainComplex V} {n₁ n₂ : ℤ}
    (f : FinCochain A B n₁) (g : FinCochain B C n₂) : FinCochain A C (n₁ + n₂) :=
  fun ⟨p, _⟩ => f.getV p ≫ g.getV (p + n₁) ≫
    eqToHom (congr_arg C.X (show (p + n₁) + n₂ = p + (n₁ + n₂) from by ring))

lemma comp_add_left {A B C : BoundedCochainComplex V} {n₁ n₂ : ℤ}
    (f g : FinCochain A B n₁) (h : FinCochain B C n₂) :
    (f + g).comp h = f.comp h + g.comp h := by
  funext ⟨p, _⟩
  simp only [comp, Pi.add_apply, getV_add, Preadditive.add_comp]

lemma comp_add_right {A B C : BoundedCochainComplex V} {n₁ n₂ : ℤ}
    (f : FinCochain A B n₁) (g h : FinCochain B C n₂) :
    f.comp (g + h) = f.comp g + f.comp h := by
  funext ⟨p, _⟩
  simp only [comp, Pi.add_apply, getV_add, Preadditive.add_comp, Preadditive.comp_add]

variable {R : Type*} [CommRing R] [Linear R V] in
lemma comp_smul_left {A B C : BoundedCochainComplex V} {n₁ n₂ : ℤ}
    (r : R) (f : FinCochain A B n₁) (g : FinCochain B C n₂) :
    (r • f).comp g = r • f.comp g := by
  funext ⟨p, _⟩
  simp only [comp, Pi.smul_apply, getV_smul, Linear.smul_comp]

variable {R : Type*} [CommRing R] [Linear R V] in
lemma comp_smul_right {A B C : BoundedCochainComplex V} {n₁ n₂ : ℤ}
    (r : R) (f : FinCochain A B n₁) (g : FinCochain B C n₂) :
    f.comp (r • g) = r • f.comp g := by
  funext ⟨p, _⟩
  simp only [comp, Pi.smul_apply, getV_smul, Linear.smul_comp, Linear.comp_smul]

/-- Composition with a degree-`0` cochain on the left, with the target degree
already in normal form (`0 + m` is definitionally but not syntactically `m`). -/
def zeroComp {A B C : BoundedCochainComplex V} {m : ℤ}
    (f : FinCochain A B 0) (g : FinCochain B C m) : FinCochain A C m :=
  fun ⟨p, _⟩ => f.getV p ≫ g.getV (p + 0) ≫
    eqToHom (congr_arg C.X (show (p + 0) + m = p + m from by ring))

/-- Composition with a degree-`0` cochain on the right, with the target degree
already in normal form (`m + 0` is definitionally but not syntactically `m`). -/
def compZero {A B C : BoundedCochainComplex V} {m : ℤ}
    (f : FinCochain A B m) (g : FinCochain B C 0) : FinCochain A C m :=
  fun ⟨p, _⟩ => f.getV p ≫ g.getV (p + m) ≫
    eqToHom (congr_arg C.X (show (p + m) + 0 = p + m from by ring))

section ToCochainEquiv

open CochainComplex.HomComplex

variable {R : Type*} [CommRing R] [Linear R V]

/-- A `FinCochain` extends to a full `Cochain` by extending with zero off-support.
Off-support components are uniquely zero since A.X p or B.X q is a zero object. -/
noncomputable def toCochain {n : ℤ} (z : FinCochain A B n) :
    Cochain A.toHomologicalComplex B.toHomologicalComplex n :=
  Cochain.mk fun p q hpq =>
    z.getV p ≫ eqToHom (congr_arg B.X hpq)

@[simp] lemma toCochain_v {n : ℤ} (z : FinCochain A B n) (p q : ℤ) (hpq : p + n = q) :
    (z.toCochain).v p q hpq = z.getV p ≫ eqToHom (congr_arg B.X hpq) := rfl

lemma toCochain_add {n : ℤ} (z w : FinCochain A B n) :
    (z + w).toCochain = z.toCochain + w.toCochain := by
  ext p q hpq; simp [getV_add, Preadditive.add_comp]

@[simp] lemma toCochain_smul (r : R) {n : ℤ} (z : FinCochain A B n) :
    (r • z).toCochain = r • z.toCochain := by
  ext p q hpq; simp [getV_smul, Linear.smul_comp]

/-- Restrict a full `Cochain` to the active pairs; off-support components are zero
and carry no data. -/
noncomputable def ofCochain {n : ℤ}
    (c : Cochain A.toHomologicalComplex B.toHomologicalComplex n) :
    FinCochain A B n :=
  fun ⟨p, _⟩ => c.v p (p + n) rfl

/-- Off-support components of a Cochain from a BoundedCochainComplex are uniquely zero. -/
lemma cochain_v_eq_zero_of_not_mem {n : ℤ}
    (c : Cochain A.toHomologicalComplex B.toHomologicalComplex n)
    {p : ℤ} (hp : p ∉ activePairs A B n) (q : ℤ) (hpq : p + n = q) :
    c.v p q hpq = 0 := by
  simp only [activePairs.mem_iff, not_and_or] at hp
  rcases hp with hA | hB
  · exact (isZero_X_of_not_mem hA).eq_of_src _ 0
  · exact (isZero_X_of_not_mem (hpq ▸ hB)).eq_of_tgt _ 0

/-- The `R`-linear equivalence between `FinCochain A B n` and `Cochain A.toHC B.toHC n`. -/
noncomputable def toCochainLinearEquiv (A B : BoundedCochainComplex V) (n : ℤ) :
    FinCochain A B n ≃ₗ[R] Cochain A.toHomologicalComplex B.toHomologicalComplex n where
  toFun := toCochain
  map_add' := toCochain_add
  map_smul' := fun r z => by simp [RingHom.id_apply]
  invFun := ofCochain
  left_inv z := by
    funext ⟨p, hp⟩
    simp only [ofCochain, toCochain_v, eqToHom_refl, getV_of_mem _ hp, v, Category.comp_id]
  right_inv c := by
    ext p q hpq
    subst hpq
    simp only [toCochain_v, eqToHom_refl, Category.comp_id, getV, ofCochain, v]
    split_ifs with h
    · rfl
    · exact (cochain_v_eq_zero_of_not_mem c h (p + n) rfl).symm

/-- Translating composition of `FinCochain`s corresponds to `Cochain.comp`. -/
lemma toCochain_comp {A B C : BoundedCochainComplex V} {n₁ n₂ : ℤ}
    (f : FinCochain A B n₁) (g : FinCochain B C n₂) :
    (f.comp g).toCochain = f.toCochain.comp g.toCochain rfl := by
  ext p q hpq
  rw [Cochain.comp_v _ _ rfl p (p + n₁) q rfl (by linarith)]
  simp only [toCochain_v, eqToHom_refl, Category.comp_id]
  by_cases hp : p ∈ activePairs A C (n₁ + n₂)
  · simp only [getV_of_mem _ hp, comp, v, Category.assoc, eqToHom_trans]
  · rw [getV_of_not_mem _ hp, zero_comp]
    simp only [activePairs.mem_iff, not_and_or] at hp
    rcases hp with hA | hC
    · simp [getV_of_not_mem f (fun h => hA (activePairs.mem_left h))]
    · simp [getV_of_not_mem g (fun h =>
          hC (add_assoc p n₁ n₂ ▸ activePairs.mem_right h))]

/-- Translating `δ_fin` corresponds to the Mathlib differential `δ`. -/
lemma toCochain_δ_fin {n : ℤ} (z : FinCochain A B n) :
    (δ_fin z).toCochain = δ n (n + 1) z.toCochain := by
  ext p q hpq
  subst hpq
  -- Expand δ with explicit intermediate indices; after subst, all eqToHoms become 𝟙
  rw [δ_v n (n + 1) rfl z.toCochain p (p + (n + 1)) rfl (p + n) (p + 1) (by ring) rfl]
  simp only [toCochain_v, getV_δ_fin, Preadditive.add_comp, Category.assoc,
    eqToHom_refl, Category.comp_id]

/-- `toCochain` sends `ofHom h` to Mathlib's `0`-cochain of the underlying chain map. -/
lemma toCochain_ofHom {A B : BoundedCochainComplex V} (h : A ⟶ B) :
    (ofHom h).toCochain = Cochain.ofHom h.hom := by
  ext p
  rw [toCochain_v]
  by_cases hp : p ∈ activePairs A B 0
  · rw [getV_of_mem _ hp]
    simp [ofHom, v, Cochain.ofHom, Cochain.ofHoms]
  · rw [getV_of_not_mem _ hp, zero_comp]
    exact (cochain_v_eq_zero_of_not_mem (Cochain.ofHom h.hom) hp p (add_zero p)).symm

/-- `[SF₁]`: a chain map is a `δ_fin`-cycle. This is the degenerate first
`A∞`-functor axiom for functor data whose degree-`0` components are genuine
chain maps. -/
lemma δ_fin_ofHom {A B : BoundedCochainComplex V} (h : A ⟶ B) :
    δ_fin (ofHom h) = 0 := by
  refine ((toCochainLinearEquiv (R := ℤ) A B (0 + 1)).map_eq_zero_iff).mp ?_
  show (δ_fin (ofHom h)).toCochain = 0
  rw [toCochain_δ_fin, toCochain_ofHom]
  exact δ_ofHom h.hom

/-- `toCochain` commutes with the `ℤˣ` action. -/
lemma toCochain_units_smul (u : ℤˣ) {n : ℤ} (z : FinCochain A B n) :
    (u • z).toCochain = u • z.toCochain := by
  ext p q hpq
  simp only [toCochain_v, Units.smul_def, getV_smul, Linear.smul_comp]
  rfl

/-- `toCochain` commutes with the `ℤ` action. -/
lemma toCochain_zsmul (c : ℤ) {n : ℤ} (z : FinCochain A B n) :
    (c • z).toCochain = c • z.toCochain :=
  map_zsmul (toCochainLinearEquiv (R := ℤ) A B n) c z

/-- `toCochain` sends zero to zero. -/
lemma toCochain_zero {n : ℤ} :
    (0 : FinCochain A B n).toCochain = (0 : Cochain A.toHomologicalComplex B.toHomologicalComplex n) :=
  map_zero (toCochainLinearEquiv (R := ℤ) A B n)

/-- Triple composition associativity via `toCochain`.
    Note: `(f.comp g).comp h` and `f.comp (g.comp h)` live in *different* types
    (`(n₁+n₂)+n₃` vs `n₁+(n₂+n₃)`), so this is stated as a `toCochain` equality. -/
lemma toCochain_comp_assoc {A B C D : BoundedCochainComplex V} {n₁ n₂ n₃ : ℤ}
    (f : FinCochain A B n₁) (g : FinCochain B C n₂) (h : FinCochain C D n₃) :
    ((f.comp g).comp h).toCochain =
    f.toCochain.comp (g.toCochain.comp h.toCochain rfl) (add_assoc n₁ n₂ n₃).symm := by
  simp only [toCochain_comp]
  exact CochainComplex.HomComplex.Cochain.comp_assoc f.toCochain g.toCochain h.toCochain rfl rfl rfl

end ToCochainEquiv

end FinCochain

end FinCochainSection

section AInfinityInstance

open AInfinityCategoryTheory AInfinityTheory CochainComplex.HomComplex FinCochain

variable {R : Type*} [CommRing R] [Linear R V]

/-! The category of bounded cochain complexes is an A∞-category over R,
  with grading β = ℤ.  The A∞-structure is that of a strict dg-category:
  * `m₁` is the differential `δ` on the Hom-complex;
  * `m₂` is composition of cochains;
  * `mₙ = 0` for n ≥ 3.

  The Stasheff identities reduce to:
  * n = 1: `δ ∘ δ = 0` (`δ_δ`);
  * n = 2: Leibniz rule (`δ_comp`);
  * n = 3: strict associativity of `comp` (`comp_assoc`);
  * n ≥ 4: all terms involve some `mₖ` with k ≥ 3, which is 0. -/

abbrev bccHom (A B : BoundedCochainComplex V) : ℤ → ModuleCat R :=
  fun n => ModuleCat.of R (FinCochain A B n)

lemma bccOperationTargetDeg_one (deg : Fin 1 → ℤ) :
    operationTargetDeg deg = deg ⟨0, by omega⟩ + 1 := by
  show (∑ i : Fin 1, deg i) + shift_ofInt (β := ℤ) 1 = deg ⟨0, by omega⟩ + 1
  simp [shift_ofInt_int]

lemma bccOperationTargetDeg_two (deg : Fin 2 → ℤ) :
    operationTargetDeg deg = deg ⟨0, by omega⟩ + deg ⟨1, by omega⟩ := by
  show (∑ i : Fin 2, deg i) + shift_ofInt (β := ℤ) 0 = deg ⟨0, by omega⟩ + deg ⟨1, by omega⟩
  simp [Fin.sum_univ_two, shift_ofInt_int]

lemma bccOperationTargetType_one (obj : Fin 2 → BoundedCochainComplex V) (deg : Fin 1 → ℤ) :
    (operationTargetType bccHom obj deg : ModuleCat R) =
      bccHom (obj 0) (obj (Fin.last 1)) (deg ⟨0, by omega⟩ + 1) := by
  unfold operationTargetType
  rw [bccOperationTargetDeg_one]

lemma bccOperationTargetType_two (obj : Fin 3 → BoundedCochainComplex V) (deg : Fin 2 → ℤ) :
    (operationTargetType bccHom obj deg : ModuleCat R) =
      bccHom (obj 0) (obj (Fin.last 2)) (deg ⟨0, by omega⟩ + deg ⟨1, by omega⟩) := by
  unfold operationTargetType
  rw [bccOperationTargetDeg_two]

/-- Degree-cast of a `FinCochain` as an `R`-linear map. Lets the A∞ operations land in
`operationTargetType` using only a clean *degree-level* cast (within a fixed `FinCochain A B`
family), avoiding opaque `ModuleCat`-object `rw`/`▸` casts. -/
def FinCochain.degCast {A B : BoundedCochainComplex V} {m n : ℤ} (h : m = n) :
    FinCochain A B m →ₗ[R] FinCochain A B n := h ▸ LinearMap.id

@[simp] lemma FinCochain.degCast_rfl {A B : BoundedCochainComplex V} {m : ℤ}
    (z : FinCochain A B m) : FinCochain.degCast (R := R) (rfl : m = m) z = z := rfl

/-- `toCochain` turns a `degCast` into the corresponding degree-level `▸` cast. -/
lemma toCochain_degCast {A B : BoundedCochainComplex V} {m n : ℤ} (h : m = n)
    (z : FinCochain A B m) :
    (FinCochain.degCast (R := R) h z).toCochain = h ▸ z.toCochain := by cases h; rfl

@[simp] lemma degCast_eq_zero_iff {A B : BoundedCochainComplex V} {m n : ℤ} (h : m = n)
    (z : FinCochain A B m) : FinCochain.degCast (R := R) h z = 0 ↔ z = 0 := by cases h; simp

def bccAInfinityPreCategory :
    AInfinityPreCategory (β := ℤ) R (BoundedCochainComplex V) where
  Hom := bccHom
  m {n} obj deg := by
    obtain ⟨n, hn⟩ := n
    match n with
    | 0 => exact absurd hn (Nat.lt_irrefl 0)
    | 1 =>
      -- m₁ = δ_fin, the FinCochain differential (landed via a clean degree cast)
      exact (FinCochain.degCast (R := R) (bccOperationTargetDeg_one deg).symm).compMultilinearMap
        { toFun := fun v => δ_fin (v ⟨0, by exact hn⟩)
          map_update_add' := fun v i x y => by
            fin_cases i; simp only [Function.update_self]; exact δ_fin_add x y
          map_update_smul' := fun v i r x => by
            fin_cases i; simp only [Function.update_self]; exact δ_fin_smul r x }
    | 2 =>
      -- m₂(f,g) = (deg g).negOnePow • f.comp g  (the Koszul-signed composition), via a degree cast.
      -- The Koszul sign is applied as an outer ℤ-smul of the multilinear map, and the inner map is
      -- the plain composition, landed into the target degree via a clean degree cast.
      exact (deg ⟨1, by exact Nat.lt_succ_self 1⟩).negOnePow.val •
        (FinCochain.degCast (R := R) (bccOperationTargetDeg_two deg).symm).compMultilinearMap
          { toFun := fun v =>
              FinCochain.comp (v ⟨0, by exact hn⟩) (v ⟨1, by exact Nat.lt_succ_self 1⟩)
            map_update_add' := fun v i x y => by
              fin_cases i
              · simpa using FinCochain.comp_add_left x y (v 1)
              · simpa using FinCochain.comp_add_right (v 0) x y
            map_update_smul' := fun v i r x => by
              fin_cases i
              · simpa using FinCochain.comp_smul_left r x (v 1)
              · simpa using FinCochain.comp_smul_right r (v 0) x }
    | _ + 3 =>
      -- mₙ = 0 for n ≥ 3
      exact 0

/-- `toCochain` commutes with a degree-level `▸` cast. -/
private lemma toCochain_cast_deg {A B : BoundedCochainComplex V} {m n : ℤ} (h : m = n)
    (z : FinCochain A B m) : (h ▸ z).toCochain = h ▸ z.toCochain := by cases h; rfl

/-- `toCochain` absorbs a type-level `cast` between definitionally equal `FinCochain` types. -/
private lemma toCochain_typecast {A B : BoundedCochainComplex V} {d : ℤ}
    (h : (FinCochain A B d : Type _) = FinCochain A B d) (z : FinCochain A B d) :
    (cast h z).toCochain = z.toCochain := rfl

@[simp] lemma toCochainLinearEquiv_apply {A B : BoundedCochainComplex V} {n : ℤ}
    (z : FinCochain A B n) :
    toCochainLinearEquiv (R := R) A B n z = z.toCochain := rfl

/-- `δ` absorbs a degree cast on its domain. -/
lemma δ_cast_dom {F G : CochainComplex V ℤ} {b a : ℤ} (H : b = a)
    (c : CochainComplex.HomComplex.Cochain F G b) (n : ℤ) :
    CochainComplex.HomComplex.δ a n (H ▸ c) = CochainComplex.HomComplex.δ b n c := by
  cases H; rfl

/-- `toCochain` commutes with `δ_fin` a degree-cast: pushes casts to the Cochain world. -/
lemma toCochain_degCast_δ_fin {A B : BoundedCochainComplex V} {m n : ℤ} (h : m = n)
    (z : FinCochain A B m) :
    (FinCochain.degCast (R := R) h z).toCochain = h ▸ z.toCochain := toCochain_degCast h z

-- Casting zero along a type equality gives zero (for ModuleCat R types).
private lemma cast_zero_eq {R : Type*} [CommRing R] {A B : ModuleCat R} (h : A = B) :
    h ▸ (0 : A) = (0 : B) := by cases h; rfl

-- h ▸ a = 0 ↔ a = 0 for ModuleCat R types. Used to eliminate the outer ▸ cast in Stasheff terms.
private lemma cast_zero_iff {R : Type*} [CommRing R] {A B : ModuleCat R} (h : A = B) {a : A} :
    h ▸ a = (0 : B) ↔ a = (0 : A) := by cases h; simp

-- A `▸` cast on the codomain of a multilinear map commutes with applying it.
-- Used to move the `rw [htype]` cast in `bccAInfinityPreCategory.m` out of the application.
private lemma modcat_mlmap_cast_apply {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → ModuleCat R} {N₁ N₂ : ModuleCat R} (h : N₁ = N₂)
    (f : MultilinearMap R (fun i => (M i : Type _)) (N₁ : Type _))
    (v : ∀ i, (M i : Type _)) :
    (h ▸ f) v = h ▸ (f v) := by cases h; rfl

-- Eliminate a `ModuleCat`-object `▸` cast (between `bccHom A B` at two provably-equal degrees)
-- under `toCochain`, turning it into a clean degree-level `▸` cast on the `Cochain`.
private lemma toCochain_bccHom_cast {A B : BoundedCochainComplex V} {d1 d2 : ℤ} (e : d1 = d2)
    (h : (bccHom (R := R) A B d1) = bccHom (R := R) A B d2)
    (z : (bccHom (R := R) A B d1 : Type _)) :
    toCochain (h ▸ z) = e ▸ (toCochain z) := by
  subst e; rfl

-- `.v` of a degree-level `▸` cast on a `Cochain`.
private lemma cochain_cast_v {A B : CochainComplex V ℤ} {d1 d2 : ℤ} (h : d1 = d2)
    (c : CochainComplex.HomComplex.Cochain A B d1) (p q : ℤ) (hpq : p + d2 = q) :
    (h ▸ c).v p q hpq = c.v p q (by rw [h]; exact hpq) := by
  subst h; rfl

-- A degree-level `▸` cast commutes with the `ℤˣ` action on cochains.
private lemma cast_units_smul {A B : CochainComplex V ℤ} {d1 d2 : ℤ} (h : d1 = d2) (u : ℤˣ)
    (c : CochainComplex.HomComplex.Cochain A B d1) :
    h ▸ (u • c) = u • (h ▸ c) := by subst h; rfl

-- `HEq` of two `Cochain`s at provably equal degrees follows from componentwise equality.
private lemma cochain_heq_of_v_eq {A B : CochainComplex V ℤ} {d1 d2 : ℤ} (hd : d1 = d2)
    {c1 : CochainComplex.HomComplex.Cochain A B d1}
    {c2 : CochainComplex.HomComplex.Cochain A B d2}
    (h : ∀ p q (hpq : p + d2 = q), c1.v p q (by rw [hd]; exact hpq) = c2.v p q hpq) :
    c1 ≍ c2 := by
  subst hd
  exact heq_of_eq (CochainComplex.HomComplex.Cochain.ext _ _ h)

-- Application form of `m₁` (arity 1): reduces the iota-stuck match on `⟨1, h⟩`.
private lemma bccM_one_apply {obj : Fin 2 → BoundedCochainComplex V} {deg : Fin 1 → ℤ}
    (h : 0 < 1) (v : ∀ i : Fin 1, (composableHomType (β := ℤ) (R := R) bccHom obj deg i)) :
    bccAInfinityPreCategory.m (R := R) (n := ⟨1, h⟩) obj deg v
      = FinCochain.degCast (R := R) (bccOperationTargetDeg_one deg).symm (δ_fin (v ⟨0, h⟩)) := rfl

-- Application form of `m₂` (arity 2): reduces the iota-stuck match on `⟨2, h⟩`.
private lemma bccM_two_apply {obj : Fin 3 → BoundedCochainComplex V} {deg : Fin 2 → ℤ}
    (h : 0 < 2) (v : ∀ i : Fin 2, (composableHomType (β := ℤ) (R := R) bccHom obj deg i)) :
    bccAInfinityPreCategory.m (R := R) (n := ⟨2, h⟩) obj deg v
      = (deg 1).negOnePow • FinCochain.degCast (R := R) (bccOperationTargetDeg_two deg).symm
          (FinCochain.comp (v ⟨0, h⟩) (v ⟨1, by norm_num⟩)) := rfl

/-! #### The A∞ operations in normalized-degree form

The A∞-native language for stating functor axioms into this category: `mOne`
and `mTwo` are `m₁` and `m₂` of `bccAInfinityPreCategory` — fed via the
chain-argument packagings `single₁`/`pair₂` — with the target degree
normalized along an equation `h` by a `degCast`. The translation theorems
`mOne_eq`/`mTwo_eq` identify them with the Hom-complex differential `δ_fin`
and the Koszul-signed composition `comp`. -/

/-- A single cochain as the argument vector of the unary A∞ operation. -/
def single₁ {X Y : BoundedCochainComplex V} {d : ℤ} (x : FinCochain X Y d) :
    ∀ i : Fin 1, (composableHomType (β := ℤ) (R := R) bccHom ![X, Y] ![d] i) :=
  Fin.cons x fun i => i.elim0

/-- Two composable cochains as the argument vector of the binary A∞ operation. -/
def pair₂ {X Y Z : BoundedCochainComplex V} {d₁ d₂ : ℤ}
    (x : FinCochain X Y d₁) (y : FinCochain Y Z d₂) :
    ∀ i : Fin 2, (composableHomType (β := ℤ) (R := R) bccHom ![X, Y, Z] ![d₁, d₂] i) :=
  Fin.cons x (Fin.cons y fun i => i.elim0)

/-- `m₁` of `bccAInfinityPreCategory` on a single cochain, with the target degree
normalized along `h`. -/
def mOne {X Y : BoundedCochainComplex V} {d e : ℤ} (h : d + 1 = e)
    (x : FinCochain X Y d) : FinCochain X Y e :=
  FinCochain.degCast (R := R) ((bccOperationTargetDeg_one ![d]).trans h)
    (bccAInfinityPreCategory.m (R := R) (n := ⟨1, Nat.one_pos⟩) ![X, Y] ![d] (single₁ x))

/-- `m₂` of `bccAInfinityPreCategory` on two composable cochains — including the
Koszul sign `(-1)^{deg y}` — with the target degree normalized along `h`. -/
def mTwo {X Y Z : BoundedCochainComplex V} {d₁ d₂ e : ℤ} (h : d₁ + d₂ = e)
    (x : FinCochain X Y d₁) (y : FinCochain Y Z d₂) : FinCochain X Z e :=
  FinCochain.degCast (R := R) ((bccOperationTargetDeg_two ![d₁, d₂]).trans h)
    (bccAInfinityPreCategory.m (R := R) (n := ⟨2, Nat.zero_lt_two⟩) ![X, Y, Z] ![d₁, d₂]
      (pair₂ x y))

lemma FinCochain.degCast_degCast {A B : BoundedCochainComplex V} {a b c : ℤ}
    (h₁ : a = b) (h₂ : b = c) (z : FinCochain A B a) :
    FinCochain.degCast (R := R) h₂ (FinCochain.degCast (R := R) h₁ z) =
      FinCochain.degCast (R := R) (h₁.trans h₂) z := by
  subst h₁; subst h₂; rfl

lemma FinCochain.degCast_units_smul {A B : BoundedCochainComplex V} {a b : ℤ}
    (h : a = b) (u : ℤˣ) (z : FinCochain A B a) :
    FinCochain.degCast (R := R) h (u • z) = u • FinCochain.degCast (R := R) h z := by
  subst h; rfl

/-- `mOne` is the Hom-complex differential `δ_fin`. -/
theorem mOne_eq {X Y : BoundedCochainComplex V} {d e : ℤ} (h : d + 1 = e)
    (x : FinCochain X Y d) :
    mOne (R := R) h x = FinCochain.degCast (R := R) h (δ_fin x) :=
  -- Term-mode: the inner `degCast` (from `bccM_one_apply`) carries
  -- `![X, Y] ⟨0, _⟩`-shaped endpoint implicits, definitionally but not
  -- syntactically `X`/`Y`, which blocks `rw`; elaboration unification copes.
  (congrArg (fun z => FinCochain.degCast (R := R)
        ((bccOperationTargetDeg_one ![d]).trans h) z)
      (bccM_one_apply Nat.one_pos (single₁ x))).trans
    (FinCochain.degCast_degCast (R := R) _ _ _)

/-- `mTwo` is the Koszul-signed composition of `FinCochain`s. -/
theorem mTwo_eq {X Y Z : BoundedCochainComplex V} {d₁ d₂ e : ℤ} (h : d₁ + d₂ = e)
    (x : FinCochain X Y d₁) (y : FinCochain Y Z d₂) :
    mTwo (R := R) h x y =
      d₂.negOnePow • FinCochain.degCast (R := R) h (FinCochain.comp x y) :=
  (congrArg (fun z => FinCochain.degCast (R := R)
        ((bccOperationTargetDeg_two ![d₁, d₂]).trans h) z)
      (bccM_two_apply Nat.zero_lt_two (pair₂ x y))).trans
    ((FinCochain.degCast_units_smul (R := R) _ _ _).trans
      (congrArg (fun z => (![d₁, d₂] 1).negOnePow • z)
        (FinCochain.degCast_degCast (R := R) _ _ _)))

/-- On a genuine chain map, `m₁` vanishes: this discharges `[SF₁]` for any
A∞-functor data whose unary component is a chain map. -/
theorem mOne_ofHom {A B : BoundedCochainComplex V} {e : ℤ} (h : (0 : ℤ) + 1 = e)
    (φ : A ⟶ B) : mOne (R := R) h (FinCochain.ofHom φ) = 0 := by
  rw [mOne_eq, δ_fin_ofHom, map_zero]

/-
Closed form of the `(r=0,s=1)` term in the n=2 Stasheff sum:
`m₂(m₁ x₀, x₁) = (deg 1).negOnePow • (δ (x₀)) ∘ x₁`.
-/
set_option maxHeartbeats 4000000 in
private lemma toCochain_stasheff_two_term_01
    (obj : Fin ((2 : ℕ+).val + 1) → BoundedCochainComplex V)
    (deg : Fin (2 : ℕ+).val → ℤ)
    (x : ∀ i : Fin (2 : ℕ+).val, (composableHomType (β := ℤ) (R := R) bccHom obj deg i)) :
    toCochain (indexedStasheffTerm (β := ℤ) (R := R) (n := (2 : ℕ+)) bccHom
        (fun {n} => bccAInfinityPreCategory.m) obj deg x 0 1 (by norm_num) (by norm_num))
      = (deg 1).negOnePow •
          Cochain.comp (CochainComplex.HomComplex.δ (deg 0) (deg 0 + 1) (toCochain (x 0)))
            (toCochain (x 1))
            ((add_right_comm (deg 0) 1 (deg 1)).trans
                (congrArg (· + 1) (Fin.sum_univ_two deg).symm) :
              (deg 0 + 1) + deg 1 = stasheffTargetDeg deg) := by
  unfold indexedStasheffTerm
  erw [toCochain_bccHom_cast (stasheffDegOut_sum deg 0 1 (by norm_num))]
  simp only [Nat.add_sub_cancel, PNat.val_ofNat, bccAInfinityPreCategory]
  erw [MultilinearMap.smul_apply, LinearMap.compMultilinearMap_apply]
  simp only [MultilinearMap.coe_mk, id_eq,
    show ¬((0 : ℕ) < 0) from by decide, show ¬((1 : ℕ) < 0) from by decide,
    show ¬((1 : ℕ) = 0) from by decide, ↓reduceDIte]
  erw [LinearMap.compMultilinearMap_apply]
  simp only [MultilinearMap.coe_mk, eq_mpr_eq_cast, eq_mp_eq_cast, cast_cast, cast_eq]
  simp only [stasheffDegOut, Nat.add_zero, Nat.add_sub_cancel,
    show ¬((1 : ℕ) < 0) from by decide, show ¬((1 : ℕ) = 0) from by decide, ↓reduceDIte]
  rw [← Units.smul_def]
  erw [toCochain_units_smul]
  erw [toCochain_degCast, toCochain_comp, toCochain_degCast, toCochain_δ_fin]
  simp only [stasheffDegIn, Nat.add_zero, Nat.add_sub_cancel]
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  simp +decide [ cochain_cast_v, δ_cast_dom ];
  congr! 1;
  · unfold stasheffInnerDeg stasheffTargetDeg; simp +decide ;
    unfold operationTargetDeg stasheffDegIn; simp +decide ;
    exact (Fin.sum_univ_two _).trans (by simp +decide <;> ring)
  · have le01 : (0 : ℕ) + 1 ≤ ((2 : ℕ+) : ℕ) := by norm_num
    have hd0 : stasheffInnerDeg deg 0 1 le01 = deg 0 + 1 := bccOperationTargetDeg_one _
    have hstar : stasheffTargetDeg deg = deg 0 + deg 1 + 1 :=
      (show stasheffTargetDeg deg = (∑ i, deg i) + 1 from rfl).trans
        (congrArg (· + 1) (Fin.sum_univ_two deg))
    refine cochain_heq_of_v_eq (by assumption) (fun p q hpq => ?_)
    have hend : p + (deg 0 + 1) + deg 1 = q :=
      (by ring : p + (deg 0 + 1) + deg 1 = p + (deg 0 + deg 1 + 1)).trans
        ((congrArg (p + ·) hstar.symm).trans hpq)
    erw [Cochain.units_smul_v, Cochain.units_smul_v, cochain_cast_v]
    refine congrArg₂ (· • ·) rfl ?_
    erw [Cochain.comp_v _ _ _ p (p + (deg 0 + 1)) q (congrArg (p + ·) hd0) hend,
      Cochain.comp_v _ _ _ p (p + (deg 0 + 1)) q rfl hend]
    erw [cochain_cast_v]
    rfl

/-
Closed form of the `(r=1,s=1)` term in the n=2 Stasheff sum:
`m₂(x₀, m₁ x₁) = (deg 1 + 1).negOnePow • x₀ ∘ (δ x₁)`.
-/
set_option maxHeartbeats 4000000 in
private lemma toCochain_stasheff_two_term_11
    (obj : Fin ((2 : ℕ+).val + 1) → BoundedCochainComplex V)
    (deg : Fin (2 : ℕ+).val → ℤ)
    (x : ∀ i : Fin (2 : ℕ+).val, (composableHomType (β := ℤ) (R := R) bccHom obj deg i)) :
    toCochain (indexedStasheffTerm (β := ℤ) (R := R) (n := (2 : ℕ+)) bccHom
        (fun {n} => bccAInfinityPreCategory.m) obj deg x 1 1 (by norm_num) (by norm_num))
      = (deg 1 + 1).negOnePow •
          Cochain.comp (toCochain (x 0))
            (CochainComplex.HomComplex.δ (deg 1) (deg 1 + 1) (toCochain (x 1)))
            ((add_assoc (deg 0) (deg 1) 1).symm.trans
                (congrArg (· + 1) (Fin.sum_univ_two deg).symm) :
              deg 0 + (deg 1 + 1) = stasheffTargetDeg deg) := by
  unfold indexedStasheffTerm;
  erw [ toCochain_bccHom_cast ( stasheffDegOut_sum deg 1 1 ( by simp +decide ) ) ];
  erw [ bccM_two_apply ];
  simp +decide [ stasheffDegOut, stasheffTargetDeg, bccOperationTargetDeg_two ];
  simp +decide [ stasheffInnerDeg, bccOperationTargetDeg_one, bccOperationTargetDeg_two ];
  erw [ toCochain_units_smul ];
  erw [ toCochain_degCast, toCochain_comp, toCochain_degCast, toCochain_δ_fin ];
  ext p q hpq; simp +decide [ cochain_cast_v, δ_cast_dom ] ;
  congr! 1;
  · have hr1 : 1 + 1 ≤ ((2 : ℕ+) : ℕ) := by norm_num
    rw [add_zero]
    refine Eq.trans (Fin.sum_univ_two _)
      (Eq.trans ?_ (congrArg (· + 1) (Fin.sum_univ_two deg).symm))
    show deg 0 + operationTargetDeg (stasheffDegIn deg 1 1 hr1) = deg 0 + deg 1 + 1
    exact (congrArg (deg 0 + ·)
        (bccOperationTargetDeg_one (stasheffDegIn deg 1 1 hr1))).trans
      (show deg 0 + (deg 1 + 1) = deg 0 + deg 1 + 1 by ring)
  · have le11 : (1 : ℕ) + 1 ≤ ((2 : ℕ+) : ℕ) := by norm_num
    have hin11 : operationTargetDeg (stasheffDegIn deg 1 1 le11) = deg 1 + 1 :=
      bccOperationTargetDeg_one _
    refine cochain_heq_of_v_eq (by assumption) (fun p q hpq => ?_)
    have hendZ : p + deg 0 + (deg 1 + 1) = q :=
      (by ring : p + deg 0 + (deg 1 + 1) = p + (deg 0 + deg 1 + 1)).trans
        ((congrArg (p + ·) (congrArg (· + 1) (Fin.sum_univ_two deg)).symm).trans hpq)
    have hendY : p + deg 0 + operationTargetDeg (stasheffDegIn deg 1 1 le11) = q := by
      rw [hin11]; exact hendZ
    erw [Cochain.units_smul_v, Cochain.units_smul_v, cochain_cast_v]
    refine congrArg₂ (· • ·) rfl ?_
    erw [Cochain.comp_v _ _ _ p (p + deg 0) q rfl hendY,
      Cochain.comp_v _ _ _ p (p + deg 0) q rfl hendZ]
    erw [cochain_cast_v]
    rfl

/-
Closed form of the `(r=0,s=2)` term in the n=2 Stasheff sum:
`m₁(m₂(x₀,x₁)) = (deg 1).negOnePow • δ(x₀ ∘ x₁)`.
-/
set_option maxHeartbeats 4000000 in
private lemma toCochain_stasheff_two_term_02
    (obj : Fin ((2 : ℕ+).val + 1) → BoundedCochainComplex V)
    (deg : Fin (2 : ℕ+).val → ℤ)
    (x : ∀ i : Fin (2 : ℕ+).val, (composableHomType (β := ℤ) (R := R) bccHom obj deg i)) :
    toCochain (indexedStasheffTerm (β := ℤ) (R := R) (n := (2 : ℕ+)) bccHom
        (fun {n} => bccAInfinityPreCategory.m) obj deg x 0 2 (by norm_num) (by norm_num))
      = (deg 1).negOnePow •
          CochainComplex.HomComplex.δ (deg 0 + deg 1) (stasheffTargetDeg deg)
            (Cochain.comp (toCochain (x 0)) (toCochain (x 1)) rfl) := by
  unfold indexedStasheffTerm;
  erw [ toCochain_bccHom_cast ( stasheffDegOut_sum deg 0 2 ( by simp +decide ) ) ];
  erw [ toCochain_degCast, toCochain_δ_fin, bccM_two_apply ];
  simp +decide [ stasheffDegOut, stasheffDegIn, bccOperationTargetDeg_two, bccOperationTargetDeg_one ];
  erw [ toCochain_typecast ];
  erw [ toCochain_units_smul ];
  erw [ toCochain_degCast, toCochain_comp ];
  ext p q hpq; simp +decide [ cochain_cast_v, δ_cast_dom ] ;
  congr! 1;
  · exact (congrArg (· + 1)
        (bccOperationTargetDeg_two (stasheffDegIn deg 0 2 (by norm_num)))).trans
      (congrArg (· + 1) (Fin.sum_univ_two deg).symm)
  · have le02 : (0 : ℕ) + 2 ≤ ((2 : ℕ+) : ℕ) := by norm_num
    have hin02 : stasheffInnerDeg deg 0 2 le02 = deg 0 + deg 1 := bccOperationTargetDeg_two _
    have hm : stasheffInnerDeg deg 0 2 le02 + 1 = stasheffTargetDeg deg :=
      (congrArg (· + 1) hin02).trans (congrArg (· + 1) (Fin.sum_univ_two deg).symm)
    erw [CochainComplex.HomComplex.δ_units_smul, δ_cast_dom]
    exact congr_arg_heq (fun m => (deg 1).negOnePow •
      CochainComplex.HomComplex.δ (deg 0 + deg 1) m
        ((toCochain (x 0)).comp (toCochain (x 1)) rfl)) hm

/-
Helper for the n=2 Stasheff identity: the Leibniz rule for δ_fin and composition.
-/
set_option maxHeartbeats 8000000 in
lemma stasheff_two
    (obj : Fin ((2 : ℕ+).val + 1) → BoundedCochainComplex V)
    (deg : Fin (2 : ℕ+).val → ℤ)
    (x : ∀ i : Fin (2 : ℕ+).val, (composableHomType (β := ℤ) (R := R) bccHom obj deg i)) :
    indexedStasheffSum (β := ℤ) (R := R) (n := (2 : ℕ+)) bccHom
        (fun {n} ↦ bccAInfinityPreCategory.m) obj deg x = 0 := by
  simp only [indexedStasheffSum, PNat.val_ofNat]
  have h01 : (⟨0, by decide⟩ : { x // x ∈ Finset.range (2 + 1) }) ∉
      ({⟨1, by decide⟩, ⟨2, by decide⟩} : Finset { x // x ∈ Finset.range (2 + 1) }) := by decide
  have h12 : (⟨1, by decide⟩ : { x // x ∈ Finset.range (2 + 1) }) ∉
      ({⟨2, by decide⟩} : Finset { x // x ∈ Finset.range (2 + 1) }) := by decide
  simp only [
    show (Finset.range (2 + 1) : Finset ℕ).attach =
        ({⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩} :
          Finset { x // x ∈ Finset.range (2 + 1) }) from by decide,
    Finset.sum_insert h01, Finset.sum_insert h12, Finset.sum_singleton,
    show (Finset.Ico 1 (2 - (0 : ℕ) + 1) : Finset ℕ).attach =
        ({⟨1, by decide⟩, ⟨2, by decide⟩} :
          Finset { x // x ∈ (Finset.Ico 1 (2 - (0 : ℕ) + 1) : Finset ℕ) }) from by decide,
    show (Finset.Ico 1 (2 - (1 : ℕ) + 1) : Finset ℕ).attach =
        ({⟨1, by decide⟩} :
          Finset { x // x ∈ (Finset.Ico 1 (2 - (1 : ℕ) + 1) : Finset ℕ) }) from by decide,
    show (Finset.Ico 1 (2 - (2 : ℕ) + 1) : Finset ℕ).attach =
        (∅ : Finset { x // x ∈ (Finset.Ico 1 (2 - (2 : ℕ) + 1) : Finset ℕ) }) from by decide,
    Finset.sum_insert (by decide : (⟨1, by decide⟩ :
        { x // x ∈ (Finset.Ico 1 (2 - (0 : ℕ) + 1) : Finset ℕ) }) ∉
        ({⟨2, by decide⟩} : Finset _)),
    Finset.sum_singleton, Finset.sum_empty, add_zero]
  simp only [stasheffSign, stasheffSignParity, Finset.sum_fin_eq_sum_range,
    show (2 : ℕ) - 0 - 1 = 1 from by norm_num,
    show (2 : ℕ) - 0 - 2 = 0 from by norm_num,
    show (2 : ℕ) - 1 - 1 = 0 from by norm_num,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, add_zero,
    sub_self, ZMod.val_zero, pow_zero, one_smul]
  refine ((toCochainLinearEquiv (R := R) (obj 0) (obj (Fin.last 2))
      (stasheffTargetDeg deg)).map_eq_zero_iff).mp ?_
  erw [toCochainLinearEquiv_apply, toCochain_add, toCochain_add, toCochain_add,
    toCochain_zsmul, toCochain_zsmul, toCochain_zsmul, toCochain_zero]
  erw [ toCochain_stasheff_two_term_01 obj deg x, toCochain_stasheff_two_term_02 obj deg x,
    toCochain_stasheff_two_term_11 obj deg x ];
  rw [ CochainComplex.HomComplex.δ_comp ];
  any_goals rfl;
  any_goals exact congrArg (· + 1) (Fin.sum_univ_two deg).symm;
  any_goals unfold stasheffTargetDeg; simp +decide [ Fin.sum_univ_two ];
  simp +decide [ Grading.sign, Int.negOnePow_add ];
  rcases Int.even_or_odd' ( deg 1 ) with ⟨ k, hk | hk ⟩ <;>
    simp +decide [ hk, show (deg ⟨0 + 1, by norm_num⟩ : ℤ) = deg 1 from rfl, ZMod.val ];
  -- On 4.30 the sign-parity exponent contains the atom `deg (1 : Fin (0 + 2))` (numeral at
  -- the `n - r - s`-shaped dimension), which `simp [hk]` does not identify with `deg 1`;
  -- bridge it explicitly before the parity computation.
  · haveI : NeZero (0 + 2) := ⟨by norm_num⟩
    have hb : (deg (1 : Fin (0 + 2)) : ℤ) = 2 * k := hk
    simp +decide [hb, ZMod.val]
    erw [ show ( 2 * k - 1 : ZMod 2 ) = 1 by erw [ show ( 2 : ZMod 2 ) = 0 by rfl ] ; simp +decide ] ; simp +decide [ ZMod.val ];
    -- Restate with canonical instances (the goal's smul/neg instance paths are exotic on
    -- 4.30 and no simp lemma keys on them); `exact` bridges by definitional unfolding.
    have key : ∀ {F G : CochainComplex V ℤ} {n : ℤ}
        (A B : CochainComplex.HomComplex.Cochain F G n),
        (-1 : ℤ) • ((1 : ℤˣ) • A) + (1 : ℤ) • ((1 : ℤˣ) • (B + (1 : ℤˣ) • A)) +
          ((1 : ℤ) • ((-1 : ℤˣ) • B) + 0) = 0 := fun A B => by
      simp only [one_smul, one_zsmul, Units.neg_smul, neg_zsmul, add_zero]
      abel
    exact key _ _
  · haveI : NeZero (0 + 2) := ⟨by norm_num⟩
    have hb : (deg (1 : Fin (0 + 2)) : ℤ) = 2 * k + 1 := hk
    simp +decide [hb, ZMod.val]
    erw [ show ( 2 * k : ZMod 2 ) = 0 by erw [ show ( 2 : ZMod 2 ) = 0 by rfl ] ; simp +decide ] ; simp +decide [ add_assoc ]
    have key : ∀ {F G : CochainComplex V ℤ} {n : ℤ}
        (A B : CochainComplex.HomComplex.Cochain F G n),
        (1 : ℤ) • ((-1 : ℤˣ) • A) + (1 : ℤ) • ((-1 : ℤˣ) • (B + (-1 : ℤˣ) • A)) +
          ((1 : ℤ) • ((1 : ℤˣ) • B) + 0) = 0 := fun A B => by
      simp only [one_smul, one_zsmul, Units.neg_smul, neg_zsmul, smul_neg, add_zero]
      abel
    exact key _ _

-- Helper for the n=1 Stasheff identity. Uses literal (1 : ℕ+) so that PNat.one_coe fires,
-- unlike the match-branch context where ⟨1, hn⟩ : ℕ+ has iota-stuck coercion ↑⟨1,hn⟩.
-- The single non-zero term of the n=1 Stasheff sum: `δ_fin (δ_fin (x 0)) = 0` (up to clean casts).
set_option maxHeartbeats 4000000 in
private lemma stasheff_one_term
    (obj : Fin ((1 : ℕ+).val + 1) → BoundedCochainComplex V)
    (deg : Fin (1 : ℕ+).val → ℤ)
    (x : ∀ i : Fin (1 : ℕ+).val, (composableHomType (β := ℤ) (R := R) bccHom obj deg i)) :
    indexedStasheffTerm (β := ℤ) (R := R) (n := (1 : ℕ+)) bccHom
        (fun {n} => bccAInfinityPreCategory.m) obj deg x 0 1 (by norm_num) (by norm_num) = 0 := by
  unfold indexedStasheffTerm
  rw [cast_zero_iff]
  simp only [PNat.one_coe, Nat.add_sub_cancel, bccAInfinityPreCategory]
  erw [LinearMap.compMultilinearMap_apply, degCast_eq_zero_iff]
  simp only [MultilinearMap.coe_mk, Fin.isValue, lt_self_iff_false, dif_neg,
    dif_pos, not_false_eq_true, dite_false]
  refine ((toCochainLinearEquiv (R := R) (obj 0) (obj 1) _).map_eq_zero_iff).mp ?_
  erw [toCochainLinearEquiv_apply, toCochain_δ_fin]
  erw [LinearMap.compMultilinearMap_apply]
  simp only [MultilinearMap.coe_mk, id_eq, eq_mpr_eq_cast, eq_mp_eq_cast, cast_cast, cast_eq]
  erw [toCochain_degCast, toCochain_δ_fin]
  rw [δ_cast_dom]
  exact δ_δ _ _ _ _

set_option maxHeartbeats 4000000 in
lemma stasheff_one
    (obj : Fin ((1 : ℕ+).val + 1) → BoundedCochainComplex V)
    (deg : Fin (1 : ℕ+).val → ℤ)
    (x : ∀ i : Fin (1 : ℕ+).val, (composableHomType (β := ℤ) (R := R) bccHom obj deg i)) :
    indexedStasheffSum (β := ℤ) (R := R) (n := (1 : ℕ+)) bccHom
        (fun {n} ↦ bccAInfinityPreCategory.m) obj deg x = 0 := by
  unfold indexedStasheffSum;
  rw [ Finset.sum_eq_single ⟨ 0, by decide ⟩ ] <;> simp +decide;
  · rw [ Finset.sum_eq_single ⟨ 1, by decide ⟩ ] <;> simp +decide;
    · rw [ stasheff_one_term ]; exact zsmul_zero _;
    · tauto;
  · intro a ha ha'; interval_cases a <;> simp +decide at ha' ⊢;
    convert Finset.sum_empty

-- For n ≥ 3, bccAInfinityPreCategory.m is the zero MultilinearMap (match arm `| _ + 3 => exact 0`).
private lemma bccAInfinityM_zero_of_ge_three {j : ℕ} (hj : 3 ≤ j)
    {obj : Fin (j + 1) → BoundedCochainComplex V} {deg : Fin j → ℤ} :
    bccAInfinityPreCategory.m (R := R) (n := ⟨j, by omega⟩) obj deg = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
  rfl

-- If the outer multilinear map is zero, the entire Stasheff term is zero.
-- Uses abstract hr so the proof term inside indexedStasheffTerm matches exactly after unfolding.
-- The explicit n := ⟨n.val+1-s, ...⟩ is needed because bccAInfinityPreCategory.m can't infer
-- the ℕ+ argument from the types of stasheffObjOut/stasheffDegOut (natural subtraction blocks it).
private lemma indexedStasheffTerm_outer_zero
    {n : ℕ+}
    {obj : Fin (n.val + 1) → BoundedCochainComplex V} {deg : Fin n.val → ℤ}
    {x : ∀ i : Fin n.val, composableHomType (β := ℤ) (R := R) bccHom obj deg i}
    {r s : ℕ} {hs : 1 ≤ s} {hr : r + s ≤ n.val}
    (hm : bccAInfinityPreCategory.m (R := R) (n := ⟨n.val + 1 - s, by omega⟩)
        (stasheffObjOut obj r s hr) (stasheffDegOut deg r s hr) = 0) :
    indexedStasheffTerm (β := ℤ) (R := R) (n := n) bccHom
        (fun {n} => bccAInfinityPreCategory.m) obj deg x r s hs hr = 0 := by
  simp only [indexedStasheffTerm, hm, MultilinearMap.zero_apply]
  exact cast_zero_eq _

-- Collapses a double TYPE-level cast of zero: Eq.mpr h₂ (Eq.mp h₁ 0) = 0,
-- given a ModuleCat R equality between the source and target types.
private lemma cast_zero_of_modcat_eq {R : Type*} [CommRing R] {A B : ModuleCat R}
    (h : A = B) {T_mid : Type*} (h₁ : ↑A = T_mid) (h₂ : ↑B = T_mid) :
    Eq.mpr h₂ (Eq.mp h₁ (0 : ↑A)) = (0 : ↑B) := by
  subst h; subst h₁; cases h₂; rfl

/-
If the inner multilinear map is zero, the Stasheff term is zero (slot r of xOut becomes cast(0)=0).
Uses abstract hr so proof terms match exactly after unfolding indexedStasheffTerm.
-/
set_option maxHeartbeats 800000 in
private lemma indexedStasheffTerm_inner_zero
    {n : ℕ+}
    {obj : Fin (n.val + 1) → BoundedCochainComplex V} {deg : Fin n.val → ℤ}
    {x : ∀ i : Fin n.val, composableHomType (β := ℤ) (R := R) bccHom obj deg i}
    {r s : ℕ} {hs : 1 ≤ s} {hr : r + s ≤ n.val}
    (hm : bccAInfinityPreCategory.m (R := R) (n := ⟨s, by omega⟩)
        (stasheffObjIn obj r s hr) (stasheffDegIn deg r s hr) = 0) :
    indexedStasheffTerm (β := ℤ) (R := R) (n := n) bccHom
        (fun {n} => bccAInfinityPreCategory.m) obj deg x r s hs hr = 0 := by
  apply cast_zero_iff _ |>.mpr;
  convert MultilinearMap.map_coord_zero _ _ _;
  exact ⟨ r, Nat.lt_sub_of_add_lt ( by linarith ) ⟩;
  convert cast_zero_of_modcat_eq _ _ _;
  rotate_left;
  exact operationTargetType bccHom ( stasheffObjIn obj r s hr ) ( stasheffDegIn deg r s hr );
  all_goals norm_num [ operationTargetType, composableHomType ];
  rotate_left;
  exact FinCochain ( stasheffObjIn obj r s hr 0 ) ( stasheffObjIn obj r s hr ( Fin.last s ) ) ( operationTargetDeg ( stasheffDegIn deg r s hr ) );
  · rfl;
  · unfold stasheffObjOut stasheffObjIn stasheffDegOut operationTargetDeg; simp +decide [ Fin.add_def, Nat.mod_eq_of_lt ] ;
    exact pi_congr (congrFun rfl);
  · exact hm.symm ▸ rfl;
  · simp +decide [ stasheffObjIn, stasheffObjOut, stasheffDegIn, stasheffDegOut, operationTargetDeg ];
    congr! 2

/-
Closed form of the `(r=0,s=2)` term in the n=3 Stasheff sum:
`m₂(m₂(x₀,x₁), x₂) = (deg 2).negOnePow • (deg 1).negOnePow • (x₀ ∘ x₁) ∘ x₂`.
-/
set_option maxHeartbeats 4000000 in
private lemma toCochain_stasheff_three_term_02
    (obj : Fin ((3 : ℕ+).val + 1) → BoundedCochainComplex V)
    (deg : Fin (3 : ℕ+).val → ℤ)
    (x : ∀ i : Fin (3 : ℕ+).val, (composableHomType (β := ℤ) (R := R) bccHom obj deg i)) :
    toCochain (indexedStasheffTerm (β := ℤ) (R := R) (n := (3 : ℕ+)) bccHom
        (fun {n} => bccAInfinityPreCategory.m) obj deg x 0 2 (by norm_num) (by norm_num))
      = (deg 2).negOnePow • (deg 1).negOnePow •
          Cochain.comp (Cochain.comp (toCochain (x 0)) (toCochain (x 1)) rfl) (toCochain (x 2))
            ((Fin.sum_univ_three deg).symm.trans (add_zero _).symm :
              (deg 0 + deg 1) + deg 2 = stasheffTargetDeg deg) := by
  unfold indexedStasheffTerm
  erw [ toCochain_bccHom_cast ( stasheffDegOut_sum deg 0 2 ( by norm_num ) ) ];
  erw [ bccM_two_apply ];
  simp +decide [ stasheffDegOut, stasheffDegIn, stasheffInnerDeg, bccOperationTargetDeg_two, bccOperationTargetDeg_one ];
  erw [ toCochain_units_smul ];
  erw [ toCochain_degCast, toCochain_comp, bccM_two_apply ];
  ext p q hpq; simp +decide [ cochain_cast_v, δ_cast_dom ] ;
  congr! 2;
  · have hr1 : 0 + 2 ≤ ((3 : ℕ+) : ℕ) := by norm_num
    refine Eq.trans (Fin.sum_univ_two _) (Eq.trans ?_ (Fin.sum_univ_three deg).symm)
    show operationTargetDeg (stasheffDegIn deg 0 2 hr1) + deg 2 = deg 0 + deg 1 + deg 2
    exact congrArg (· + deg 2) (bccOperationTargetDeg_two (stasheffDegIn deg 0 2 hr1))
  · have le02 : (0 : ℕ) + 2 ≤ ((3 : ℕ+) : ℕ) := by norm_num
    have hin02 : operationTargetDeg (stasheffDegIn deg 0 2 le02) = deg 0 + deg 1 :=
      bccOperationTargetDeg_two _
    have hstar3 : stasheffTargetDeg deg = deg 0 + deg 1 + deg 2 :=
      (show stasheffTargetDeg deg = (∑ i, deg i) + 0 from rfl).trans
        ((add_zero _).trans (Fin.sum_univ_three deg))
    erw [ toCochain_typecast, toCochain_typecast, toCochain_units_smul, toCochain_degCast,
      toCochain_comp ]
    erw [ Cochain.units_smul_comp, cast_units_smul ]
    refine cochain_heq_of_v_eq (by assumption) (fun p q hpq => ?_)
    have hendZ : p + (deg 0 + deg 1) + deg 2 = q :=
      (by ring : p + (deg 0 + deg 1) + deg 2 = p + (deg 0 + deg 1 + deg 2)).trans
        ((congrArg (p + ·) hstar3.symm).trans hpq)
    erw [Cochain.units_smul_v, Cochain.units_smul_v]
    refine congrArg₂ (· • ·) rfl ?_
    refine congrArg₂ (· • ·) rfl ?_
    erw [cochain_cast_v]
    erw [Cochain.comp_v _ _ _ p (p + (deg 0 + deg 1)) q (congrArg (p + ·) hin02) hendZ]
    erw [cochain_cast_v]
    rfl
    all_goals rfl

/-
Closed form of the `(r=1,s=2)` term in the n=3 Stasheff sum:
`m₂(x₀, m₂(x₁,x₂)) = (deg 1 + deg 2).negOnePow • (deg 2).negOnePow • x₀ ∘ (x₁ ∘ x₂)`.
-/
set_option maxHeartbeats 4000000 in
private lemma toCochain_stasheff_three_term_12
    (obj : Fin ((3 : ℕ+).val + 1) → BoundedCochainComplex V)
    (deg : Fin (3 : ℕ+).val → ℤ)
    (x : ∀ i : Fin (3 : ℕ+).val, (composableHomType (β := ℤ) (R := R) bccHom obj deg i)) :
    toCochain (indexedStasheffTerm (β := ℤ) (R := R) (n := (3 : ℕ+)) bccHom
        (fun {n} => bccAInfinityPreCategory.m) obj deg x 1 2 (by norm_num) (by norm_num))
      = (deg 1 + deg 2).negOnePow • (deg 2).negOnePow •
          Cochain.comp (toCochain (x 0)) (Cochain.comp (toCochain (x 1)) (toCochain (x 2)) rfl)
            ((add_assoc (deg 0) (deg 1) (deg 2)).symm.trans
                ((Fin.sum_univ_three deg).symm.trans (add_zero _).symm) :
              deg 0 + (deg 1 + deg 2) = stasheffTargetDeg deg) := by
  unfold indexedStasheffTerm
  erw [ toCochain_bccHom_cast ( stasheffDegOut_sum deg 1 2 ( by norm_num ) ) ];
  erw [ bccM_two_apply ] ; simp +decide [ stasheffDegOut, stasheffInnerDeg, stasheffDegIn, bccOperationTargetDeg_two, bccOperationTargetDeg_one ];
  erw [ toCochain_units_smul, toCochain_degCast, toCochain_comp, toCochain_units_smul, toCochain_degCast, toCochain_comp ];
  ext p q hpq; simp +decide [ cochain_cast_v, δ_cast_dom ] ;
  congr! 2;
  · have hr1 : 1 + 2 ≤ ((3 : ℕ+) : ℕ) := by norm_num
    refine Eq.trans (Fin.sum_univ_two _) (Eq.trans ?_ (Fin.sum_univ_three deg).symm)
    show deg 0 + operationTargetDeg (stasheffDegIn deg 1 2 hr1) = deg 0 + deg 1 + deg 2
    exact (congrArg (deg 0 + ·)
        (bccOperationTargetDeg_two (stasheffDegIn deg 1 2 hr1))).trans
      (show deg 0 + (deg 1 + deg 2) = deg 0 + deg 1 + deg 2 by ring)
  · have le12 : (1 : ℕ) + 2 ≤ ((3 : ℕ+) : ℕ) := by norm_num
    have hin12 : operationTargetDeg (stasheffDegIn deg 1 2 le12) = deg 1 + deg 2 :=
      bccOperationTargetDeg_two _
    have hstar3 : stasheffTargetDeg deg = deg 0 + deg 1 + deg 2 :=
      (show stasheffTargetDeg deg = (∑ i, deg i) + 0 from rfl).trans
        ((add_zero _).trans (Fin.sum_univ_three deg))
    erw [ toCochain_typecast ]
    erw [ Cochain.comp_units_smul, cast_units_smul ]
    refine cochain_heq_of_v_eq (by assumption) (fun p q hpq => ?_)
    have hendZ : p + deg 0 + (deg 1 + deg 2) = q :=
      (by ring : p + deg 0 + (deg 1 + deg 2) = p + (deg 0 + deg 1 + deg 2)).trans
        ((congrArg (p + ·) hstar3.symm).trans hpq)
    have hendY : p + deg 0 + operationTargetDeg (stasheffDegIn deg 1 2 le12) = q := by
      rw [hin12]; exact hendZ
    erw [Cochain.units_smul_v, Cochain.units_smul_v]
    refine congrArg₂ (· • ·) rfl ?_
    refine congrArg₂ (· • ·) rfl ?_
    erw [cochain_cast_v]
    erw [Cochain.comp_v _ _ _ p (p + deg 0) q rfl hendY]
    erw [cochain_cast_v]
    rfl

/-
n=3 Stasheff identity: two non-zero terms (r=0,s=2) and (r=1,s=2) cancel by signed comp_assoc;
four terms with m₃ in inner/outer are zero.
-/
set_option maxHeartbeats 80000000 in
private lemma stasheff_three
    (obj : Fin ((3 : ℕ+).val + 1) → BoundedCochainComplex V)
    (deg : Fin (3 : ℕ+).val → ℤ)
    (x : ∀ i : Fin (3 : ℕ+).val, (composableHomType (β := ℤ) (R := R) bccHom obj deg i)) :
    indexedStasheffSum (β := ℤ) (R := R) (n := (3 : ℕ+)) bccHom
        (fun {n} ↦ bccAInfinityPreCategory.m) obj deg x = 0 := by
  simp +decide [ indexedStasheffSum, Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty ];
  rw [ show ( Finset.attach ( Finset.range 4 ) : Finset { x // x ∈ Finset.range 4 } ) = { ⟨ 0, by decide ⟩, ⟨ 1, by decide ⟩, ⟨ 2, by decide ⟩, ⟨ 3, by decide ⟩ } by decide ] ; simp +decide [ Finset.sum_insert, Finset.sum_singleton ] ;
  erw [ show ( Finset.attach ( Finset.Ico 1 4 ) : Finset { x : ℕ // x ∈ Finset.Ico 1 4 } ) = { ⟨ 1, by decide ⟩, ⟨ 2, by decide ⟩, ⟨ 3, by decide ⟩ } by rfl ] ; simp +decide [ Finset.sum_insert, Finset.sum_singleton ];
  erw [ show ( Finset.attach ( Finset.Ico 1 3 ) : Finset { x : ℕ // x ∈ Finset.Ico 1 3 } ) = { ⟨ 1, by decide ⟩, ⟨ 2, by decide ⟩ } by decide ] ; simp +decide [ Finset.sum_insert, Finset.sum_singleton ];
  erw [ show ( Finset.attach ( Finset.Ico 1 2 ) : Finset { x : ℕ // x ∈ Finset.Ico 1 2 } ) = { ⟨ 1, by decide ⟩ } by decide ] ; simp +decide [ Finset.sum_insert, Finset.sum_singleton ] ;
  rw [ Finset.sum_eq_zero ] <;> try simp +decide [ indexedStasheffTerm_outer_zero, indexedStasheffTerm_inner_zero, bccAInfinityM_zero_of_ge_three ];
  refine ((toCochainLinearEquiv (R := R) (obj 0) (obj (Fin.last 3))
      (stasheffTargetDeg deg)).map_eq_zero_iff).mp ?_
  erw [toCochainLinearEquiv_apply]
  repeat first
    | erw [toCochain_add]
    | erw [toCochain_zsmul]
    | erw [toCochain_zero]
  -- The four terms with an arity-≥3 operation vanish; the conditional simp with the
  -- *_zero lemmas no longer discharges them on 4.30, so rewrite them explicitly
  -- (as ground `simp only` rewrites: simp matches these modulo the embedded proofs,
  -- which `rw`/`erw` no longer do efficiently).
  have hz01 : toCochain (indexedStasheffTerm (β := ℤ) (R := R) (n := (3 : ℕ+)) bccHom
      (fun {n} => bccAInfinityPreCategory.m) obj deg x 0 1 (by norm_num) (by norm_num)) = 0 := by
    rw [indexedStasheffTerm_outer_zero (bccAInfinityM_zero_of_ge_three (by decide))]
    exact toCochain_zero
  have hz03 : toCochain (indexedStasheffTerm (β := ℤ) (R := R) (n := (3 : ℕ+)) bccHom
      (fun {n} => bccAInfinityPreCategory.m) obj deg x 0 3 (by norm_num) (by norm_num)) = 0 := by
    rw [indexedStasheffTerm_inner_zero (bccAInfinityM_zero_of_ge_three (by decide))]
    exact toCochain_zero
  have hz11 : toCochain (indexedStasheffTerm (β := ℤ) (R := R) (n := (3 : ℕ+)) bccHom
      (fun {n} => bccAInfinityPreCategory.m) obj deg x 1 1 (by norm_num) (by norm_num)) = 0 := by
    rw [indexedStasheffTerm_outer_zero (bccAInfinityM_zero_of_ge_three (by decide))]
    exact toCochain_zero
  have hz21 : toCochain (indexedStasheffTerm (β := ℤ) (R := R) (n := (3 : ℕ+)) bccHom
      (fun {n} => bccAInfinityPreCategory.m) obj deg x 2 1 (by norm_num) (by norm_num)) = 0 := by
    rw [indexedStasheffTerm_outer_zero (bccAInfinityM_zero_of_ge_three (by decide))]
    exact toCochain_zero
  -- simp/rw cannot match the goal's terms (their embedded proofs differ), so rewrite the
  -- whole sum by a congruence tree whose leaves unify up to defeq and proof irrelevance.
  refine Eq.trans (congrArg₂ (· + ·)
      (congrArg₂ (· + ·) ((congrArg₂ (· • ·) rfl hz01).trans (zsmul_zero _))
        (congrArg₂ (· + ·)
          (congrArg₂ (· • ·) rfl (toCochain_stasheff_three_term_02 obj deg x))
          ((congrArg₂ (· • ·) rfl hz03).trans (zsmul_zero _))))
      (congrArg₂ (· + ·)
        (congrArg₂ (· + ·) ((congrArg₂ (· • ·) rfl hz11).trans (zsmul_zero _))
          (congrArg₂ (· • ·) rfl (toCochain_stasheff_three_term_12 obj deg x)))
        (congrArg₂ (· + ·) ((congrArg₂ (· • ·) rfl hz21).trans (zsmul_zero _)) rfl))) ?_
  simp only [zero_add, add_zero]
  unfold stasheffSign; simp +decide [ stasheffSignParity ] ;
  erw [ CochainComplex.HomComplex.Cochain.comp_assoc ];
  any_goals rfl;
  any_goals exact ((Fin.sum_univ_three deg).symm.trans (add_zero _).symm);
  all_goals unfold stasheffTargetDeg; simp +decide [ Fin.sum_univ_three ];
  simp +decide [ Grading.sign, Int.negOnePow_add ];
  rcases Int.even_or_odd' ( deg 2 ) with ⟨ k, hk | hk ⟩ <;> simp +decide [ hk, ZMod.val ];
  · -- Quantify over the `deg 2` atom (its numeral form differs invisibly from `hk`'s on
    -- 4.30); the metavariable absorbs the mismatch and `hk` coerces definitionally.
    have key : ∀ {F G : CochainComplex V ℤ} {m : ℤ} (d : ℤ) (u : ℤˣ)
        (C : CochainComplex.HomComplex.Cochain F G m), d = 2 * k →
        (0 : CochainComplex.HomComplex.Cochain F G m) +
            ((-1 : ℤ) ^ (((d : ZMod 2) - 1).val) • (1 : ℤˣ) • u • C + 0) +
          (0 + (1 : ℤ) • u • (1 : ℤˣ) • C + 0) = 0 := by
      intro F G m d u C hd
      subst hd
      rw [show (((2 * k : ℤ) : ZMod 2) - 1).val = 1 from by
        rw [show ((2 * k : ℤ) : ZMod 2) = 0 from by
          push_cast
          rw [show ((2 : ZMod 2)) = 0 from rfl]
          ring]
        decide]
      simp only [zero_add, add_zero, pow_one, one_smul, one_zsmul, neg_smul, neg_zsmul]
      abel
    exact key _ _ _ hk
  · have key : ∀ {F G : CochainComplex V ℤ} {m : ℤ} (d : ℤ) (u : ℤˣ)
        (C : CochainComplex.HomComplex.Cochain F G m), d = 2 * k + 1 →
        (0 : CochainComplex.HomComplex.Cochain F G m) +
            ((-1 : ℤ) ^ (((d : ZMod 2) - 1).val) • (-1 : ℤˣ) • u • C + 0) +
          (0 + (1 : ℤ) • (-u) • (-1 : ℤˣ) • C + 0) = 0 := by
      intro F G m d u C hd
      subst hd
      rw [show (((2 * k + 1 : ℤ) : ZMod 2) - 1).val = 0 from by
        rw [show ((2 * k + 1 : ℤ) : ZMod 2) = 1 from by
          push_cast
          rw [show ((2 : ZMod 2)) = 0 from rfl]
          ring]
        decide]
      simp only [zero_add, add_zero, pow_zero, one_smul, one_zsmul, Units.neg_smul,
        smul_neg, neg_smul, neg_zsmul, neg_neg]
      abel
    exact key _ _ _ hk

-- n≥4 Stasheff identity: every term has either s≥3 (inner m_s=0) or n+1-s≥3 (outer m_{n+1-s}=0).
set_option maxHeartbeats 8000000 in
private lemma stasheff_ge_four (j : ℕ)
    (obj : Fin (j + 5) → BoundedCochainComplex V)
    (deg : Fin (j + 4) → ℤ)
    (x : ∀ i : Fin (j + 4), composableHomType (β := ℤ) (R := R) bccHom obj deg i) :
    indexedStasheffSum (β := ℤ) (R := R) (n := ⟨j + 4, by omega⟩) bccHom
        (fun {n} ↦ bccAInfinityPreCategory.m) obj deg x = 0 := by
  simp only [indexedStasheffSum]
  apply Finset.sum_eq_zero
  intro ⟨r, hr_mem⟩ _
  apply Finset.sum_eq_zero
  intro ⟨s, hs_mem⟩ _
  have hv := validStasheffIndices_of_mem_ranges (n := j + 4) hr_mem hs_mem
  suffices h : indexedStasheffTerm (β := ℤ) (n := ⟨j + 4, by omega⟩) bccHom
      (fun {n} => bccAInfinityPreCategory.m) obj deg x r s hv.1 hv.2 = 0 by
    rw [h, smul_zero]
  by_cases hs3 : s ≤ 2
  · -- Outer arity = (j+4)+1-s ≥ 3, so outer map is zero.
    apply indexedStasheffTerm_outer_zero
    apply bccAInfinityM_zero_of_ge_three
    change 3 ≤ j + 4 + 1 - s
    omega
  · -- Inner arity = s ≥ 3, so inner map is zero.
    push Not at hs3
    exact indexedStasheffTerm_inner_zero (bccAInfinityM_zero_of_ge_three (by omega))

instance : AInfinityCategory (β := ℤ) R (BoundedCochainComplex V) where
  toAInfinityPreCategory := bccAInfinityPreCategory
  stasheff := by
    intro n obj deg x
    obtain ⟨n, hn⟩ := n
    match n with
    | 0 => exact absurd hn (Nat.lt_irrefl 0)
    | 1 =>
      -- Delegate to stasheff_one which uses the literal (1 : ℕ+), avoiding the iota-stuck
      -- coercion ↑⟨1, hn⟩ that appears in this match branch. Lean accepts this via
      -- definitional equality: ⟨1, hn⟩ = 1 : ℕ+ by proof irrelevance (kernel rule).
      exact stasheff_one obj deg x
    | 2 =>
      -- Delegate to stasheff_two (Leibniz rule), same pattern as n=1.
      exact stasheff_two obj deg x
    | k + 3 =>
      -- n ≥ 3: split into n=3 (signed comp_assoc) and n≥4 (all terms zero via m_{≥3}=0).
      match k with
      | 0 => exact stasheff_three obj deg x
      | j + 1 => exact stasheff_ge_four j obj deg x

end AInfinityInstance


/-- Render a bounded cochain complex as its chain of nonzero terms with
degree superscripts and labelled differentials, e.g.
`{T_0 ⊕ T_2}^{(0)} → {T_1}^{(1)}`. -/
instance [Texify V] [∀ (X Y : V), Texify (X ⟶ Y)] :
    Texify (BoundedCochainComplex V) where
  texify c :=
    match c.support.sort (· ≤ ·) with
    | [] => "0"
    | i₀ :: rest =>
      let entry (i : ℤ) : String :=
        s!"{texifyWithBracketsAndParenthesesIfNecessary (c.X i)}^\{({i})}"
      (rest.foldl
        (fun (acc : String × ℤ) (j : ℤ) =>
          (acc.1 ++
            (if j = acc.2 + 1 then
              s!" \\xrightarrow{texifyWithBrackets (c.d acc.2 j)} "
            else
              " \\longrightarrow \\cdots \\longrightarrow ") ++
            entry j, j))
        (entry i₀, i₀)).1
  requiresParentheses := true

end BoundedCochainComplex