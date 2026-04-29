module

public import Mathlib
public import AInfinity.KLRW
public import AInfinity.AdditiveCompletion

@[expose] public section

open CategoryTheory AInfinityTheory

universe u v w
variable {R : Type u} [CommRing R] [CharP R 2] [DecidableEq R] {n : ℕ}

structure BraidingFunctorData (R : Type u) [CommRing R] [CharP R 2] [DecidableEq R] (n : ℕ) where
  gen₀ : KLRWCategory n R → CochainComplex (CMat_ (KLRWCategory n R)) ℤ
  gen₁ : {A B : KLRWCategory n R} → (A ⟶ B) → (gen₀ A ⟶ gen₀ B)
  gen₂ : {A B C : KLRWCategory n R} → (A ⟶ B) → (B ⟶ C) →
    ∀ (i : ℤ), (gen₀ A).X i ⟶ (gen₀ C).X (i - 1)
  -- invoke shift functor from boundedcochaincomplexes

  --SFₙ axioms. Note:
  --KLRW is a preadditive category, so its Hom-space is
  --all degree 0. Then only μ₂ is nonzero (it is composition).
  --Tw(Add(KLRW)) is a dg-category, so it has μ₁ = d, μ₂ = composition,
  --and no higher terms.
  SF₂ : ∀ {A B C : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (i : ℤ),
    (gen₁ (f ≫ g)).f i + (gen₁ f ≫ gen₁ g).f i
      = gen₂ f g i ≫ (gen₀ C).d (i - 1) i
        + (gen₀ A).d i (i + 1) ≫ gen₂ f g (i + 1) ≫
          eqToHom (by
            have h : i + 1 - 1 = i := by omega
            rw [h])
  SF₃ : ∀ {A B C D : KLRWCategory n R}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (i : ℤ),
    gen₂ (f ≫ g) h i + gen₂ f (g ≫ h) i
      = (gen₁ f).f i ≫ gen₂ g h i
        + gen₂ f g i ≫ (gen₁ h).f (i - 1)
  SF₄ : ∀ {A B C D E : KLRWCategory n R}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E) (i : ℤ),
    gen₂ f g i ≫ gen₂ h k (i - 1) = 0
namespace BraidingFunctorData

variable (β : BraidingFunctorData R n)

def add₀ (A : CMat_ (KLRWCategory n R))
  : CochainComplex (CMat_ (KLRWCategory n R)) ℤ :=
  -- Idea: Use CochainComplex.singleFunctor
  let _ := β -- To get β to become a parameter of this until we actually implement it
  sorry

def add₁ {A B : CMat_ (KLRWCategory n R)} (f : A ⟶ B)
  -- Idea: Use the action of CochainComplex.singleFunctor on maps
  : β.add₀ A ⟶ β.add₀ B := sorry

def add₂ {A B C : CMat_ (KLRWCategory n R)} (f : A ⟶ B) (g : B ⟶ C)
  : ∀ i : ℤ, (β.add₀ A).X i ⟶ (β.add₀ C).X (i - 1) := sorry

/-- The `Add(Add(KLRW))` object on the `k`th diagonal of the lattice in the PDF.

The finite list `outerDegrees` records the degrees of the source complex that are included in
the diagonal. When the source is later changed to `BoundedCochainComplex`, this should be the
bounded support list. -/
def halfFullObj (outerDegrees : List ℤ)
    (A : CochainComplex (CMat_ (KLRWCategory n R)) ℤ) (k : ℤ) :
    CMat_ (CMat_ (KLRWCategory n R)) :=
  CMat_.ofList (outerDegrees.map fun i => (β.add₀ (A.X i)).X (k - i))

/-- Recover the source-complex degree represented by an index in a diagonal object. -/
def halfFullOuterDegree (outerDegrees : List ℤ)
    {A : CochainComplex (CMat_ (KLRWCategory n R)) ℤ} {k : ℤ}
    (a : (β.halfFullObj outerDegrees A k).ι) : ℤ :=
  outerDegrees.get ⟨a.toFin.val, by
    simpa [halfFullObj] using a.toFin.isLt⟩

lemma halfFullObj_X (outerDegrees : List ℤ)
    {A : CochainComplex (CMat_ (KLRWCategory n R)) ℤ} {k : ℤ}
    (a : (β.halfFullObj outerDegrees A k).ι) :
    (β.halfFullObj outerDegrees A k).X a =
      (β.add₀ (A.X (β.halfFullOuterDegree outerDegrees a))).X
        (k - β.halfFullOuterDegree outerDegrees a) := by
  unfold halfFullObj halfFullOuterDegree CMat_.X
  simp only [Fin.getElem_fin, List.getElem_map]
  congr

/-- A single block of the `halfFull₀` differential.

For a source outer degree `p` and target outer degree `q`, this is the diagonal block `f`,
the first lower off-diagonal block `g`, the second lower off-diagonal block `h`, or zero. -/
def halfFullDCore
    (A : CochainComplex (CMat_ (KLRWCategory n R)) ℤ) (k p q : ℤ) :
    (β.add₀ (A.X p)).X (k - p) ⟶ (β.add₀ (A.X q)).X (k + 1 - q) := by
  by_cases h₀ : q = p
  · subst q
    exact (β.add₀ (A.X p)).d (k - p) (k + 1 - p)
  by_cases h₁ : q = p + 1
  · subst q
    let e : k - p = k + 1 - (p + 1) := by omega
    exact (β.add₁ (A.d p (p + 1))).f (k - p) ≫ eqToHom (by rw [e])
  by_cases h₂ : q = p + 2
  · subst q
    let e : k - p - 1 = k + 1 - (p + 2) := by omega
    exact β.add₂ (A.d p (p + 1)) (A.d (p + 1) (p + 2)) (k - p) ≫
      eqToHom (by rw [e])
  exact 0

/-- The block-matrix differential on the diagonal object. -/
def halfFullD (outerDegrees : List ℤ)
    (A : CochainComplex (CMat_ (KLRWCategory n R)) ℤ) (k : ℤ) :
    β.halfFullObj outerDegrees A k ⟶ β.halfFullObj outerDegrees A (k + 1) :=
  fun a b =>
    eqToHom (β.halfFullObj_X outerDegrees a) ≫
      β.halfFullDCore A k
        (β.halfFullOuterDegree outerDegrees a)
        (β.halfFullOuterDegree outerDegrees b) ≫
      eqToHom (β.halfFullObj_X outerDegrees b).symm

/-- The computable intermediate `full₀` construction from the PDF.

This lands in complexes over `Add(Add(KLRW))`: the objects are diagonal lists, and the
differential is the lower-triangular block matrix whose bands are the internal differentials,
the `β₁.add` maps, and the `β₂.add` corrections. -/
def halfFull₀ (outerDegrees : List ℤ)
    (A : CochainComplex (CMat_ (KLRWCategory n R)) ℤ) :
    CochainComplex (CMat_ (CMat_ (KLRWCategory n R))) ℤ :=
  CochainComplex.of
    (fun k => β.halfFullObj outerDegrees A k)
    (fun k => β.halfFullD outerDegrees A k)
    (fun _ => by
      -- This is exactly the matrix identity from the PDF:
      -- f² = 0, fg + gf = 0, fh + g² + hf = 0, gh + hg = 0, h² = 0.
      -- The first two are the internal differential and chain-map laws; the last three are
      -- supplied by the A∞ relations on `β`.
      sorry)

/-- ASCII alias for users who type `halfFull0` instead of `halfFull₀`. -/
abbrev halfFull0 (outerDegrees : List ℤ)
    (A : CochainComplex (CMat_ (KLRWCategory n R)) ℤ) :
    CochainComplex (CMat_ (CMat_ (KLRWCategory n R))) ℤ :=
  β.halfFull₀ outerDegrees A

def full₀ (A : CochainComplex (CMat_ (KLRWCategory n R)) ℤ)
  : CochainComplex (CMat_ (KLRWCategory n R)) ℤ :=
  let _ := β -- To get β to become a parameter of this until we actually implement it
  sorry

def full₁ {A B : CochainComplex (CMat_ (KLRWCategory n R)) ℤ} (f : A ⟶ B)
  : β.full₀ A ⟶ β.full₀ B := sorry

def full₂ {A B C : CochainComplex (CMat_ (KLRWCategory n R)) ℤ}
  (f : A ⟶ B) (g : B ⟶ C) :
  ∀ i : ℤ, (β.full₀ A).X i ⟶ (β.full₀ C).X (i - 1) := sorry
