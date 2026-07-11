module

public import AInfinity.KLRW
public import AInfinity.AdditiveCompletion
public import AInfinity.BoundedCochainComplex

@[expose] public section

open CategoryTheory AInfinityTheory CochainComplex.HomComplex
open BoundedCochainComplex (FinCochain mOne mTwo mOne_eq mTwo_eq mOne_ofHom)

/-- Tool for addition, allows
operands' types to only be *definitionally* equal. -/
infixl:65 " +≡ " => Add.add


universe u v w
variable {R : Type u} [CommRing R] [CharP R 2] [DecidableEq R] {n : ℕ}
variable [DecidablePred (Limits.IsZero (C := CMat_ (KLRWCategory n R)))]

/-- Over `[CharP R 2]` every Hom-group of the KLRW Hom-complexes is 2-torsion:
componentwise, morphisms are matrices of `DFinsupp`s valued in `R`. This is what
lets the sign-free `FinCochain`-language statements agree with the Koszul-signed
A∞ ones (see `BraidingFunctorData.sf₃_fin`). -/
theorem finCochain_neg_eq_self {X Y : BoundedCochainComplex (CMat_ (KLRWCategory n R))}
    {m : ℤ} (w : FinCochain X Y m) : -w = w := by
  funext p i j
  refine DFinsupp.ext fun k => ?_
  exact (DFinsupp.neg_apply _ _).trans (CharTwo.neg_eq _)

/--
β.gen as written in the blueprint.
-/
structure BraidingFunctorData (R : Type u) [CommRing R] [CharP R 2] [DecidableEq R] (n : ℕ)
    [DecidablePred (Limits.IsZero (C := CMat_ (KLRWCategory n R)))] where
  gen₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R))
  gen₁ : {A B : KLRWCategory n R} → (A ⟶ B) → (gen₀ A ⟶ gen₀ B)
  gen₂ : {A B C : KLRWCategory n R} → (A ⟶ B) → (B ⟶ C) →
    FinCochain (gen₀ A) (gen₀ C) (-1)

  -- [SF₁.gen]: 0 = μ₁^B(β₁(f))
  sf₁ : ∀ {A B : KLRWCategory n R} (f : A ⟶ B),
    mOne (R := R) (show (0 : ℤ) + 1 = 1 from rfl) (FinCochain.ofHom (gen₁ f)) = 0

  -- [SF₂.gen]: β₁(μ₂^A(f, g)) = μ₂^B(β₁(f), β₁(g)) + μ₁^B(β₂(f, g))
  sf₂ : ∀ {A B C : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C),
    FinCochain.ofHom (gen₁ (f ≫ g)) =
      mTwo (R := R) (show (0 : ℤ) + 0 = 0 from rfl)
          (FinCochain.ofHom (gen₁ f)) (FinCochain.ofHom (gen₁ g)) +
        mOne (R := R) (show (-1 : ℤ) + 1 = 0 from rfl) (gen₂ f g)

  -- [SF₃.gen]: β₂(f, μ₂^A(g, h)) + β₂(μ₂^A(f, g), h)
  sf₃ : ∀ {A B C D : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D),
    gen₂ f (g ≫ h) + gen₂ (f ≫ g) h =
      mTwo (R := R) (show (0 : ℤ) + -1 = -1 from rfl)
          (FinCochain.ofHom (gen₁ f)) (gen₂ g h) +
        mTwo (R := R) (show (-1 : ℤ) + 0 = -1 from rfl)
          (gen₂ f g) (FinCochain.ofHom (gen₁ h))

  -- [SF₄.gen]: 0 = μ₂^B(β₂(f, g), β₂(h, k))
  sf₄ : ∀ {A B C D E : KLRWCategory n R}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E),
    mTwo (R := R) (show (-1 : ℤ) + -1 = -2 from rfl) (gen₂ f g) (gen₂ h k) = 0

namespace BraidingFunctorData

variable (β : BraidingFunctorData R n)

/-! ### The axioms in differential / `FinCochain` language

The `[SFᵢ]` fields are stated via the A∞ operations "mOne"/"mTwo",
so they are here translated into the language of Hom-complex differential
"δ_fin" and composition ("comp"/"zeroComp"/"compZero").

Notice that we are working still in ring of char 2

-/

theorem sf₁_fin {A B : KLRWCategory n R} (f : A ⟶ B) :
    (FinCochain.ofHom (β.gen₁ f)).δ_fin =
      (0 : FinCochain (β.gen₀ A) (β.gen₀ B) (0 + 1)) :=
  BoundedCochainComplex.FinCochain.δ_fin_ofHom (β.gen₁ f)

theorem sf₂_fin {A B C : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) :
    FinCochain.ofHom (β.gen₁ (f ≫ g)) =
      (FinCochain.ofHom (β.gen₁ f)).comp (FinCochain.ofHom (β.gen₁ g)) +≡
        (β.gen₂ f g).δ_fin := by
  have h := β.sf₂ f g
  rw [mTwo_eq, mOne_eq] at h
  simpa [Int.negOnePow_zero] using h

theorem sf₃_fin {A B C D : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    β.gen₂ f (g ≫ h) + β.gen₂ (f ≫ g) h =
      FinCochain.zeroComp (FinCochain.ofHom (β.gen₁ f)) (β.gen₂ g h) +
        FinCochain.compZero (β.gen₂ f g) (FinCochain.ofHom (β.gen₁ h)) := by
  have hsf := β.sf₃ f g h
  rw [mTwo_eq, mTwo_eq] at hsf
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Int.negOnePow_zero, one_smul,
    Units.neg_smul, finCochain_neg_eq_self] at hsf
  exact hsf

/-- `[SF₄]` in `FinCochain` language. (Sign-free over any ring: the sign is
absorbed by the vanishing right-hand side.) -/
theorem sf₄_fin {A B C D E : KLRWCategory n R}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E) :
    (β.gen₂ f g).comp (β.gen₂ h k) = 0 := by
  have hsf := β.sf₄ f g h k
  rw [mTwo_eq] at hsf
  simpa using hsf

structure BraidingFunctorAdd (R : Type u) [CommRing R] [CharP R 2]
[DecidableEq R] (n : ℕ) [DecidablePred (Limits.IsZero (C := CMat_ (KLRWCategory n R)))] where
  add₀ : CMat_ (KLRWCategory n R) → BoundedCochainComplex (CMat_ (KLRWCategory n R))
  add₁ : {A B : CMat_ (KLRWCategory n R)} → (A ⟶ B) → (add₀ A ⟶ add₀ B)
  add₂ : {A B C : CMat_ (KLRWCategory n R)} → (A ⟶ B) → (B ⟶ C) →
    FinCochain (add₀ A) (add₀ C) (-1)

structure BraidingFunctorFull (R : Type u) [CommRing R] [CharP R 2]
[DecidableEq R] (n : ℕ) [DecidablePred (Limits.IsZero (C := CMat_ (KLRWCategory n R)))] where
  full₀ : BoundedCochainComplex (CMat_ (KLRWCategory n R)) → BoundedCochainComplex (CMat_ (KLRWCategory n R))
  full₁ : {A B : BoundedCochainComplex (CMat_ (KLRWCategory n R))} → (A ⟶ B) → (full₀ A ⟶ full₀ B)
  full₂ : {A B C : BoundedCochainComplex (CMat_ (KLRWCategory n R))} → (A ⟶ B) → (B ⟶ C) →
    FinCochain (full₀ A) (full₀ C) (-1)

-- Transposition braiding data starts here
def isInterior (k : Fin (n + 1)) : Bool :=
  0 < k.1 ∧ k.1 < n

def specialPosition (A : KLRWCategory n R) (k : Fin (n + 1)) : Bool :=
  A.positioning == k

lemma isInterior_spec {k : Fin (n + 1)} (hk : isInterior (n := n) k = true) :
    0 < k.1 ∧ k.1 < n := by
  simpa [isInterior] using hk

def leftNeighbor (k : Fin (n + 1)) (hk : isInterior (n := n) k = true) : KLRWCategory n R :=
  ⟨⟨k.1 - 1, by
    have hk' := isInterior_spec (n := n) hk
    omega⟩⟩

def rightNeighbor (k : Fin (n + 1)) (hk : isInterior (n := n) k = true) : KLRWCategory n R :=
  ⟨⟨k.1 + 1, by
    have hk' := isInterior_spec (n := n) hk
    omega⟩⟩

noncomputable def asCC (A : KLRWCategory n R) : CochainComplex (CMat_ (KLRWCategory n R)) ℤ :=
  (CochainComplex.singleFunctor (CMat_ (KLRWCategory n R)) 0).obj [A]ₘ
--returns A as a chain complex with only nonzero degree being 0 which is [A]_m
--differential should be 0

def specialDifferential (A : KLRWCategory n R) (k : Fin (n + 1)) (hk : isInterior k = true) :
    [leftNeighbor (R := R) k hk, rightNeighbor (R := R) k hk]ₘ ⟶ [A]ₘ :=
  fun _ _ => StrandSpace.dots R 1

def specialCaseObj (A : KLRWCategory n R) (k : Fin (n + 1)) (hk : isInterior k = true) :
    CochainComplex (CMat_ (KLRWCategory n R)) ℤ :=
  { X := fun i =>
      match i with
      | 0 => [leftNeighbor (R := R) k hk, rightNeighbor (R := R) k hk]ₘ
      | 1 => [A]ₘ
      | _ => 𝟎
    d := fun i j =>
      if hij : i = 0 ∧ j = 1 then
        by
          rcases hij with ⟨rfl, rfl⟩
          exact specialDifferential (R := R) A k hk
      else
        0 --only non-zero morphism should be between 0 and 1, pair of maps with N=1
    shape := by
      intro i j hij
      by_cases h01 : i = 0 ∧ j = 1
      · exfalso
        rcases h01 with ⟨rfl, rfl⟩
        exact hij (by simp [ComplexShape.up, ComplexShape.up'])
      · simp [h01]
    d_comp_d' := by
      intro i j l hij hjl
      by_cases h01 : i = 0 ∧ j = 1
      · rcases h01 with ⟨rfl, rfl⟩
        rw [dif_pos (by simp)]
        split_ifs with h
        · rcases h with ⟨h₁, _⟩
          simp at h₁
        · exact Limits.comp_zero
      · rw [dif_neg h01]
        split_ifs with h
        · exact Limits.zero_comp
        · exact Limits.zero_comp }

def shiftStrands (f : StrandSpace R) : StrandSpace R :=
  f.sum (fun i r => r • StrandSpace.dots R (i + 1))

def singletonMap {A B : KLRWCategory n R} (f : A ⟶ B) : [A]ₘ ⟶ [B]ₘ :=
  fun _ _ => f

def diagonalNeighborMap {A B : KLRWCategory n R} (f : A ⟶ B) :
    [A, B]ₘ ⟶ [A, B]ₘ :=
  fun i j => if i.toFin = j.toFin then f else 0

def leftToSingletonMap {A B C : KLRWCategory n R} (f : A ⟶ C) : [A, B]ₘ ⟶ [C]ₘ :=
  fun i _ => if i.toFin.1 = 0 then f else 0

def rightToSingletonMap {A B C : KLRWCategory n R} (f : B ⟶ C) : [A, B]ₘ ⟶ [C]ₘ :=
  fun i _ => if i.toFin.1 = 1 then f else 0

def singletonToNeighborsMap {A B C : KLRWCategory n R} (fLeft fRight : A ⟶ B) :
    [A]ₘ ⟶ [B, C]ₘ :=
  fun _ j => if j.toFin.1 = 0 then fLeft else fRight

def specialSpecialMor {A B : KLRWCategory n R} (f : A ⟶ B) (k : Fin (n + 1))
    (hk : isInterior k = true) :
    specialCaseObj (R := R) A k hk ⟶ specialCaseObj (R := R) B k hk :=
  { f := fun i =>
      match i with
      | 0 =>
          diagonalNeighborMap
            (A := leftNeighbor (R := R) k hk) (B := rightNeighbor (R := R) k hk) f
      | 1 => singletonMap f
      | _ => 0
    comm' := sorry
    }

def specialToGeneralMor {A B : KLRWCategory n R} (f : A ⟶ B) (k : Fin (n + 1))
    (hk : isInterior k = true) :
    specialCaseObj (R := R) A k hk ⟶ asCC B :=
  { f := fun i =>
      match i with
      | 0 =>
          if h : B.positioning.1 < A.positioning.1 then
            leftToSingletonMap
              (A := leftNeighbor (R := R) k hk) (B := rightNeighbor (R := R) k hk) f
          else
            rightToSingletonMap
              (A := leftNeighbor (R := R) k hk) (B := rightNeighbor (R := R) k hk) f
      | _ => 0
    comm' := sorry
        }

def generalToSpecialMor {A B : KLRWCategory n R} (f : A ⟶ B) (k : Fin (n + 1))
    (hk : isInterior k = true) :
    asCC A ⟶ specialCaseObj (R := R) B k hk :=
  { f := fun i =>
      match i with
      | 0 =>
          if h : B.positioning.1 < A.positioning.1 then
            singletonToNeighborsMap
              (A := A) (B := leftNeighbor (R := R) k hk) (C := rightNeighbor (R := R) k hk)
              f (shiftStrands (R := R) f)
          else
            singletonToNeighborsMap
              (A := A) (B := leftNeighbor (R := R) k hk) (C := rightNeighbor (R := R) k hk)
              (shiftStrands (R := R) f) f
      | _ => 0
    comm' := sorry
    }

noncomputable def generalGeneralMor {A B : KLRWCategory n R} (f : A ⟶ B) :
    asCC A ⟶ asCC B :=
  (CochainComplex.singleFunctor (CMat_ (KLRWCategory n R)) 0).map (singletonMap f)

noncomputable def transpositionObj (k : Fin (n + 1)) (A : KLRWCategory n R) :
    CochainComplex (CMat_ (KLRWCategory n R)) ℤ := by
  if hk : isInterior k = true then
    if hA : specialPosition A k = true then
      exact specialCaseObj A k hk
    else
      exact asCC A
  else
    exact asCC A

noncomputable def transpositionMor (k : Fin (n + 1)) {A B : KLRWCategory n R} (f : A ⟶ B) :
    transpositionObj (R := R) k A ⟶ transpositionObj (R := R) k B := by
  match hA : specialPosition A k, hB : specialPosition B k, hk : isInterior k with
  | true, true, true =>
      simpa [transpositionObj, hA, hB, hk] using specialSpecialMor (R := R) f k hk
  | true, false, true =>
      simpa [transpositionObj, hA, hB, hk] using specialToGeneralMor (R := R) f k hk
  | false, true, true =>
      simpa [transpositionObj, hA, hB, hk] using generalToSpecialMor (R := R) f k hk
  | false, false, true =>
      simpa [transpositionObj, hA, hB, hk] using generalGeneralMor (R := R) f
  | _, _, false =>
      simpa [transpositionObj, hk] using generalGeneralMor (R := R) f


noncomputable def PositiveTransposition (k : Fin (n + 1)) : BraidingFunctorData R n where
  gen₀ := fun A => BoundedCochainComplex.mkOfBounded (transpositionObj (R := R) k A)
      (supersetOfSupport := {0, 1}) (by sorry)
  gen₁ := fun {A B} f => BoundedCochainComplex.homMk (transpositionMor (R := R) k f)
  gen₂ := fun {A B C} _f _g => sorry
  sf₁ := fun _f => BoundedCochainComplex.mOne_ofHom _ _
  sf₂ := sorry
  sf₃ := sorry
  sf₄ := sorry
