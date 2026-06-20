module

public import AInfinity.KLRW
public import AInfinity.AdditiveCompletion
public import AInfinity.BoundedCochainComplex

@[expose] public section

open CategoryTheory AInfinityTheory CochainComplex.HomComplex


universe u v w
variable {R : Type u} [CommRing R] [CharP R 2] [DecidableEq R] {n : ℕ}
variable [DecidablePred (Limits.IsZero (C := CMat_ (KLRWCategory n R)))]

structure BraidingFunctorData (R : Type u) [CommRing R] [CharP R 2] [DecidableEq R] (n : ℕ)
    [DecidablePred (Limits.IsZero (C := CMat_ (KLRWCategory n R)))] where
  gen₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R))
  gen₁ : {A B : KLRWCategory n R} → (A ⟶ B) → (gen₀ A ⟶ gen₀ B)
  gen₂ : {A B C : KLRWCategory n R} → (A ⟶ B) → (B ⟶ C) →
    ((BoundedCochainComplex.shiftFunctor 1).obj (gen₀ A) ⟶ gen₀ C)
  /-
  --SFₙ axioms. Note:
  --KLRW is a preadditive category, so its Hom-space is
  --all degree 0. Then only μ₂ is nonzero (it is composition).
  --Tw(Add(KLRW)) is a dg-category, so it has μ₁ = d, μ₂ = composition,
  --and no higher terms.

  -- [SF₁.gen]: gen₁(f) is a chain map, i.e. 0 = μ₁^B(gen₁(f)).
  -- Concretely: 0 = (gen₁ f)ᵢ ≫ d^i_{gen₀B} + d^i_{gen₀A} ≫ (gen₁ f)_{i+1}
  sf₁ : ∀ {A B : KLRWCategory n R} (f : A ⟶ B) (i : ℤ),
    (0 : (gen₀ A).X i ⟶ (gen₀ B).X (i + 1)) =
    (gen₁ f).f i ≫ (gen₀ B).d i (i + 1) +
    (gen₀ A).d i (i + 1) ≫ (gen₁ f).f (i + 1)

  -- [SF₂.gen]: β₁(μ₂^A(f, g)) = μ₂^B(β₁(f), β₁(g)) + μ₁^B(β₂(f, g))
  -- (gen₂ f g).f i : (gen₀ A).X (i+1) ⟶ (gen₀ C).X i
  -- μ₁^B(gen₂ f g) at degree (i+1):
  --   d^A_{i+1,i+2} ≫ (gen₂ f g).f (i+1)  :  X_A(i+1) ⟶ X_C(i+1)
  --   (gen₂ f g).f i ≫ d^C_{i,i+1}         :  X_A(i+1) ⟶ X_C(i+1)
  sf₂ : ∀ {A B C : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (i : ℤ),
    (gen₁ (f ≫ g)).f (i + 1) =
    (gen₁ f).f (i + 1) ≫ (gen₁ g).f (i + 1) +
    ((gen₀ A).d (i + 1) (i + 2) ≫ (gen₂ f g).f (i + 1) +
     (gen₂ f g).f i ≫ (gen₀ C).d i (i + 1))

  -- [SF₃.gen]: β₂(f, μ₂^A(g, h)) + β₂(μ₂^A(f, g), h) = μ₂^B(β₁(f), β₂(g, h)) + μ₂^B(β₂(f, g), β₁(h))
  -- (gen₁ f).f (i+1) ≫ (gen₂ g h).f i : (gen₀ A).X (i+1) ⟶ (gen₀ D).X i
  -- (gen₂ f g).f i ≫ (gen₁ h).f i     : (gen₀ A).X (i+1) ⟶ (gen₀ D).X i
  sf₃ : ∀ {A B C D : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (i : ℤ),
    (gen₂ f (g ≫ h)).f i + (gen₂ (f ≫ g) h).f i =
    (gen₁ f).f (i + 1) ≫ (gen₂ g h).f i +
    (gen₂ f g).f i ≫ (gen₁ h).f i

  -- [SF₄.gen]: 0 = μ₂^B(β₂(f, g), β₂(h, k))
  -- (shiftFunctor 1).map (gen₂ f g) : (shiftFunctor 1)² (gen₀ A) ⟶ (shiftFunctor 1) (gen₀ C)
  sf₄ : ∀ {A B C D E : KLRWCategory n R}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E),
    (BoundedCochainComplex.shiftFunctor 1).map (gen₂ f g) ≫ gen₂ h k = 0 -/

namespace BraidingFunctorData

variable (β : BraidingFunctorData R n)

structure BraidingFunctorAdd (R : Type u) [CommRing R] [CharP R 2]
[DecidableEq R] (n : ℕ) [DecidablePred (Limits.IsZero (C := CMat_ (KLRWCategory n R)))] where
  add₀ : CMat_ (KLRWCategory n R) → BoundedCochainComplex (CMat_ (KLRWCategory n R))
  add₁ : {A B : CMat_ (KLRWCategory n R)} → (A ⟶ B) → (add₀ A ⟶ add₀ B)
  add₂ : {A B C : CMat_ (KLRWCategory n R)} → (A ⟶ B) → (B ⟶ C) →
    ((BoundedCochainComplex.shiftFunctor 1).obj (add₀ A) ⟶ add₀ C)

structure BraidingFunctorFull (R : Type u) [CommRing R] [CharP R 2]
[DecidableEq R] (n : ℕ) [DecidablePred (Limits.IsZero (C := CMat_ (KLRWCategory n R)))] where
  full₀ : BoundedCochainComplex (CMat_ (KLRWCategory n R)) → BoundedCochainComplex (CMat_ (KLRWCategory n R))
  full₁ : {A B : BoundedCochainComplex (CMat_ (KLRWCategory n R))} → (A ⟶ B) → (full₀ A ⟶ full₀ B)
  full₂ : {A B C : BoundedCochainComplex (CMat_ (KLRWCategory n R))} → (A ⟶ B) → (B ⟶ C) →
    ((BoundedCochainComplex.shiftFunctor 1).obj (full₀ A) ⟶ full₀ C)

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
  gen₀ := transpositionObj (R := R) k
  gen₁ := fun {A B} f => transpositionMor (R := R) k f
  gen₂ := fun f g i x =>
    sorry -- gen_2 does not seem to be defined as the correct type
  SF₂ := sorry
  SF₃ := sorry
  SF₄ := sorry
