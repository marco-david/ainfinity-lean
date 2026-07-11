module

public import AInfinity.KLRW
public import AInfinity.AdditiveCompletion
public import AInfinity.BoundedCochainComplex

@[expose] public section

open CategoryTheory AInfinityTheory CochainComplex.HomComplex
open BoundedCochainComplex (FinCochain)

/-- Addition whose operands' types need only be *definitionally* equal.

`+` is elaborated by `binop%`, which reconciles the operands' types at reducible
transparency only, so it rejects e.g. `FinCochain A B (0 + 0)` next to
`FinCochain A B (-1 + 1)`. This notation expands to a plain `Add.add`
application instead: the carrier is unified with the expected type and each
operand is checked by full definitional unification, where the degree
arithmetic reduces. -/
infixl:65 " +≡ " => Add.add


universe u v w
variable {R : Type u} [CommRing R] [CharP R 2] [DecidableEq R] {n : ℕ}
variable [DecidablePred (Limits.IsZero (C := CMat_ (KLRWCategory n R)))]

/--
The data of an `A∞`-morphism from `KLRW` (viewed as a degenerate `A∞`-category:
Hom-spaces concentrated in degree `0`, `μ₁ = 0`, `μ₂ =` composition, `μₙ = 0` for
`n ≥ 3`) to the dg-category `K^•(Add KLRW)` of bounded cochain complexes
(`μ₁ = δ_fin`, `μ₂ =` composition, `μₙ = 0` for `n ≥ 3`), truncated at level 2:
the components `βₙ` for `n ≥ 3` vanish, so the general `[SFₙ]` axioms reduce to
the finite list `[SF₁]`–`[SF₄]` below.

* `gen₁ f` is a genuine chain map, so `[SF₁]` (`μ₁(β₁ f) = 0`) is automatic from
  its typing: the field `sf₁` is discharged by `FinCochain.δ_fin_ofHom` for any
  choice of the data.
* `gen₂ f g` is a *raw* degree `-1` element of the Hom-complex
  (`FinCochain (gen₀ A) (gen₀ C) (-1)`), NOT a chain map out of the shift: its
  `μ₁`-differential is exactly the failure of `gen₁` to be strictly functorial,
  as recorded by `[SF₂]`.

The axioms are stated without Koszul signs; over `[CharP R 2]` this agrees with
the signed specialization of the general `[SFₙ]` equations.
-/
structure BraidingFunctorData (R : Type u) [CommRing R] [CharP R 2] [DecidableEq R] (n : ℕ)
    [DecidablePred (Limits.IsZero (C := CMat_ (KLRWCategory n R)))] where
  gen₀ : KLRWCategory n R → BoundedCochainComplex (CMat_ (KLRWCategory n R))
  gen₁ : {A B : KLRWCategory n R} → (A ⟶ B) → (gen₀ A ⟶ gen₀ B)
  gen₂ : {A B C : KLRWCategory n R} → (A ⟶ B) → (B ⟶ C) →
    FinCochain (gen₀ A) (gen₀ C) (-1)

  -- [SF₁.gen]: 0 = μ₁^B(β₁(f)) — `gen₁ f` is a `δ_fin`-cycle, an equation in
  -- the degree-1 Hom-space. Automatic from the chain-map typing of `gen₁`:
  -- discharge with `fun f => FinCochain.δ_fin_ofHom _`.
  sf₁ : ∀ {A B : KLRWCategory n R} (f : A ⟶ B),
    (FinCochain.ofHom (gen₁ f)).δ_fin =
      (0 : FinCochain (gen₀ A) (gen₀ B) (0 + 1))

  -- [SF₂.gen]: β₁(μ₂^A(f, g)) = μ₂^B(β₁(f), β₁(g)) + μ₁^B(β₂(f, g)),
  -- an equation in the degree-0 Hom-space `FinCochain (gen₀ A) (gen₀ C) 0`.
  -- (`+≡` rather than `+`: the summands' degrees `0 + 0` and `-1 + 1` are
  -- definitionally but not syntactically `0`.)
  sf₂ : ∀ {A B C : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C),
    FinCochain.ofHom (gen₁ (f ≫ g)) =
      (FinCochain.ofHom (gen₁ f)).comp (FinCochain.ofHom (gen₁ g)) +≡
        (gen₂ f g).δ_fin

  -- [SF₃.gen]: β₂(f, μ₂^A(g, h)) + β₂(μ₂^A(f, g), h)
  --              = μ₂^B(β₁(f), β₂(g, h)) + μ₂^B(β₂(f, g), β₁(h)),
  -- an equation in the degree-(-1) Hom-space `FinCochain (gen₀ A) (gen₀ D) (-1)`.
  sf₃ : ∀ {A B C D : KLRWCategory n R} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D),
    gen₂ f (g ≫ h) + gen₂ (f ≫ g) h =
      FinCochain.zeroComp (FinCochain.ofHom (gen₁ f)) (gen₂ g h) +
        FinCochain.compZero (gen₂ f g) (FinCochain.ofHom (gen₁ h))

  -- [SF₄.gen]: 0 = μ₂^B(β₂(f, g), β₂(h, k)),
  -- an equation in the degree-(-2) Hom-space.
  sf₄ : ∀ {A B C D E : KLRWCategory n R}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E),
    (gen₂ f g).comp (gen₂ h k) = 0

namespace BraidingFunctorData

variable (β : BraidingFunctorData R n)

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
  sf₁ := fun _f => BoundedCochainComplex.FinCochain.δ_fin_ofHom _
  sf₂ := sorry
  sf₃ := sorry
  sf₄ := sorry
