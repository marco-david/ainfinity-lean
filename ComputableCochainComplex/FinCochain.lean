module

public import Mathlib
public import ComputableCochainComplex.BoundedCochainComplex

/-! # Computable cochains between bounded cochain complexes

For bounded cochain complexes `A` and `B` in `V`, a degree-`n` cochain `A ⟶ B` in the sense of
`CochainComplex.HomComplex.Cochain` consists of morphisms `A.X p ⟶ B.X (p + n)` for every `p : ℤ`,
almost all of which are forced to vanish because `A.X p` or `B.X (p + n)` is a zero object.
`BoundedCochainComplex.FinCochain A B n` records only the components at the finitely many *active*
degrees `p` with `p ∈ A.support` and `p + n ∈ B.support`, which makes it a computable model of the
Hom-complex.

## Main definitions

* `BoundedCochainComplex.activePairs A B n`: the finite set of source degrees `p` at which a
  degree-`n` cochain `A ⟶ B` can be nonzero.
* `BoundedCochainComplex.FinCochain A B n`: the `R`-module of degree-`n` cochains on the active
  degrees, with components accessed by `FinCochain.v` (on the active set) or `FinCochain.getV`
  (extended by zero).
* `BoundedCochainComplex.FinCochain.δ`: the Hom-complex differential, raising the degree by one.
* `BoundedCochainComplex.FinCochain.comp`: composition of cochains, adding the degrees.
* `BoundedCochainComplex.FinCochain.ofHom`: the degree-`0` cochain underlying a chain map.
* `BoundedCochainComplex.FinCochain.toCochainLinearEquiv`: the `R`-linear equivalence with
  Mathlib's `CochainComplex.HomComplex.Cochain` on the underlying complexes, under which `δ`, `comp`
  and `ofHom` correspond to `CochainComplex.HomComplex.δ`, `Cochain.comp` and `Cochain.ofHom`.

## Implementation notes

`FinCochain A B n` is an abbreviation for a dependent function type on the subtype
`{p // p ∈ activePairs A B n}`, so that it inherits the pointwise `AddCommGroup` and `Module R`
structures. The differential and the composition are stated with `eqToHom` casts along the degree
identities `(p + 1) + n = p + (n + 1)` and `(p + n₁) + n₂ = p + (n₁ + n₂)`; the `toCochain_*`
lemmas transfer their properties from Mathlib's Hom-complex.
-/

@[expose] public section

open CategoryTheory Limits

namespace BoundedCochainComplex

variable {V : Type*} [Category V] [HasZeroObject V] [Preadditive V]

/-- Outside its support, a bounded cochain complex consists of zero objects. -/
lemma isZero_X_of_not_mem_support (C : BoundedCochainComplex V) {p : ℤ} (hp : p ∉ C.support) :
    IsZero (C.X p) :=
  not_not.mp (mt (C.not_isZero_iff_mem_support p).mp hp)

/-- The finite set of source degrees `p` at which a degree-`n` cochain `A ⟶ B` can be nonzero:
those `p` in the support of `A` whose target degree `p + n` lies in the support of `B`. -/
def activePairs (A B : BoundedCochainComplex V) (n : ℤ) : Finset ℤ :=
  A.support.filter fun p => p + n ∈ B.support

namespace activePairs

variable {A B : BoundedCochainComplex V} {n : ℤ} {p : ℤ}

@[simp] lemma mem_iff : p ∈ activePairs A B n ↔ p ∈ A.support ∧ p + n ∈ B.support :=
  Finset.mem_filter

lemma mem_left (h : p ∈ activePairs A B n) : p ∈ A.support := (mem_iff.mp h).1

lemma mem_right (h : p ∈ activePairs A B n) : p + n ∈ B.support := (mem_iff.mp h).2

end activePairs

/-- A computable cochain of degree `n` from `A` to `B`: a morphism `A.X p ⟶ B.X (p + n)` for each
active source degree `p`, i.e. `p ∈ A.support` with `p + n ∈ B.support`. Outside the active
degrees either the source or the target is a zero object, so the component is uniquely zero and
carries no data. -/
abbrev FinCochain (A B : BoundedCochainComplex V) (n : ℤ) : Type _ :=
  ∀ p : {p : ℤ // p ∈ activePairs A B n}, A.X ↑p ⟶ B.X (↑p + n)

namespace FinCochain

variable {A B : BoundedCochainComplex V} {n : ℤ}
variable {R : Type*} [CommRing R] [Linear R V]

instance instAddCommGroup : AddCommGroup (FinCochain A B n) := inferInstance

instance instModule : Module R (FinCochain A B n) := inferInstance

/-- The component of a `FinCochain` at an active source degree `p`. -/
def v (z : FinCochain A B n) {p : ℤ} (hp : p ∈ activePairs A B n) : A.X p ⟶ B.X (p + n) :=
  z ⟨p, hp⟩

@[simp] lemma v_add (z w : FinCochain A B n) {p : ℤ} (hp : p ∈ activePairs A B n) :
    (z + w).v hp = z.v hp + w.v hp := rfl

@[simp] lemma v_zero {p : ℤ} (hp : p ∈ activePairs A B n) :
    (0 : FinCochain A B n).v hp = 0 := rfl

@[simp] lemma v_neg (z : FinCochain A B n) {p : ℤ} (hp : p ∈ activePairs A B n) :
    (-z).v hp = -z.v hp := rfl

@[simp] lemma v_smul (r : R) (z : FinCochain A B n) {p : ℤ} (hp : p ∈ activePairs A B n) :
    (r • z).v hp = r • z.v hp := rfl

/-- The component of a `FinCochain` at an arbitrary source degree `p`, extended by zero outside the
active degrees. -/
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

lemma getV_smul (r : R) (z : FinCochain A B n) (p : ℤ) :
    (r • z).getV p = r • z.getV p := by
  simp only [getV]
  split_ifs with h <;> simp [v_smul]

/-! ### The differential -/

/-- The Hom-complex differential on `FinCochain`, raising the degree by `1`. It is the formula of
`CochainComplex.HomComplex.δ` restricted to the active degrees,
`(δ z).v p = z.getV p ≫ B.d (p + n) (p + (n + 1))
  + (n + 1).negOnePow • A.d p (p + 1) ≫ z.getV (p + 1)`,
where an `eqToHom` accounts for `(p + 1) + n = p + (n + 1)`. -/
def δ (z : FinCochain A B n) : FinCochain A B (n + 1) :=
  fun ⟨p, _⟩ =>
    z.getV p ≫ B.d (p + n) (p + (n + 1)) +
    (n + 1).negOnePow • (A.d p (p + 1) ≫ z.getV (p + 1) ≫
      eqToHom (congr_arg B.X (show (p + 1) + n = p + (n + 1) from by ring)))

lemma δ_add (z w : FinCochain A B n) : δ (z + w) = δ z + δ w := by
  funext ⟨p, _⟩
  simp only [δ, Pi.add_apply, getV_add, Preadditive.add_comp, Preadditive.comp_add, smul_add]
  abel

lemma δ_smul (r : R) (z : FinCochain A B n) : δ (r • z) = r • δ z := by
  funext ⟨p, _⟩
  simp only [δ, Pi.smul_apply, getV_smul, Linear.comp_smul, Linear.smul_comp, smul_add,
    smul_comm r]

variable (R) in
/-- The differential as an `R`-linear map. -/
def δLinear (A B : BoundedCochainComplex V) (n : ℤ) :
    FinCochain A B n →ₗ[R] FinCochain A B (n + 1) where
  toFun := δ
  map_add' := δ_add
  map_smul' := δ_smul

@[simp] private lemma eqToHom_d_comp {C : BoundedCochainComplex V} {a b c : ℤ} {h : a = b} :
    eqToHom (congr_arg C.X h) ≫ C.d b c = C.d a c := by subst h; simp

@[simp] private lemma d_comp_eqToHom {C : BoundedCochainComplex V} {a b c : ℤ} {h : b = c} :
    C.d a b ≫ eqToHom (congr_arg C.X h) = C.d a c := by subst h; simp

/-- The formula for `δ` at an arbitrary degree `p`, with components extended by zero. -/
lemma getV_δ (z : FinCochain A B n) (p : ℤ) :
    (δ z).getV p =
      z.getV p ≫ B.d (p + n) (p + (n + 1)) +
      (n + 1).negOnePow • (A.d p (p + 1) ≫ z.getV (p + 1) ≫
        eqToHom (congr_arg B.X (show (p + 1) + n = p + (n + 1) from by ring))) := by
  by_cases h : p ∈ activePairs A B (n + 1)
  · simp only [getV_of_mem _ h, v, δ]
  · rw [getV_of_not_mem _ h]
    symm
    by_cases hA : p ∈ A.support
    · have hB : p + (n + 1) ∉ B.support :=
        fun hB => h (activePairs.mem_iff.mpr ⟨hA, hB⟩)
      have hZ := B.isZero_X_of_not_mem_support hB
      have h1 : B.d (p + n) (p + (n + 1)) = 0 := hZ.eq_of_tgt _ 0
      have h2 : z.getV (p + 1) ≫
          eqToHom (congr_arg B.X (show (p + 1) + n = p + (n + 1) from by ring)) = 0 :=
        hZ.eq_of_tgt _ 0
      simp [h1, h2]
    · have hZ := A.isZero_X_of_not_mem_support hA
      have h1 : z.getV p = 0 := hZ.eq_of_src _ 0
      have h2 : A.d p (p + 1) = 0 := hZ.eq_of_src _ 0
      simp [h1, h2]

/-- The differential squares to zero. -/
lemma δ_δ (z : FinCochain A B n) : δ (δ z) = 0 := by
  funext ⟨p, _⟩
  simp only [δ, Pi.zero_apply, getV_δ, Preadditive.add_comp, Preadditive.comp_add,
    Preadditive.neg_comp, Preadditive.comp_neg,
    Category.assoc, smul_add, Linear.units_smul_comp, Linear.comp_units_smul,
    HomologicalComplex.d_comp_d, HomologicalComplex.d_comp_d_assoc,
    comp_zero, zero_comp, smul_zero, zero_add, Int.negOnePow_succ, Units.neg_smul]
  rw [eqToHom_d_comp, d_comp_eqToHom]
  · simp only [Units.smul_def, neg_zero, smul_zero]; abel
  · ring
  · ring

/-! ### Chain maps and composition -/

/-- The degree-`0` cochain underlying a morphism of bounded cochain complexes. The `eqToHom`
accounts for `p = p + 0`. -/
def ofHom (h : A ⟶ B) : FinCochain A B 0 :=
  fun ⟨p, _⟩ => h.f p ≫ eqToHom (congr_arg B.X (add_zero p).symm)

/-- Composition of a degree-`n₁` cochain `A ⟶ B` with a degree-`n₂` cochain `B ⟶ C`, a cochain of
degree `n₁ + n₂`. The `eqToHom` accounts for `(p + n₁) + n₂ = p + (n₁ + n₂)`. -/
def comp {C : BoundedCochainComplex V} {n₁ n₂ : ℤ}
    (f : FinCochain A B n₁) (g : FinCochain B C n₂) : FinCochain A C (n₁ + n₂) :=
  fun ⟨p, _⟩ => f.getV p ≫ g.getV (p + n₁) ≫
    eqToHom (congr_arg C.X (show (p + n₁) + n₂ = p + (n₁ + n₂) from by ring))

lemma add_comp {C : BoundedCochainComplex V} {n₁ n₂ : ℤ}
    (f g : FinCochain A B n₁) (h : FinCochain B C n₂) :
    (f + g).comp h = f.comp h + g.comp h := by
  funext ⟨p, _⟩
  simp only [comp, Pi.add_apply, getV_add, Preadditive.add_comp]

lemma comp_add {C : BoundedCochainComplex V} {n₁ n₂ : ℤ}
    (f : FinCochain A B n₁) (g h : FinCochain B C n₂) :
    f.comp (g + h) = f.comp g + f.comp h := by
  funext ⟨p, _⟩
  simp only [comp, Pi.add_apply, getV_add, Preadditive.add_comp, Preadditive.comp_add]

lemma smul_comp {C : BoundedCochainComplex V} {n₁ n₂ : ℤ}
    (r : R) (f : FinCochain A B n₁) (g : FinCochain B C n₂) :
    (r • f).comp g = r • f.comp g := by
  funext ⟨p, _⟩
  simp only [comp, Pi.smul_apply, getV_smul, Linear.smul_comp]

lemma comp_smul {C : BoundedCochainComplex V} {n₁ n₂ : ℤ}
    (r : R) (f : FinCochain A B n₁) (g : FinCochain B C n₂) :
    f.comp (r • g) = r • f.comp g := by
  funext ⟨p, _⟩
  simp only [comp, Pi.smul_apply, getV_smul, Linear.smul_comp, Linear.comp_smul]

/-! ### Comparison with Mathlib's Hom-complex -/

section ToCochain

open CochainComplex

/-- The cochain on the underlying complexes determined by a `FinCochain`, extended by zero off the
active degrees. -/
noncomputable def toCochain (z : FinCochain A B n) :
    HomComplex.Cochain A.toHomologicalComplex B.toHomologicalComplex n :=
  HomComplex.Cochain.mk fun p q hpq => z.getV p ≫ eqToHom (congr_arg B.X hpq)

@[simp] lemma toCochain_v (z : FinCochain A B n) (p q : ℤ) (hpq : p + n = q) :
    z.toCochain.v p q hpq = z.getV p ≫ eqToHom (congr_arg B.X hpq) := rfl

lemma toCochain_add (z w : FinCochain A B n) : (z + w).toCochain = z.toCochain + w.toCochain := by
  ext p q hpq
  simp [getV_add, Preadditive.add_comp]

@[simp] lemma toCochain_smul (r : R) (z : FinCochain A B n) :
    (r • z).toCochain = r • z.toCochain := by
  ext p q hpq
  simp [getV_smul, Linear.smul_comp]

/-- The restriction of a cochain on the underlying complexes to the active degrees. -/
noncomputable def ofCochain
    (c : HomComplex.Cochain A.toHomologicalComplex B.toHomologicalComplex n) :
    FinCochain A B n :=
  fun ⟨p, _⟩ => c.v p (p + n) rfl

/-- Off the active degrees, every cochain on the underlying complexes vanishes. -/
lemma cochain_v_eq_zero_of_not_mem
    (c : HomComplex.Cochain A.toHomologicalComplex B.toHomologicalComplex n)
    {p : ℤ} (hp : p ∉ activePairs A B n) (q : ℤ) (hpq : p + n = q) :
    c.v p q hpq = 0 := by
  simp only [activePairs.mem_iff, not_and_or] at hp
  rcases hp with hA | hB
  · exact (A.isZero_X_of_not_mem_support hA).eq_of_src _ 0
  · exact (B.isZero_X_of_not_mem_support (hpq ▸ hB)).eq_of_tgt _ 0

variable (R) in
/-- `FinCochain A B n` is `R`-linearly equivalent to Mathlib's cochains of degree `n` between the
underlying complexes. -/
noncomputable def toCochainLinearEquiv (A B : BoundedCochainComplex V) (n : ℤ) :
    FinCochain A B n ≃ₗ[R]
      HomComplex.Cochain A.toHomologicalComplex B.toHomologicalComplex n where
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

/-- `toCochain` sends `comp` to `Cochain.comp`. -/
lemma toCochain_comp {C : BoundedCochainComplex V} {n₁ n₂ : ℤ}
    (f : FinCochain A B n₁) (g : FinCochain B C n₂) :
    (f.comp g).toCochain = f.toCochain.comp g.toCochain rfl := by
  ext p q hpq
  rw [HomComplex.Cochain.comp_v _ _ rfl p (p + n₁) q rfl (by omega)]
  simp only [toCochain_v, eqToHom_refl, Category.comp_id]
  by_cases hp : p ∈ activePairs A C (n₁ + n₂)
  · simp only [getV_of_mem _ hp, comp, v, Category.assoc, eqToHom_trans]
  · rw [getV_of_not_mem _ hp, zero_comp]
    simp only [activePairs.mem_iff, not_and_or] at hp
    rcases hp with hA | hC
    · simp [getV_of_not_mem f (fun h => hA (activePairs.mem_left h))]
    · simp [getV_of_not_mem g (fun h =>
          hC (add_assoc p n₁ n₂ ▸ activePairs.mem_right h))]

/-- `toCochain` sends `δ` to Mathlib's Hom-complex differential. -/
lemma toCochain_δ (z : FinCochain A B n) :
    (δ z).toCochain = HomComplex.δ n (n + 1) z.toCochain := by
  ext p q hpq
  subst hpq
  rw [HomComplex.δ_v n (n + 1) rfl z.toCochain p (p + (n + 1)) rfl (p + n) (p + 1) (by ring) rfl]
  simp only [toCochain_v, getV_δ, Preadditive.add_comp, Category.assoc,
    eqToHom_refl, Category.comp_id]

/-- `toCochain` sends `ofHom h` to Mathlib's degree-`0` cochain of the underlying chain map. -/
lemma toCochain_ofHom (h : A ⟶ B) : (ofHom h).toCochain = HomComplex.Cochain.ofHom h.hom := by
  ext p
  rw [toCochain_v]
  by_cases hp : p ∈ activePairs A B 0
  · rw [getV_of_mem _ hp]
    simp [ofHom, v, HomComplex.Cochain.ofHom, HomComplex.Cochain.ofHoms]
  · rw [getV_of_not_mem _ hp, zero_comp]
    exact (cochain_v_eq_zero_of_not_mem (HomComplex.Cochain.ofHom h.hom) hp p (add_zero p)).symm

/-- A chain map is a cocycle: `δ (ofHom h) = 0`. -/
lemma δ_ofHom (h : A ⟶ B) : δ (ofHom h) = 0 := by
  refine ((toCochainLinearEquiv ℤ A B (0 + 1)).map_eq_zero_iff).mp ?_
  show (δ (ofHom h)).toCochain = 0
  rw [toCochain_δ, toCochain_ofHom]
  exact HomComplex.δ_ofHom h.hom

/-- `toCochain` commutes with the action of `ℤˣ`. -/
lemma toCochain_units_smul (u : ℤˣ) (z : FinCochain A B n) :
    (u • z).toCochain = u • z.toCochain := by
  ext p q hpq
  simp only [toCochain_v, Units.smul_def, getV_smul, Linear.smul_comp]
  rfl

/-- `toCochain` commutes with the action of `ℤ`. -/
lemma toCochain_zsmul (c : ℤ) (z : FinCochain A B n) : (c • z).toCochain = c • z.toCochain :=
  map_zsmul (toCochainLinearEquiv ℤ A B n) c z

@[simp] lemma toCochain_zero : (0 : FinCochain A B n).toCochain = 0 :=
  map_zero (toCochainLinearEquiv ℤ A B n)

/-- Associativity of `comp`, transported to Mathlib's cochains: the two triple composites live in
the degrees `(n₁ + n₂) + n₃` and `n₁ + (n₂ + n₃)`, which differ syntactically. -/
lemma toCochain_comp_assoc {C D : BoundedCochainComplex V} {n₁ n₂ n₃ : ℤ}
    (f : FinCochain A B n₁) (g : FinCochain B C n₂) (h : FinCochain C D n₃) :
    ((f.comp g).comp h).toCochain =
      f.toCochain.comp (g.toCochain.comp h.toCochain rfl) (add_assoc n₁ n₂ n₃).symm := by
  simp only [toCochain_comp]
  exact HomComplex.Cochain.comp_assoc f.toCochain g.toCochain h.toCochain rfl rfl rfl

end ToCochain

end FinCochain

end BoundedCochainComplex
