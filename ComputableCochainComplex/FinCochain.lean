/-
Copyright (c) 2026 Jason Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Dong, Marco David
-/
module

public import Mathlib
public import ComputableCochainComplex.BoundedCochainComplex

/-! # Computable cochains between bounded cochain complexes

For bounded cochain complexes `A` and `B` in `V`, a degree-`n` cochain `A ⟶ B` in the sense of
`CochainComplex.HomComplex.Cochain` consists of morphisms `A.X p ⟶ B.X q` for all triplets
`⟨p, q, hpq⟩` with `hpq : p + n = q`, almost all of which are forced to vanish because `A.X p` or
`B.X q` is a zero object. `BoundedCochainComplex.FinCochain A B n` records only the components on
the finitely many *active* triplets, those with `p ∈ A.support` and `q ∈ B.support`, which makes it
a computable model of the Hom-complex.

The interface follows Mathlib's `CochainComplex.HomComplex`: the components of a cochain are
`FinCochain.v p q hpq`, cochains are built with `FinCochain.mk`, the differential `δ n m` is
defined for all degrees `n` and `m`, and the composition `f.comp g h` takes the degree of the
composite together with an equation `h : n₁ + n₂ = n₁₂`.

## Main definitions

* `BoundedCochainComplex.activePairs A B n`: the finite set of source degrees `p` at which a
  degree-`n` cochain `A ⟶ B` can be nonzero.
* `BoundedCochainComplex.FinCochain A B n`: the `R`-module of degree-`n` cochains on the active
  triplets, with components `FinCochain.v p q hpq`, extended by zero off the active triplets.
* `BoundedCochainComplex.FinCochain.mk`: the cochain with given components.
* `BoundedCochainComplex.FinCochain.δ`: the Hom-complex differential `δ n m`, from degree `n` to
  degree `m`, which vanishes unless `n + 1 = m`.
* `BoundedCochainComplex.FinCochain.comp`: the composite `f.comp g h` of cochains of degrees `n₁`
  and `n₂`, of degree `n₁₂` where `h : n₁ + n₂ = n₁₂`, and
  `BoundedCochainComplex.FinCochain.compBilin`, the same as a bilinear map.
* `BoundedCochainComplex.FinCochain.ofHom`: the degree-`0` cochain underlying a chain map.
* `BoundedCochainComplex.FinCochain.toCochainLinearEquiv`: the `R`-linear equivalence with
  Mathlib's `CochainComplex.HomComplex.Cochain` on the underlying complexes, under which `δ`, `comp`
  and `ofHom` correspond to `CochainComplex.HomComplex.δ`, `Cochain.comp` and `Cochain.ofHom`.

## Main results

* `BoundedCochainComplex.FinCochain.δ_δ`: the differential squares to zero.
* `BoundedCochainComplex.FinCochain.δ_comp`: the Leibniz rule for the composition.
* `BoundedCochainComplex.FinCochain.comp_assoc`: the composition is associative.

## Implementation notes

`FinCochain A B n` is an abbreviation for a dependent function type on the active triplets, so
that it inherits the pointwise `AddCommGroup` and `Module R` structures. Off the active triplets,
the source or the target of a component is a zero object, so the components of `FinCochain.mk v`
are those of `v` on every triplet (`FinCochain.mk_v`). The differential, the composition and
`ofHom` are defined by Mathlib's formulas, so they correspond to Mathlib's under `toCochain` by
`mk_v` alone. Their linearity and the identities `δ_δ`, `δ_comp` and `comp_assoc` are transferred
from Mathlib's Hom-complex along the injective map `toCochain`.
-/

@[expose] public section

open CategoryTheory Limits

namespace BoundedCochainComplex

variable {V : Type*} [Category V] [HasZeroObject V] [Preadditive V]

/-- Outside its support, a bounded cochain complex consists of zero objects. -/
lemma isZero_X_of_notMem_support (C : BoundedCochainComplex V) {p : ℤ} (hp : p ∉ C.support) :
    IsZero (C.X p) :=
  not_not.mp (mt (C.not_isZero_iff_mem_support p).mp hp)

/-- The finite set of source degrees `p` at which a degree-`n` cochain `A ⟶ B` can be nonzero:
those `p` in the support of `A` whose target degree `p + n` lies in the support of `B`. -/
def activePairs (A B : BoundedCochainComplex V) (n : ℤ) : Finset ℤ :=
  A.support.filter fun p => p + n ∈ B.support

namespace activePairs

variable {A B : BoundedCochainComplex V} {n p q : ℤ}

@[simp] lemma mem_iff : p ∈ activePairs A B n ↔ p ∈ A.support ∧ p + n ∈ B.support :=
  Finset.mem_filter

/-- Two morphisms `A.X p ⟶ B.X q`, where `p + n = q`, agree as soon as they agree when `p` is an
active degree: otherwise their source or their target is a zero object. -/
lemma hom_ext (hpq : p + n = q) {f g : A.X p ⟶ B.X q} (h : p ∈ activePairs A B n → f = g) :
    f = g := by
  by_cases hp : p ∈ activePairs A B n
  · exact h hp
  subst hpq
  rcases not_and_or.mp (mem_iff.not.mp hp) with hA | hB
  · exact (A.isZero_X_of_notMem_support hA).eq_of_src f g
  · exact (B.isZero_X_of_notMem_support hB).eq_of_tgt f g

end activePairs

/-- A computable cochain of degree `n` from `A` to `B`: a morphism `A.X p ⟶ B.X q` for each active
triplet `⟨p, q, hpq⟩`, i.e. with `p + n = q`, `p ∈ A.support` and `q ∈ B.support`. Off the active
triplets either the source or the target is a zero object, so the component is uniquely zero and
carries no data. -/
abbrev FinCochain (A B : BoundedCochainComplex V) (n : ℤ) : Type _ :=
  ∀ T : {T : CochainComplex.HomComplex.Triplet n // T.p ∈ activePairs A B n}, A.X T.1.p ⟶ B.X T.1.q

namespace FinCochain

variable {A B : BoundedCochainComplex V} {n : ℤ}
variable {R : Type*} [CommRing R] [Linear R V]

instance instAddCommGroup : AddCommGroup (FinCochain A B n) := inferInstance

instance instModule : Module R (FinCochain A B n) := inferInstance

/-! ### Components -/

/-- The component of a cochain on the triplet `⟨p, q, hpq⟩`, extended by zero off the active
triplets. -/
def v (z : FinCochain A B n) (p q : ℤ) (hpq : p + n = q) : A.X p ⟶ B.X q :=
  if hp : p ∈ activePairs A B n then z ⟨⟨p, q, hpq⟩, hp⟩ else 0

lemma v_of_mem (z : FinCochain A B n) {p q : ℤ} (hpq : p + n = q) (hp : p ∈ activePairs A B n) :
    z.v p q hpq = z ⟨⟨p, q, hpq⟩, hp⟩ :=
  dite_eq_left hp

@[ext]
lemma ext {z w : FinCochain A B n} (h : ∀ p q hpq, z.v p q hpq = w.v p q hpq) : z = w := by
  funext ⟨⟨p, q, hpq⟩, hp⟩
  simpa only [v_of_mem _ hpq hp] using h p q hpq

/-- The cochain with components `v p q hpq` on the active triplets. -/
def mk (v : ∀ p q : ℤ, p + n = q → (A.X p ⟶ B.X q)) : FinCochain A B n :=
  fun T => v T.1.p T.1.q T.1.hpq

@[simp]
lemma mk_v (v : ∀ p q : ℤ, p + n = q → (A.X p ⟶ B.X q)) (p q : ℤ) (hpq : p + n = q) :
    (mk v).v p q hpq = v p q hpq :=
  activePairs.hom_ext hpq (v_of_mem _ hpq)

@[simp]
lemma zero_v (p q : ℤ) (hpq : p + n = q) : (0 : FinCochain A B n).v p q hpq = 0 :=
  activePairs.hom_ext hpq fun hp ↦ by rw [v_of_mem _ hpq hp, Pi.zero_apply]

@[simp]
lemma add_v (z w : FinCochain A B n) (p q : ℤ) (hpq : p + n = q) :
    (z + w).v p q hpq = z.v p q hpq + w.v p q hpq :=
  activePairs.hom_ext hpq fun hp ↦ by simp only [v_of_mem _ hpq hp, Pi.add_apply]

@[simp]
lemma neg_v (z : FinCochain A B n) (p q : ℤ) (hpq : p + n = q) :
    (-z).v p q hpq = -z.v p q hpq :=
  activePairs.hom_ext hpq fun hp ↦ by simp only [v_of_mem _ hpq hp, Pi.neg_apply]

@[simp]
lemma smul_v (r : R) (z : FinCochain A B n) (p q : ℤ) (hpq : p + n = q) :
    (r • z).v p q hpq = r • z.v p q hpq :=
  activePairs.hom_ext hpq fun hp ↦ by simp only [v_of_mem _ hpq hp, Pi.smul_apply]

/-! ### The differential, the composition and chain maps

The definitions are Mathlib's formulas for `CochainComplex.HomComplex`, restricted to the active
triplets. -/

/-- The Hom-complex differential, from degree `n` to degree `m`. As for
`CochainComplex.HomComplex.δ`, it is defined for all `n` and `m`, and vanishes unless
`n + 1 = m`; its component on `⟨p, q, hpq⟩` is
`z.v p (p + n) ≫ B.d (p + n) q + m.negOnePow • A.d p (p + m - n) ≫ z.v (p + m - n) q`. -/
def δ (n m : ℤ) (z : FinCochain A B n) : FinCochain A B m :=
  mk fun p q hpq => z.v p (p + n) rfl ≫ B.d (p + n) q +
    m.negOnePow • A.d p (p + m - n) ≫ z.v (p + m - n) q (by rw [hpq, sub_add_cancel])

/-- The composite of a degree-`n₁` cochain `A ⟶ B` and a degree-`n₂` cochain `B ⟶ C`. As for
`CochainComplex.HomComplex.Cochain.comp`, the composite has degree `n₁₂`, given together with an
equation `h : n₁ + n₂ = n₁₂`. -/
def comp {C : BoundedCochainComplex V} {n₁ n₂ n₁₂ : ℤ}
    (f : FinCochain A B n₁) (g : FinCochain B C n₂) (h : n₁ + n₂ = n₁₂) : FinCochain A C n₁₂ :=
  mk fun p q hpq => f.v p (p + n₁) rfl ≫ g.v (p + n₁) q (by rw [← hpq, ← h, add_assoc])

/-- The degree-`0` cochain underlying a morphism of bounded cochain complexes. -/
def ofHom (φ : A ⟶ B) : FinCochain A B 0 :=
  mk fun p q hpq => φ.f p ≫ eqToHom (by rw [← hpq, add_zero])

/-! ### Comparison with Mathlib's Hom-complex -/

section ToCochain

open CochainComplex

/-- The cochain on the underlying complexes with the same components. -/
noncomputable def toCochain (z : FinCochain A B n) :
    HomComplex.Cochain A.toHomologicalComplex B.toHomologicalComplex n :=
  HomComplex.Cochain.mk z.v

@[simp] lemma toCochain_v (z : FinCochain A B n) (p q : ℤ) (hpq : p + n = q) :
    z.toCochain.v p q hpq = z.v p q hpq := rfl

/-- The restriction of a cochain on the underlying complexes to the active triplets. -/
noncomputable def ofCochain
    (c : HomComplex.Cochain A.toHomologicalComplex B.toHomologicalComplex n) :
    FinCochain A B n :=
  FinCochain.mk c.v

@[simp] lemma toCochain_add (z w : FinCochain A B n) :
    (z + w).toCochain = z.toCochain + w.toCochain := by
  ext; simp

@[simp] lemma toCochain_smul (r : R) (z : FinCochain A B n) :
    (r • z).toCochain = r • z.toCochain := by
  ext; simp

variable (R) in
/-- `FinCochain A B n` is `R`-linearly equivalent to Mathlib's cochains of degree `n` between the
underlying complexes. -/
noncomputable def toCochainLinearEquiv (A B : BoundedCochainComplex V) (n : ℤ) :
    FinCochain A B n ≃ₗ[R]
      HomComplex.Cochain A.toHomologicalComplex B.toHomologicalComplex n where
  toFun := toCochain
  map_add' := toCochain_add
  map_smul' := toCochain_smul
  invFun := ofCochain
  left_inv z := by ext; simp [ofCochain]
  right_inv c := by ext; simp [ofCochain]

lemma toCochain_injective : Function.Injective (toCochain : FinCochain A B n → _) :=
  (toCochainLinearEquiv ℤ A B n).injective

@[simp] lemma toCochain_zero : (0 : FinCochain A B n).toCochain = 0 :=
  map_zero (toCochainLinearEquiv ℤ A B n)

/-- `toCochain` commutes with the action of `ℤ`. -/
lemma toCochain_zsmul (c : ℤ) (z : FinCochain A B n) : (c • z).toCochain = c • z.toCochain :=
  map_zsmul (toCochainLinearEquiv ℤ A B n) c z

/-- `toCochain` commutes with the action of `ℤˣ`. -/
lemma toCochain_units_smul (u : ℤˣ) (z : FinCochain A B n) :
    (u • z).toCochain = u • z.toCochain :=
  toCochain_zsmul (u : ℤ) z

/-- `toCochain` sends `δ` to Mathlib's Hom-complex differential. -/
lemma toCochain_δ (m : ℤ) (z : FinCochain A B n) :
    (δ n m z).toCochain = HomComplex.δ n m z.toCochain := by
  ext; simp [δ, HomComplex.δ]

/-- `toCochain` sends `comp` to `Cochain.comp`. -/
lemma toCochain_comp {C : BoundedCochainComplex V} {n₁ n₂ n₁₂ : ℤ}
    (f : FinCochain A B n₁) (g : FinCochain B C n₂) (h : n₁ + n₂ = n₁₂) :
    (f.comp g h).toCochain = f.toCochain.comp g.toCochain h := by
  ext; simp [comp, HomComplex.Cochain.comp]

/-- `toCochain` sends `ofHom φ` to Mathlib's degree-`0` cochain of the underlying chain map. -/
lemma toCochain_ofHom (φ : A ⟶ B) : (ofHom φ).toCochain = HomComplex.Cochain.ofHom φ.hom := by
  ext; simp [ofHom, HomComplex.Cochain.ofHom, HomComplex.Cochain.ofHoms]

/-! ### Linearity of the differential and the composition -/

lemma δ_add {m : ℤ} (z w : FinCochain A B n) : δ n m (z + w) = δ n m z + δ n m w :=
  toCochain_injective (by simp only [toCochain_add, toCochain_δ, HomComplex.δ_add])

lemma δ_smul {m : ℤ} (r : R) (z : FinCochain A B n) : δ n m (r • z) = r • δ n m z :=
  toCochain_injective (by simp only [toCochain_smul, toCochain_δ, HomComplex.δ_smul])

@[simp]
lemma δ_units_smul {m : ℤ} (u : ℤˣ) (z : FinCochain A B n) : δ n m (u • z) = u • δ n m z :=
  toCochain_injective (by
    simp only [toCochain_units_smul, toCochain_δ, HomComplex.δ_units_smul])

variable (R) in
/-- The differential as an `R`-linear map. -/
def δLinear (A B : BoundedCochainComplex V) (n m : ℤ) :
    FinCochain A B n →ₗ[R] FinCochain A B m where
  toFun := δ n m
  map_add' := δ_add
  map_smul' := δ_smul

protected lemma add_comp {C : BoundedCochainComplex V} {n₁ n₂ n₁₂ : ℤ}
    (f g : FinCochain A B n₁) (k : FinCochain B C n₂) (h : n₁ + n₂ = n₁₂) :
    (f + g).comp k h = f.comp k h + g.comp k h :=
  toCochain_injective (by simp only [toCochain_add, toCochain_comp, HomComplex.Cochain.add_comp])

protected lemma comp_add {C : BoundedCochainComplex V} {n₁ n₂ n₁₂ : ℤ}
    (f : FinCochain A B n₁) (g k : FinCochain B C n₂) (h : n₁ + n₂ = n₁₂) :
    f.comp (g + k) h = f.comp g h + f.comp k h :=
  toCochain_injective (by simp only [toCochain_add, toCochain_comp, HomComplex.Cochain.comp_add])

protected lemma smul_comp {C : BoundedCochainComplex V} {n₁ n₂ n₁₂ : ℤ}
    (r : R) (f : FinCochain A B n₁) (g : FinCochain B C n₂) (h : n₁ + n₂ = n₁₂) :
    (r • f).comp g h = r • f.comp g h :=
  toCochain_injective (by
    simp only [toCochain_smul, toCochain_comp, HomComplex.Cochain.smul_comp])

protected lemma comp_smul {C : BoundedCochainComplex V} {n₁ n₂ n₁₂ : ℤ}
    (r : R) (f : FinCochain A B n₁) (g : FinCochain B C n₂) (h : n₁ + n₂ = n₁₂) :
    f.comp (r • g) h = r • f.comp g h :=
  toCochain_injective (by
    simp only [toCochain_smul, toCochain_comp, HomComplex.Cochain.comp_smul])

@[simp]
lemma units_smul_comp {C : BoundedCochainComplex V} {n₁ n₂ n₁₂ : ℤ} (u : ℤˣ)
    (f : FinCochain A B n₁) (g : FinCochain B C n₂) (h : n₁ + n₂ = n₁₂) :
    (u • f).comp g h = u • f.comp g h :=
  toCochain_injective (by
    simp only [toCochain_units_smul, toCochain_comp, HomComplex.Cochain.units_smul_comp])

@[simp]
lemma comp_units_smul {C : BoundedCochainComplex V} {n₁ n₂ n₁₂ : ℤ} (u : ℤˣ)
    (f : FinCochain A B n₁) (g : FinCochain B C n₂) (h : n₁ + n₂ = n₁₂) :
    f.comp (u • g) h = u • f.comp g h :=
  toCochain_injective (by
    simp only [toCochain_units_smul, toCochain_comp, HomComplex.Cochain.comp_units_smul])

variable (R) in
/-- The composition of cochains as an `R`-bilinear map. -/
def compBilin (A B C : BoundedCochainComplex V) (n₁ n₂ n₁₂ : ℤ) (h : n₁ + n₂ = n₁₂) :
    FinCochain A B n₁ →ₗ[R] FinCochain B C n₂ →ₗ[R] FinCochain A C n₁₂ :=
  .mk₂ R (fun f g ↦ f.comp g h) (fun _ _ _ ↦ FinCochain.add_comp _ _ _ h)
    (fun _ _ _ ↦ FinCochain.smul_comp _ _ _ h) (fun _ _ _ ↦ FinCochain.comp_add _ _ _ h)
    (fun _ _ _ ↦ FinCochain.comp_smul _ _ _ h)

@[simp]
lemma compBilin_apply {C : BoundedCochainComplex V} {n₁ n₂ n₁₂ : ℤ} (h : n₁ + n₂ = n₁₂)
    (f : FinCochain A B n₁) (g : FinCochain B C n₂) :
    compBilin R A B C n₁ n₂ n₁₂ h f g = f.comp g h :=
  rfl

/-! ### Identities of the differential and the composition

Each identity is transferred from its counterpart for Mathlib's cochains along the injective map
`toCochain`. -/

/-- The differential squares to zero. -/
lemma δ_δ (n₀ n₁ n₂ : ℤ) (z : FinCochain A B n₀) : δ n₁ n₂ (δ n₀ n₁ z) = 0 :=
  toCochain_injective (by rw [toCochain_δ, toCochain_δ, HomComplex.δ_δ, toCochain_zero])

/-- A chain map is a cocycle. -/
lemma δ_ofHom {m : ℤ} (φ : A ⟶ B) : δ 0 m (ofHom φ) = 0 :=
  toCochain_injective (by rw [toCochain_δ, toCochain_ofHom, HomComplex.δ_ofHom, toCochain_zero])

/-- The Leibniz rule: δ(f ≫ g) = f ≫ δg + (-1)^n₂ δf ≫ g, where `g` has degree `n₂`. -/
lemma δ_comp {C : BoundedCochainComplex V} {n₁ n₂ n₁₂ : ℤ} (f : FinCochain A B n₁)
    (g : FinCochain B C n₂) (h : n₁ + n₂ = n₁₂) (m₁ m₂ m₁₂ : ℤ) (h₁₂ : n₁₂ + 1 = m₁₂)
    (h₁ : n₁ + 1 = m₁) (h₂ : n₂ + 1 = m₂) :
    δ n₁₂ m₁₂ (f.comp g h) =
      f.comp (δ n₂ m₂ g) (by omega) + n₂.negOnePow • (δ n₁ m₁ f).comp g (by omega) := by
  apply toCochain_injective
  simp only [toCochain_add, toCochain_units_smul, toCochain_comp, toCochain_δ]
  exact HomComplex.δ_comp _ _ h m₁ m₂ m₁₂ h₁₂ h₁ h₂

/-- The composition of cochains is associative. -/
lemma comp_assoc {C D : BoundedCochainComplex V} {n₁ n₂ n₃ n₁₂ n₂₃ n₁₂₃ : ℤ}
    (f : FinCochain A B n₁) (g : FinCochain B C n₂) (k : FinCochain C D n₃)
    (h₁₂ : n₁ + n₂ = n₁₂) (h₂₃ : n₂ + n₃ = n₂₃) (h₁₂₃ : n₁ + n₂ + n₃ = n₁₂₃) :
    (f.comp g h₁₂).comp k (show n₁₂ + n₃ = n₁₂₃ by omega) =
      f.comp (g.comp k h₂₃) (show n₁ + n₂₃ = n₁₂₃ by omega) := by
  apply toCochain_injective
  simp only [toCochain_comp]
  exact HomComplex.Cochain.comp_assoc _ _ _ h₁₂ h₂₃ h₁₂₃

end ToCochain

end FinCochain

end BoundedCochainComplex
