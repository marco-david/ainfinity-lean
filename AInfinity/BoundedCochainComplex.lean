import Mathlib
import AInfinity.AdditiveCompletion

open CategoryTheory Limits

/-!
# Bounded Cochain Complexes

A computable version of `CochainComplex` backed by `List`, analogous to
`CMat_` vs `Mat_`. Objects are stored as a finite list with an explicit
starting cohomological degree.
-/


structure BoundedCochainComplex (V : Type*) [Category V] [HasZeroObject V] [Preadditive V]
    extends CochainComplex V ℤ where
  support : Finset ℤ
  not_isZero_iff_mem_support : ∀ i : ℤ, ¬ IsZero (X i) ↔ i ∈ support

def BoundedCochainComplex.length {V : Type*} [Category V] [HasZeroObject V] [Preadditive V]
    (c : BoundedCochainComplex V) : ℤ :=
  if h : c.support.Nonempty then c.support.max' h - c.support.min' h else 0

def BoundedCochainComplex.mkOfBounded {V : Type*} [Category V] [HasZeroObject V] [Preadditive V]
    [DecidablePred (IsZero : V → Prop)]
    (c : CochainComplex V ℤ) {supersetOfSupport : Finset ℤ}
    (h : ∀ i : ℤ, ¬ IsZero (c.X i) → i ∈ supersetOfSupport)
    : BoundedCochainComplex V where
  X := c.X
  d := c.d
  support := {i ∈ supersetOfSupport | ¬ IsZero (c.X i)}
  not_isZero_iff_mem_support := by
    sorry

theorem BoundedCochainComplex.mkOfBounded_eq
    {V : Type*} [Category V] [HasZeroObject V] [Preadditive V]
    [DecidablePred (IsZero : V → Prop)] (c : CochainComplex V ℤ)
    {s₁ s₂ : Finset ℤ}
    (h₁ : ∀ i : ℤ, ¬ IsZero (c.X i) → i ∈ s₁)
    (h₂ : ∀ i : ℤ, ¬ IsZero (c.X i) → i ∈ s₂)
  : BoundedCochainComplex.mkOfBounded c h₁ = BoundedCochainComplex.mkOfBounded c h₂ := by
  sorry

namespace BoundedCochainComplex

variable {V : Type*} [Category V] [HasZeroObject V] [Preadditive V]

instance : Category (BoundedCochainComplex V) where
  Hom A B := sorry
  id A := sorry
  comp := sorry
instance : Preadditive (BoundedCochainComple V) := sorry

def BoundedCochainComplex.embed : BoundedCochainComplex V ⥤ CochainComplex V ℤ := sorry

instance : Functor.Faithful (BoundedCochainComplex.embed (V := V)) := sorry
instance : Functor.Full (BoundedCochainComplex.embed (V := V)) := sorry

variable {R : Type*} [CommRing R] [Linear R V] in
instance : Linear R (BoundedCochainComplex V) := sorry

/-! ## Basic accessors -/

abbrev len (C : BoundedCochainComplex V) : ℕ := C.objects.length
def stop (C : BoundedCochainComplex V) : ℤ := C.start + C.len
def X (C : BoundedCochainComplex V) (i : Fin C.len) : V := C.objects[i]

/-! ## Fixed-length category -/

/-- Bounded cochain complexes with fixed length and start. -/
structure FixedBCC (V : Type*) [Category V] [Preadditive V] (n : ℕ) (s : ℤ) where
  val : BoundedCochainComplex V
  hlen : val.len = n
  hstart : val.start = s

namespace FixedBCC

variable {V : Type*} [Category V] [Preadditive V] {n : ℕ} {s : ℤ}

/-- Get the `i`-th object of a fixed-length bounded complex. -/
abbrev obj (A : FixedBCC V n s) (i : Fin n) : V :=
  A.val.objects[i.val]'(by have : A.val.objects.length = n := A.hlen; omega)

/-- Get the `i`-th differential of a fixed-length bounded complex. -/
abbrev dif (A : FixedBCC V n s) (i : Fin (n - 1)) : A.obj ⟨i, by omega⟩ ⟶ A.obj ⟨i + 1, by omega⟩ :=
  A.val.d ⟨i, by have : A.val.objects.length = n := A.hlen; omega⟩

/-- A morphism in `FixedBCC`: component maps commuting with differentials. -/
structure Hom (A B : FixedBCC V n s) where
  f : ∀ (i : Fin n), A.obj i ⟶ B.obj i
  comm : ∀ (i : Fin (n - 1)),
    f ⟨i, by omega⟩ ≫ B.dif i = A.dif i ≫ f ⟨i + 1, by omega⟩

theorem hom_f_injective {A B : FixedBCC V n s} :
    Function.Injective (Hom.f : Hom A B → _) := by
  intro f g h; cases f; cases g; congr

@[ext]
theorem Hom.ext {A B : FixedBCC V n s} {f g : Hom A B}
    (h : ∀ i, f.f i = g.f i) : f = g :=
  hom_f_injective (funext h)

def Hom.id (A : FixedBCC V n s) : Hom A A where
  f _ := 𝟙 _
  comm _ := by simp

def Hom.comp {A B C : FixedBCC V n s} (f : Hom A B) (g : Hom B C) : Hom A C where
  f i := f.f i ≫ g.f i
  comm i := by
    calc (f.f ⟨i, _⟩ ≫ g.f ⟨i, _⟩) ≫ C.dif i
        = f.f ⟨i, _⟩ ≫ (g.f ⟨i, _⟩ ≫ C.dif i) := by rw [Category.assoc]
      _ = f.f ⟨i, _⟩ ≫ (B.dif i ≫ g.f ⟨i + 1, _⟩) := by rw [g.comm]
      _ = (f.f ⟨i, _⟩ ≫ B.dif i) ≫ g.f ⟨i + 1, _⟩ := by rw [← Category.assoc]
      _ = (A.dif i ≫ f.f ⟨i + 1, _⟩) ≫ g.f ⟨i + 1, _⟩ := by rw [f.comm]
      _ = A.dif i ≫ f.f ⟨i + 1, _⟩ ≫ g.f ⟨i + 1, _⟩ := by rw [Category.assoc]

instance : Category (FixedBCC V n s) where
  Hom := Hom
  id := Hom.id
  comp f g := f.comp g
  id_comp f := by ext i; simp [Hom.comp, Hom.id]
  comp_id f := by ext i; simp [Hom.comp, Hom.id]
  assoc f g h := by ext i; simp [Hom.comp, Category.assoc]

-- Algebraic structure on morphisms, registered after Category so they apply to `A ⟶ B`.

instance {A B : FixedBCC V n s} : Zero (A ⟶ B) where
  zero := { f := fun _ => 0, comm := fun _ => by simp }

instance {A B : FixedBCC V n s} : Add (A ⟶ B) where
  add φ ψ := {
    f := fun i => φ.f i + ψ.f i
    comm := fun i => by simp [Preadditive.add_comp, Preadditive.comp_add, Hom.comm φ, Hom.comm ψ] }

instance {A B : FixedBCC V n s} : Neg (A ⟶ B) where
  neg φ := {
    f := fun i => -φ.f i
    comm := fun i => by simp [Preadditive.neg_comp, Preadditive.comp_neg, Hom.comm φ] }

instance {A B : FixedBCC V n s} : Sub (A ⟶ B) where
  sub φ ψ := {
    f := fun i => φ.f i - ψ.f i
    comm := fun i => by simp [Preadditive.sub_comp, Preadditive.comp_sub, Hom.comm φ, Hom.comm ψ] }

instance {A B : FixedBCC V n s} : SMul ℕ (A ⟶ B) where
  smul r φ := {
    f := fun i => r • φ.f i
    comm := fun i => by simp [Hom.comm φ] }

instance {A B : FixedBCC V n s} : SMul ℤ (A ⟶ B) where
  smul r φ := {
    f := fun i => r • φ.f i
    comm := fun i => by simp [Hom.comm φ] }

instance {A B : FixedBCC V n s} : AddCommGroup (A ⟶ B) :=
  Function.Injective.addCommGroup Hom.f hom_f_injective rfl
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[simp] theorem comp_f {A B C : FixedBCC V n s} (f : A ⟶ B) (g : B ⟶ C) (i : Fin n) :
    (f ≫ g).f i = f.f i ≫ g.f i := rfl

@[simp] theorem add_f {A B : FixedBCC V n s} (f g : A ⟶ B) (i : Fin n) :
    (f + g).f i = f.f i + g.f i := rfl

instance : Preadditive (FixedBCC V n s) where
  add_comp := by intros; apply Hom.ext; intro i; simp [Preadditive.add_comp]
  comp_add := by intros; apply Hom.ext; intro i; simp [Preadditive.comp_add]

/-! ## Equivalence to CochainComplex

Following the `CMat_.toMat_` pattern: the computable direction maps a
`FixedBCC` to a `CochainComplex` by zero-padding outside the support.
The noncomputable inverse extracts a bounded complex from a `CochainComplex`
that is known to have bounded support. -/

section equivalence

variable {V : Type*} [Category V] [Preadditive V] {n : ℕ} {s : ℤ}

/-- Whether an integer degree is in the range `[s, s + n)`. -/
def inRange (s : ℤ) (n : ℕ) (deg : ℤ) : Prop := s ≤ deg ∧ deg < s + n

instance (s : ℤ) (n : ℕ) (deg : ℤ) : Decidable (inRange s n deg) :=
  instDecidableAnd

/-- Convert a degree in range to a `Fin n` index. -/
def degToFin (s : ℤ) (n : ℕ) (deg : ℤ) (h : inRange s n deg) : Fin n :=
  ⟨(deg - s).toNat, by unfold inRange at h; omega⟩

theorem degToFin_succ {s : ℤ} {n : ℕ} {deg : ℤ}
    (h : inRange s n deg) (h' : inRange s n (deg + 1)) :
    (degToFin s n (deg + 1) h').val = (degToFin s n deg h).val + 1 := by
  simp only [degToFin]
  have hs : 0 ≤ deg - s := by unfold inRange at h; omega
  zify [hs, show 0 ≤ deg + 1 - s by omega]; omega

open scoped ZeroObject in
/-- Functor from bounded cochain complexes to `CochainComplex`, padding with
    zero objects outside the support. Noncomputable due to `HasZeroObject`. -/
noncomputable def toCochainComplex [Limits.HasZeroObject V] :
    FixedBCC V n s ⥤ CochainComplex V ℤ where
  obj A :=
    let Xfun : ℤ → V := fun deg =>
      if h : inRange s n deg then A.obj (degToFin s n deg h) else (0 : V)
    { X := Xfun
      d := fun i j =>
        if hij : j = i + 1 then
          if hi : inRange s n i then
            if hj : inRange s n j then
              eqToHom (show Xfun i = A.obj (degToFin s n i hi) from dif_pos hi) ≫
                A.val.d ⟨(degToFin s n i hi).val, by
                  have hlen : A.val.objects.length = n := A.hlen
                  have hlt := (degToFin s n i hi).isLt
                  have hjr : i + 1 < s + ↑n := by unfold inRange at hj; omega
                  have h0 : 0 ≤ i - s := by unfold inRange at hi; omega
                  have : (degToFin s n i hi).val = (i - s).toNat := rfl
                  zify [h0] at this; omega⟩ ≫
                eqToHom (by
                  change A.val.objects[(degToFin s n i hi).val + 1]'_ = Xfun j
                  simp only [Xfun, dif_pos hj, obj]
                  congr 1; change _ = (degToFin s n j hj).val
                  have h1 : 0 ≤ i - s := by unfold inRange at hi; omega
                  have h2 : 0 ≤ j - s := by unfold inRange at hj; omega
                  simp only [degToFin]
                  zify [h1, h2]; omega)
            else
              (0 : Xfun i ⟶ Xfun j)
          else
            0
        else
          0
      shape := fun i j hij => by
        simp only [ComplexShape.up, ComplexShape.up'] at hij
        dsimp only
        rw [dif_neg (by omega : ¬(j = i + 1))]
      d_comp_d' := sorry }
  map φ := sorry
  map_id := sorry
  map_comp := sorry

instance [Limits.HasZeroObject V] :
    (toCochainComplex (V := V) (n := n) (s := s)).Faithful where
  map_injective := sorry

instance [Limits.HasZeroObject V] :
    (toCochainComplex (V := V) (n := n) (s := s)).Full where
  map_surjective := sorry

/-- Extract a bounded complex from a `CochainComplex` with known bounded support.
    This is noncomputable because it goes from an unbounded to a bounded representation. -/
noncomputable def ofCochainComplex
    (C : CochainComplex V ℤ) (start : ℤ) (len : ℕ) : FixedBCC V len start where
  val := {
    start := start
    objects := (List.finRange len).map (fun i => C.X (start + i))
    d := sorry
    d_comp_d := sorry
  }
  hlen := by simp [BoundedCochainComplex.len]
  hstart := rfl

noncomputable instance [Limits.HasZeroObject V] :
    (toCochainComplex (V := V) (n := n) (s := s)).EssSurj where
  mem_essImage := sorry

end equivalence

end FixedBCC

end BoundedCochainComplex
