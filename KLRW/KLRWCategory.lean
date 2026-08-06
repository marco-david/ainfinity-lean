module

public import Mathlib
public import KLRW.KLRWAlgebra
@[expose] public section


namespace KLRW

open CategoryTheory


variable {V : Type*} [DecidableEq V] [Fintype V]
variable {parameters : KLRWStructure V}
variable {R : Type*} [CommRing R]



/- If f and g are equal by a rule in KLRWImplicit, then f and g are equal. -/

lemma implicit_rel_eq_rel {f g : KLRWFreeAlg R parameters} (h : KLRWImplicitConRel f g) :
    KLRWRel R parameters f g :=
  RingConGen.Rel.of f g (Or.inl h)


/- If f and g are equal by a rule in KLRWExplicit, then f and g are equal. -/

lemma explicit_rel_eq_rel {f g : KLRWFreeAlg R parameters} (h : KLRWExplicitConRel f g) :
    KLRWRel R parameters f g :=
  RingConGen.Rel.of f g (Or.inr h)


/- If f and g are equal, then they are in the same equivalence class. -/

lemma rel_eq_same_con_class {x y : KLRWFreeAlg R parameters} (h : KLRWRel R parameters x y) :
    (KLRWRel R parameters).mk' x = (KLRWRel R parameters).mk' y := by
  exact (KLRWRel R parameters).eq.mpr h


/- The idempotent morphism in KLRWAlg is idempotent (uses id_left in KLRW Implicit relations). -/

lemma idem_is_idem (M : KLRWObject parameters) :
    idem_morph R M * idem_morph R M = idem_morph R M := by
  apply rel_eq_same_con_class
  apply implicit_rel_eq_rel
  exact KLRWImplicitConRel.idem_left M (.idem M) rfl


/- Shows idem * f = f, so idem acts as the left identity for KLRWHom R X Y. -/

lemma id_mul_left {X Y : KLRWObject parameters} (f : KLRWAlg R parameters)
    (hf : f ∈ KLRWHom R X Y) : idem_morph R Y * f = f := by
  obtain ⟨a, ha⟩ := hf
  dsimp [LinearMap.mulLeft, LinearMap.mulRight, LinearMap.comp] at ha
  rw [← ha, ← mul_assoc, idem_is_idem]


/- Shows f * idem = f, so idem acts as the right identity for KLRWHom R X Y. -/

lemma id_mul_right {X Y : KLRWObject parameters} (f : KLRWAlg R parameters)
    (hf : f ∈ KLRWHom R X Y) : f * idem_morph R X = f := by
  obtain ⟨a, ha⟩ := hf
  dsimp [LinearMap.mulLeft, LinearMap.mulRight, LinearMap.comp] at ha
  rw [← ha, ← mul_assoc, mul_assoc, idem_is_idem]


/- Shows the connection between f ∈ KLRWHom X Y and the idem_moprh . -/

lemma mem_KLRWHom_iff {X Y : KLRWObject parameters} (f : KLRWAlg R parameters) :
    f ∈ KLRWHom R X Y ↔ idem_morph R Y * f * idem_morph R X = f := by
  constructor
  · intro h
    rcases h with ⟨a, rfl⟩
    dsimp at *
    simp [mul_assoc, idem_is_idem]
    simp [← mul_assoc, idem_is_idem]
  · intro h
    use f
    dsimp
    simp only [← mul_assoc]
    exact h


/- Shows the domain and codomain of the multiplication (composition) of two functions is as expected. -/

lemma KLRWHom_comp_mem {X Y Z : KLRWObject parameters} {f g : KLRWAlg R parameters}
    (hf : f ∈ KLRWHom R X Y) (hg : g ∈ KLRWHom R Y Z) :
    g * f ∈ KLRWHom R X Z := by
  rw [mem_KLRWHom_iff, mul_assoc, mul_assoc, id_mul_right f hf]
  rw [← mul_assoc, id_mul_left g hg]


/- This adds R to KLRWObject so that user can specify what ring they are working in. -/

structure KLRWObject.WithRing (R : Type*) [CommRing R] (parameters : KLRWStructure V) where
  obj : KLRWObject parameters


/- KLRWObjectR is a category. -/

noncomputable instance : Category (KLRWObject.WithRing R parameters) where

  Hom X Y := ↥(KLRWHom R X.obj Y.obj)

  id X := ⟨idem_morph R X.obj, by
    rw [mem_KLRWHom_iff]
    simp [idem_is_idem]⟩

  comp f g := ⟨g.val * f.val, KLRWHom_comp_mem f.property g.property⟩ -- check order of f * g

  id_comp f := by ext; exact id_mul_right f.val f.property

  comp_id f := by ext; exact id_mul_left f.val f.property

  assoc f g h := by ext; simp [mul_assoc]


/- If two KLRWObjectRs have the same value, then they are equal. -/

@[ext]
lemma KLRWHom.ext {X Y : KLRWObject.WithRing R parameters} {f g : X ⟶ Y} (h : f.val = g.val) : f = g :=
  Subtype.ext h


/- KLRWObjectR is a preadditive category. -/

noncomputable instance : Preadditive (KLRWObject.WithRing R parameters) where

  homGroup X Y := inferInstanceAs (AddCommGroup (KLRWHom R X.obj Y.obj))

  add_comp X Y Z f g h := by
    ext
    change h.val * (f.val + g.val) = h.val * f.val + h.val * g.val
    exact mul_add h.val f.val g.val
  comp_add X Y Z f g h := by
    ext
    change (g.val + h.val) * f.val = g.val * f.val + h.val * f.val
    exact add_mul g.val h.val f.val


/- KLRWObjectR is a linear category. -/

noncomputable instance : CategoryTheory.Linear R (KLRWObject.WithRing R parameters) where

  homModule X Y := inferInstanceAs (Module R (KLRWHom R X.obj Y.obj))

  smul_comp X Y Z r f g := by
    ext
    change g.val * (r • f.val) = r • (g.val * f.val)
    exact mul_smul_comm r g.val f.val

  comp_smul X Y Z f r g := by
    ext
    change (r • g.val) * f.val = r • (g.val * f.val)
    exact smul_mul_assoc r g.val f.val



 end KLRW
