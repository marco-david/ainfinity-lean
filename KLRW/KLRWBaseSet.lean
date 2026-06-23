module

public import Mathlib

@[expose] public section

namespace KLRW

structure SimpleDigraph (V : Type*) extends Digraph V where
  loopless : ∀ x : V, ¬ Adj x x

inductive StrandColor where
  | red   : StrandColor
  | black : StrandColor
  deriving DecidableEq

-- n represents the number of verticies in the simple directed graph
-- Γ represents the directed graph with labeled verticies
-- dᵢ (a) tells you the number of black strands labeled a, given a is in Fin n
-- red_Strands (a) tells you the number of red strands labeled a, given a is in Fin n

structure KLRWStructure (V : Type*) where
  Γ : SimpleDigraph (V)
  black_strands : V → Nat
  red_strands : V → Nat

def num_black [DecidableEq V] (v : Vector (V × StrandColor) m) (k : V) : Nat :=
  (v.toList.filter (fun p => p.1 == k && p.2 == StrandColor.black)).length

def num_red [DecidableEq V] (v : Vector (V × StrandColor) m) (k : V) : Nat :=
  (v.toList.filter (fun p => p.1 == k && p.2 == StrandColor.red)).length

abbrev total_strands [DecidableEq V] [Fintype V] (parameters : KLRWStructure V) :=
  ∑ v : V, (parameters.black_strands v + parameters.red_strands v)


-- strand_seq is a vector where each slot contains the strand's label (vertex number associated with it) and color
-- num_black_right makes sure the number of black strands for each label in strand_seq matches that of dᵢ in blueprint
-- num_red_right makes sure the number of red strands for each label in strand_seq matches that of red_strands in blueprint


structure KLRWObject {V : Type*} [DecidableEq V] [Fintype V] (parameters : KLRWStructure V) where
  strand_seq : Vector (V × StrandColor) (total_strands parameters)
  corr_num_black : ∀ (i : V), parameters.black_strands i = num_black strand_seq i
  corr_num_red : ∀ (i : V), parameters.red_strands i = num_red strand_seq i



-- Examples of the previous structures

def exGraph : SimpleDigraph (Fin 3) where
  Adj i j := i.val < j.val
  loopless := by
    intro i h
    exact Nat.lt_irrefl i.val h

def exReq : KLRWStructure (Fin 3) where
  Γ := exGraph
  black_strands := ![2, 1, 0]
  red_strands := ![1, 0, 1]


def exObj : KLRWObject exReq where
  strand_seq := ⟨#[(0, .black), (0, .black), (0, .red),
                 (1, .black), (2, .red)], by decide⟩
  corr_num_black := by
    intro i
    fin_cases i <;> decide
  corr_num_red := by
    intro i
    fin_cases i <;> decide



-- Basis for defining homomorphisms between KLRW objects

-- StrandGenerators are basic elements like dot 4, cross 3, etc. that describe what what happens to
-- the ith strand and is meant to describes crosses and dots in a diagram in order from bottom up

inductive StrandGenerator [DecidableEq V] [Fintype V] (parameters : KLRWStructure V) where
  | dot   : KLRWObject parameters → Fin (total_strands parameters) → StrandGenerator parameters
  | cross : KLRWObject parameters → Fin (total_strands parameters - 1) → StrandGenerator parameters
  | id : KLRWObject parameters → StrandGenerator parameters


-- Function that gives you the KLRWObject after before a strand generator (the domain of the morphism)

def gen_domain [DecidableEq V] [Fintype V] {parameters : KLRWStructure V}
    (gen : StrandGenerator parameters) : KLRWObject parameters :=
  match gen with
  | .dot M _   => M
  | .cross M _ => M
  | .id M      => M


-- Function that gives you the KLRWObject after applying a strand generator (NOT FINISHED)

def gen_codomain [DecidableEq V] [Fintype V] {parameters : KLRWStructure V} (gen : StrandGenerator parameters)
    : KLRWObject parameters :=
  match gen with
  | .dot M _   => M
  | .cross M i => M
  | .id M      => M



-- Lifts the StrandGenerator to a Free algebra over R[x, y]

abbrev KLRWFreeAlg [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (parameters : KLRWStructure V) :=
  FreeAlgebra (MvPolynomial (Fin 2) R) (StrandGenerator parameters)


-- returns generators for all combinations of terms in the free algebra that should equal 0

inductive KLRWRelGen [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (parameters : KLRWStructure V) :
    KLRWFreeAlg R parameters → Prop where

  -- dot on red strand → zero
  | dot_on_red :
      ∀ (M : KLRWObject parameters) (i : Fin (total_strands parameters)),
      (M.strand_seq.get ⟨i, by omega⟩).2 = StrandColor.red →
      KLRWRelGen R parameters (FreeAlgebra.ι _ (StrandGenerator.dot M i))

  -- crossing with 2 red strands → zero
  | cross_two_red :
      ∀ (M : KLRWObject parameters) (i : Fin (total_strands parameters - 1)),
      (M.strand_seq.get ⟨i, by omega⟩).2 = StrandColor.red →
      (M.strand_seq.get ⟨i+1, by omega⟩).2 = StrandColor.red →
      KLRWRelGen R parameters (FreeAlgebra.ι _ (StrandGenerator.cross M i))

  -- identity composed with identity = identity
  | id_idem :
      ∀ (M : KLRWObject parameters),
      KLRWRelGen R parameters
        (FreeAlgebra.ι _ (StrandGenerator.id M) *
         FreeAlgebra.ι _ (StrandGenerator.id M) -
         FreeAlgebra.ι _ (StrandGenerator.id M))

  -- bad composition (for f compose g, when domain of f ≠ codomain of g) → zero
  | bad_comp :
      ∀ (f g : StrandGenerator parameters),
      gen_codomain f ≠ gen_domain g →
      KLRWRelGen R parameters
        (FreeAlgebra.ι _ f * FreeAlgebra.ι _ g)


  -- (a) bigon (two black strands cross twice = 0)
  | bigon :
      ∀ (M : KLRWObject parameters) (i : Fin (total_strands parameters - 1)),
      (M.strand_seq.get ⟨i, by omega⟩).2 = StrandColor.black →
      (M.strand_seq.get ⟨i+1, by omega⟩).2 = StrandColor.black →
      KLRWRelGen R parameters
        (FreeAlgebra.ι _ (StrandGenerator.cross M i) *
         FreeAlgebra.ι _ (StrandGenerator.cross M i))


-- returns an ideal that contains all of the values of KLRWFreeAlg that should equal 0 (uses
-- KLRWRelGen to find which relations should equal 0)

noncomputable def KLRWRel [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (parameters : KLRWStructure V) :
    TwoSidedIdeal (KLRWFreeAlg R parameters) :=
  TwoSidedIdeal.span {x | KLRWRelGen R parameters x}


/-
-- another potential way to define KLRWRel

noncomputable def KLRWRel [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (parameters : KLRWStructure V) :
    TwoSidedIdeal (KLRWFreeAlg R parameters) :=
  TwoSidedIdeal.span (

    -- dot on red strand -> zero
    {x | ∃ (M : KLRWObject parameters) (i : Fin (total_strands parameters)),
    (M.strand_seq.get ⟨i, by omega⟩).2 = StrandColor.red ∧ x = FreeAlgebra.ι (MvPolynomial (Fin 2) R)
    (StrandGenerator.dot M i)} ∪

    -- crossing with 2 red strands -> zero
    {x | ∃ (M : KLRWObject parameters) (i : Fin (total_strands parameters - 1)),
    (M.strand_seq.get ⟨i, by omega⟩).2 = StrandColor.red ∧ (M.strand_seq.get ⟨i + 1, by omega⟩).2 = StrandColor.red ∧
    x = FreeAlgebra.ι (MvPolynomial (Fin 2) R) (StrandGenerator.cross M i)} ∪

    -- identity composed with identity = identity
    {x | ∃ (M : KLRWObject parameters), x = FreeAlgebra.ι (MvPolynomial (Fin 2) R) (StrandGenerator.id M) *
      FreeAlgebra.ι (MvPolynomial (Fin 2) R) (StrandGenerator.id M) - FreeAlgebra.ι (MvPolynomial
      (Fin 2) R) (StrandGenerator.id M)} ∪

  -- bad composition (for f compose g, when domain of f ≠ codomain of g) → zero
    {x | ∃ (f g : StrandGenerator parameters), gen_codomain f ≠ gen_domain g ∧
    x = FreeAlgebra.ι (MvPolynomial (Fin 2) R) f * FreeAlgebra.ι (MvPolynomial (Fin 2) R) g} ∪

  -- (a) bigon (two black strands cross twice = 0)
    {x | ∃ (M : KLRWObject parameters) (i : Fin (total_strands parameters - 1)),
    (M.strand_seq.get ⟨i, by omega⟩).2 = StrandColor.black ∧ (M.strand_seq.get ⟨i + 1, by omega⟩).2 = StrandColor.black ∧
    x = FreeAlgebra.ι (MvPolynomial (Fin 2) R) (StrandGenerator.cross M i) *
        FreeAlgebra.ι (MvPolynomial (Fin 2) R) (StrandGenerator.cross M i)}

  )
 -/


-- quotients out KLRWRel from KLRWFreeAlg to get KLRW Algebra
abbrev KLRWAlg [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (parameters : KLRWStructure V) :=
  (KLRWRel R parameters).ringCon.Quotient


-- helper function to get the idempotent element e_X inside the quotient algebra (identity_morph R X = e_X)
noncomputable def identity_morph [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] {parameters : KLRWStructure V}
    (X : KLRWObject parameters) : KLRWAlg R parameters :=
  (KLRWRel R parameters).ringCon.mk' (FreeAlgebra.ι (MvPolynomial (Fin 2) R) (StrandGenerator.id X))


-- uses helper function e to get the set of all equivalence classes of morphisms in KLRAlg that start
-- from X and map to Y (KLRW Hom X Y = e_X KLRWAlg e_Y)
noncomputable def KLRWHom [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (parameters : KLRWStructure V)
    (X Y : KLRWObject parameters) : Submodule R (KLRWAlg R parameters) :=
  LinearMap.range ((LinearMap.mulLeft R (identity_morph R X)).comp (LinearMap.mulRight R (identity_morph R Y)))


/-
alternative way to define KLRWHom:

def KLRWHom [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (parameters : KLRWStructure V)
    (X Y : KLRWObject parameters) : Submodule R (KLRWAlg R parameters) where
  carrier := {f | identity_morph R X * f * identity_morph R Y = f}
  zero_mem' := by
    change identity_morph R X * 0 * identity_morph R Y = 0
    simp
  add_mem' := by
    intro a b ha hb
    change identity_morph R X * (a + b) * identity_morph R Y = a + b
    rw [mul_add, add_mul, ha, hb]
  smul_mem' := by
    intro r a ha
    change identity_morph R X * (r • a) * identity_morph R Y = r • a
    rw [mul_smul_comm, smul_mul_assoc, ha]

-/



open CategoryTheory




-- if x - y is in the ideal, their images in the quotient are equivalent.

theorem rel_imply_quotient_eq [DecidableEq V] [Fintype V] {R : Type*} [CommRing R]
    {parameters : KLRWStructure V} {x y : KLRWFreeAlg R parameters}
    (h : x - y ∈ KLRWRel R parameters) :
    (KLRWRel R parameters).ringCon.mk' x = (KLRWRel R parameters).ringCon.mk' y :=
  Quotient.sound' ((TwoSidedIdeal.rel_iff _ x y).2 h)


-- uses realtion from KLRWRel to show that the identity is an idempotent (for all X, e_X * e_X = e_X)

theorem identity_is_idempotent [DecidableEq V] [Fintype V]
    {R : Type*} [CommRing R] {parameters : KLRWStructure V}
    (X : KLRWObject parameters) :
    id_morph R X * id_morph R X = id_morph R X := by
  have id_idem_in_rel :
    FreeAlgebra.ι (MvPolynomial (Fin 2) R) (StrandGenerator.id X) *
      FreeAlgebra.ι (MvPolynomial (Fin 2) R) (StrandGenerator.id X) -
      FreeAlgebra.ι (MvPolynomial (Fin 2) R) (StrandGenerator.id X) ∈
    KLRWRel R parameters :=
  TwoSidedIdeal.subset_span (KLRWRelGen.id_idem X)
  have quotient_eq := rel_imply_quotient_eq id_idem_in_rel
  simpa [id_morph, map_mul, map_sub] using quotient_eq


-- theorem that may be useful in the future, shows connection between f ∈ KLRWHom X Y and e_X * f * e_Y = f

theorem mem_KLRWHom_iff [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] {parameters : KLRWStructure V}
    {X Y : KLRWObject parameters} (f : KLRWAlg R parameters) :
    f ∈ KLRWHom R parameters X Y ↔ identity_morph R X * f * identity_morph R Y = f := by
  constructor
  · -- forward direction: if f ∈ range, then e_X * f * e_Y = f
    intro h
    rcases h with ⟨a, rfl⟩
    dsimp at *
    simp [mul_assoc, identity_is_idempotent]
    simp [← mul_assoc, identity_is_idempotent]
  · -- backward direction: if e_X * f * e_Y = f, then f ∈ range
    intro h
    use f
    dsimp
    simp only [← mul_assoc]
    exact h


-- just adds R to KLRWObject so that user can specify what ring they are working in, syntatically
-- needed by lean when defining the category

structure KLRWObjectR (R : Type*) [CommRing R] {V : Type*} [DecidableEq V] [Fintype V]
    (parameters : KLRWStructure V) where
  obj : KLRWObject parameters



-- prove KLRWObjectR R parameters is actually a category

noncomputable instance {R : Type*} [CommRing R] {V : Type*} [DecidableEq V] [Fintype V] {parameters : KLRWStructure V} :
    Category (KLRWObjectR R parameters) where
  Hom X Y :=  ↥(KLRWHom R parameters X.obj Y.obj)
  id X := ⟨identity_morph R X.obj, by
    simp only [KLRWHom, LinearMap.mem_range, LinearMap.comp_apply,
              LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    exact ⟨identity_morph R X.obj, by rw [identity_is_idempotent, identity_is_idempotent]⟩⟩
  comp {X Y Z} f g := ⟨f.val * g.val, by
    simp only [KLRWHom, LinearMap.mem_range, LinearMap.comp_apply,
              LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    obtain ⟨a, ha⟩ := f.property
    obtain ⟨b, hb⟩ := g.property
    refine ⟨a * identity_morph R Y.obj * b, ?_⟩
    rw [← ha, ← hb]
    simp [mul_assoc]
    simp [← mul_assoc, identity_is_idempotent]⟩
  id_comp  := by sorry
  comp_id  := by sorry
  assoc  := by sorry




 end KLRW
