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



-- basis for defining homomorphisms between KLRW objects

-- StrandGenerators are basic elements like dot KLRWDomainObj 4, cross KLRWDomainObj 3, etc. that includes the 
-- domain and what action happens to the ith strand

inductive StrandGenerator [DecidableEq V] [Fintype V] (parameters : KLRWStructure V) where
  | dot   : KLRWObject parameters → Fin (total_strands parameters) → StrandGenerator parameters
  | cross : KLRWObject parameters → Fin (total_strands parameters - 1) → StrandGenerator parameters
  | id : KLRWObject parameters → StrandGenerator parameters


-- function that gives you the KLRWObject after before a strand generator (the domain of the morphism)

def gen_domain [DecidableEq V] [Fintype V] {parameters : KLRWStructure V}
    (gen : StrandGenerator parameters) : KLRWObject parameters :=
  match gen with
  | .dot M _   => M
  | .cross M _ => M
  | .id M      => M


-- function that gives you the KLRWObject after applying a strand generator (NOT FINISHED)

def gen_codomain [DecidableEq V] [Fintype V] {parameters : KLRWStructure V} (gen : StrandGenerator parameters)
    : KLRWObject parameters :=
  match gen with
  | .dot M _   => M
  | .cross M i => M
  | .id M      => M



-- lifts the StrandGenerator to a Free algebra over R[x, y]

abbrev KLRWFreeAlg [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (parameters : KLRWStructure V) :=
  FreeAlgebra (MvPolynomial (Fin 2) R) (StrandGenerator parameters)


-- returns an ideal that contains all of the values of KLRWFreeAlg that should equal 0

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

    -- need to mod out bad compositions of StrandGenerator elements (for f compose g, check if domain
    -- of f = codomain of g)
    {x | ∃ (f g : StrandGenerator parameters), gen_codomain f ≠ gen_domain g ∧
    x = FreeAlgebra.ι (MvPolynomial (Fin 2) R) f * FreeAlgebra.ι (MvPolynomial (Fin 2) R) g} ∪

    -- (a) bigon
    {x | ∃ (M : KLRWObject parameters) (i : Fin (total_strands parameters - 1)),
    (M.strand_seq.get ⟨i, by omega⟩).2 = StrandColor.black ∧ (M.strand_seq.get ⟨i + 1, by omega⟩).2 = StrandColor.black ∧
    x = FreeAlgebra.ι (MvPolynomial (Fin 2) R) (StrandGenerator.cross M i) *
        FreeAlgebra.ι (MvPolynomial (Fin 2) R) (StrandGenerator.cross M i)}

    -- Need to add rest of relations
  )


-- quotients out KLRWRel from KLRWFreeAlg to get KLRW Algebra
abbrev KLRWAlg [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (parameters : KLRWStructure V) :=
  (KLRWRel R parameters).ringCon.Quotient


-- helper function to get the idempotent element e_X inside the quotient algebra (e R X = e_X)
noncomputable def e [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] {parameters : KLRWStructure V}
    (X : KLRWObject parameters) : KLRWAlg R parameters :=
  (KLRWRel R parameters).ringCon.mk' (FreeAlgebra.ι (MvPolynomial (Fin 2) R) (StrandGenerator.id X))


-- uses helper function e to get the set of all equivalence classes of morphisms in KLRAlg that start
-- from X and map to Y (KLRW Hom X Y = e_X KLRWAlg e_Y)
noncomputable def KLRWHom [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (parameters : KLRWStructure V)
    (X Y : KLRWObject parameters) : Submodule R (KLRWAlg R parameters) :=
  LinearMap.range ((LinearMap.mulLeft R (e R X)).comp (LinearMap.mulRight R (e R Y)))






open CategoryTheory


-- Just adds R to KLRWObject so that user can specify what ring they are working in, syntatically
-- needed by lean when defining the category

structure KLRWObjectR (R : Type*) [CommRing R] {V : Type*} [DecidableEq V] [Fintype V]
    (parameters : KLRWStructure V) where
  obj : KLRWObject parameters



noncomputable instance {R : Type*} [CommRing R] {V : Type*} [DecidableEq V] [Fintype V] {parameters : KLRWStructure V} :
    Category (KLRWObjectR R parameters) where
  Hom X Y :=  ↥(KLRWHom R parameters X.obj Y.obj)
  id X := ⟨e R X.obj, by sorry⟩
  comp f g := ⟨f.val * g.val, by sorry⟩
  id_comp  := by sorry
  comp_id  := by sorry
  assoc  := by sorry




 end KLRW
