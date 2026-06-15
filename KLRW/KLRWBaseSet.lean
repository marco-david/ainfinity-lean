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
-- the verticies of DirGraph are labeled from 1 to n
-- dᵢ (a) tells you the number of black strands labeled a, given a is in Fin n
-- red_Strands (a) tells you the number of red strands labeled a, given a is in Fin n

structure KLRWStructure (V : Type*) where
  DirGraph : SimpleDigraph (V)
  dᵢ : V → Nat
  red_strands : V → Nat

def num_black [DecidableEq V] (v : Vector (V × StrandColor) m) (k : V) : Nat :=
  (v.toList.filter (fun p => p.1 == k && p.2 == StrandColor.black)).length

def num_red [DecidableEq V] (v : Vector (V × StrandColor) m) (k : V) : Nat :=
  (v.toList.filter (fun p => p.1 == k && p.2 == StrandColor.red)).length

abbrev total_strands [DecidableEq V] [Fintype V] (Parameters : KLRWStructure V) :=
  ∑ v : V, (Parameters.dᵢ v + Parameters.red_strands v)


-- strand_seq is a vector where each slot contains the strand's label (vertex number associated with it) and color
-- num_black_right makes sure the number of black strands for each label in strand_seq matches that of dᵢ in blueprint
-- num_red_right makes sure the number of red strands for each label in strand_seq matches that of red_strands in blueprint


structure KLRWObject (V : Type*) [DecidableEq V] [Fintype V] (blueprint : KLRWStructure V) where
  strand_seq : Vector (V × StrandColor) (total_strands blueprint)
  corr_num_black : ∀ (i : V), blueprint.dᵢ i = num_black strand_seq i
  corr_num_red : ∀ (i : V), blueprint.red_strands i = num_red strand_seq i



-- Examples of the previous structures

def exGraph : SimpleDigraph (Fin 3) where
  Adj i j := i.val < j.val
  loopless := by
    intro i h
    exact Nat.lt_irrefl i.val h

def exReq : KLRWStructure (Fin 3) where
  DirGraph := exGraph
  dᵢ := ![2, 1, 0]
  red_strands := ![1, 0, 1]


def exObj : KLRWObject (Fin 3) exReq where
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

inductive StrandGenerator (m : Nat) where
  | dot   : Fin m → StrandGenerator m
  | cross : Fin (m - 1) → StrandGenerator m


-- Function that gives you the final position of a strand given its initial position i and the list
-- of StrandGenerators applied to it

def final_pos (mor : List (StrandGenerator m)) (i : Fin m) : Fin m :=
  mor.foldl (fun pos e =>
    match e with
    | StrandGenerator.dot _ => pos
    | StrandGenerator.cross k =>
        if pos.val == k.val then
          ⟨k.val + 1, by omega⟩
        else if pos.val == k.val + 1 then
          ⟨k.val, by omega⟩
        else
          pos
  ) i


-- Example of a list of StrandGenerators and using the function final_pos

def exStrandEventList : List (StrandGenerator 5) :=
  [StrandGenerator.cross 3, StrandGenerator.cross 1, StrandGenerator.cross 2,
  StrandGenerator.cross 0, StrandGenerator.cross 2]

#eval final_pos exStrandEventList 2



-- Defining basic variables that will be commonly used

variable {V : Type*} [DecidableEq V] [Fintype V] {Parameters : KLRWStructure V} (M N K : KLRWObject V Parameters)


-- Describes a single strand diagram, contains 3 pieces of information: the list of all crosses and
-- dots in the strand diagram from bottom up, a proof that all the dots are on blck strands, and
-- a proof that all the strands have the same starting and ending label.

structure HomGenerator (domain codomain : KLRWObject V Parameters) where
  morph : List (StrandGenerator (total_strands Parameters))
  dots_on_black : ∀ (idx : Fin morph.length),
    match morph.get idx with
    | StrandGenerator.dot i =>
        let initialtPos := final_pos (morph.take idx.val) i
        (domain.strand_seq.get initialtPos).2 = StrandColor.black
    | StrandGenerator.cross _ => True
  matching_start_end : ∀ (i : Fin (total_strands Parameters)),
    domain.strand_seq.get i = codomain.strand_seq.get (final_pos morph i)


-- Work in progress, currently returns a list of the positions of a strand i after all crosings and
-- dots, even those that don't cause the position of the the strand to change. Considering changing
-- it to also describe dots

def strand_all_pos (mor : List (StrandGenerator m)) (i : Fin m) : List (Fin m) :=
  List.ofFn (fun j : Fin (mor.length + 1) => final_pos (mor.take j.val) i)

-- Work in progress, currently returns a list of the strand_trace of each strand

def all_strand_all_pos (mor : List (StrandGenerator m)) : List (List (Fin m)) :=
  List.ofFn (fun i : Fin m => strand_all_pos mor i)


-- HomFreeModule is the free R-module generated by the strand diagrams from M to N

abbrev HomFreeModule (R : Type*) [CommRing R] {V : Type*} [DecidableEq V]
    [Fintype V] {Parameters : KLRWStructure V} (M N : KLRWObject V Parameters) :=
  (HomGenerator M N) →₀ R




-- KLRWCoefficients acts like a polynomial, lets user choose 2 elemetns of R to be "special." Can
-- define a general case to make R the same as a a communitive ring ajoined with X and Y.

structure KLRWCoefficients (R : Type*) [CommRing R] where
  u : R
  h : R


-- Just adds R to KLRWObject so that user can specify what ring they are working in, syntatically
-- needed by lean when defining the category

structure KLRWObjectR (R : Type*) [CommRing R] (coeffs : KLRWCoefficients R)
    {V : Type*} [DecidableEq V] [Fintype V]
    (Parameters : KLRWStructure V) where
  obj : KLRWObject V Parameters



-- KLRWRelation is a palceholder which will contain all the equivalence relations between
-- different strand diagrams in the future (give it an element of the free R-module generated
-- by the strand diagrams from M to N and it will return true if that element equals 0)

inductive KLRWRelation (R : Type*) [CommRing R] (coeffs : KLRWCoefficients R) {Parameters : KLRWStructure V}
    (M N : KLRWObject V Parameters) : HomFreeModule R M N → Prop where
  | placeholder : KLRWRelation R coeffs M N 0


-- KLRWRelSubmodule is the submodule generated by all relation terms in KLRWRelation

noncomputable def KLRWRelSubmodule (R : Type*) [CommRing R] (coeffs : KLRWCoefficients R) {Parameters : KLRWStructure V} (M N : KLRWObject V Parameters) :
    Submodule R (HomFreeModule R M N) :=
  Submodule.span R {x | KLRWRelation R coeffs M N x}


-- Hom is made by moding KLRWRelSubmodule out from HomFreeModule

def Hom (R : Type*) [CommRing R] (coeffs : KLRWCoefficients R) {Parameters : KLRWStructure V} (M N : KLRWObject V Parameters) :=
  (HomFreeModule R M N) ⧸ (KLRWRelSubmodule R coeffs M N)




-- This is the identity function in HomGenerator (not in Hom yet, need to project it onto the
-- quotient space still)

def HomGenerator.id : HomGenerator M M where
  morph := []
  dots_on_black := by
    intro idx
    exact Fin.elim0 idx
  matching_start_end := by
    intro i
    simp [final_pos]

-- This is how to compose 2 functions in HomGenerator (doesn't use R at all yet)

def HomGenerator.comp {M N K : KLRWObject V Parameters} (f : HomGenerator M N)
    (g : HomGenerator N K) :
  HomGenerator M K where
  morph := f.morph ++ g.morph
  dots_on_black := by sorry
  matching_start_end := by sorry


-- HomFreeModule.comp is what we need to extend HomGenerator.comp linearly to the free module

def HomFreeModule.comp {R : Type*} [CommRing R] {V : Type*} [DecidableEq V] [Fintype V]
    {Parameters : KLRWStructure V} {M N K : KLRWObject V Parameters} :
    HomFreeModule R M N →ₗ[R] HomFreeModule R N K →ₗ[R] HomFreeModule R M K :=
  by sorry

-- This checks that compositions respects the KLRWRelations so that we can descend
-- HomFreeModule.comp to the quotient Hom.

def Hom.comp {R : Type*} [CommRing R] (coeffs : KLRWCoefficients R) {V : Type*} [DecidableEq V]
    [Fintype V] {Parameters : KLRWStructure V} {M N K : KLRWObject V Parameters}
    (f : Hom R coeffs M N) (g : Hom R coeffs N K) :
    Hom R coeffs M K := by sorry




open CategoryTheory


-- This is an outline of how we will define KLRW categories

noncomputable instance (R : Type*) [CommRing R] (coeffs : KLRWCoefficients R) :
    Category (KLRWObjectR R coeffs Parameters) where
  Hom X Y := Hom R coeffs X.obj Y.obj
  id X := Submodule.mkQ _ (Finsupp.single (HomGenerator.id X.obj) 1)
  comp f g := Hom.comp coeffs f g
  id_comp  := by sorry
  comp_id  := by sorry
  assoc  := by sorry








 end KLRW
