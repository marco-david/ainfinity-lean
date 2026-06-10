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

structure KLRWReq (n : Nat) where
  DirGraph : SimpleDigraph (Fin n)
  dᵢ : Fin n → Nat
  red_strands : Fin n → Nat

def num_black (v : Vector (Fin n × StrandColor) m) (k : Nat) : Nat :=
  (v.toList.filter (fun p => p.1.val == k && p.2 == StrandColor.black)).length

def num_red (v : Vector (Fin n × StrandColor) m) (k : Nat) : Nat :=
  (v.toList.filter (fun p => p.1.val == k && p.2 == StrandColor.red)).length


-- strand_seq is a vector where each slot contains the strand's label (vertex number associated with it) and color
-- num_black_right makes sure the number of black strands for each label in strand_seq matches that of dᵢ in blueprint
-- num_red_right makes sure the number of red strands for each label in strand_seq matches that of red_strands in blueprint

structure KLRWSet (blueprint : KLRWReq n) where
  strand_seq : Vector (Fin n × StrandColor)
    (Finset.univ.sum blueprint.dᵢ + Finset.univ.sum blueprint.red_strands)
  num_black_right : ∀ (i : Fin n), KLRWReq.dᵢ blueprint i = num_black (strand_seq) i
  num_red_right : ∀ (i : Fin n), KLRWReq.red_strands blueprint i = num_red (strand_seq) i



-- Examples of the previous structures

def exGraph : SimpleDigraph (Fin 3) where
  Adj i j := i.val < j.val
  loopless := by
    intro i h
    exact Nat.lt_irrefl i.val h

def exReq : KLRWReq 3 where
  DirGraph := exGraph
  dᵢ := ![2, 1, 0]
  red_strands := ![1, 0, 1]


def exObj : KLRWSet exReq where
  strand_seq := ⟨#[(0, .black), (0, .black), (0, .red), 
                 (1, .black), (2, .red)], by decide⟩
  num_black_right := by
    intro i
    fin_cases i <;> decide
  num_red_right := by
    intro i
    fin_cases i <;> decide



 end KLRW
