module

public import Mathlib

@[expose] public section

namespace KLRW


/- A SimpleDigraph is a loopless directed graph. -/

structure SimpleDigraph (V : Type*) extends Digraph V where
  loopless : ∀ x : V, ¬ Adj x x


/- StrandColor holds the two color options a strand can be. -/

inductive StrandColor where
  | red   : StrandColor
  | black : StrandColor
  deriving DecidableEq, Fintype


/- KLRWStructure holds the parameters for a KLRW Algebra.
   Γ represents the directed graph with labeled verticies, BlackStrands tells you the number of
   black strands labeled a given a is in V, and RedStrands a tells you the number of red strands
   labeled a, given a is in V. -/

structure KLRWStructure (V : Type*) where
  Γ : SimpleDigraph (V)
  BlackStrands : V → Nat
  RedStrands : V → Nat


/- StrandDate holds the information each strand is associated with (label and color). -/

structure StrandData (V : Type*) where
  label : V
  color : StrandColor
  deriving DecidableEq



variable {V : Type*} [DecidableEq V] [Fintype V]
variable {parameters : KLRWStructure V}

open StrandColor


/- numColor calculates the number of strands with a given label and color. -/

def numColor {m : ℕ} (v : Vector (StrandData V) m) (k : V) (c : StrandColor) : Nat :=
  (v.toList.filter (fun p => p.label == k && p.color == c)).length

abbrev numBlack {m : ℕ} (v : Vector (StrandData V) m) (k : V) : Nat := numColor v k .black
abbrev numRed {m : ℕ} (v : Vector (StrandData V) m) (k : V) : Nat := numColor v k .red


/- totalStrands calculates the total number of strands in a KLRWStructure. -/

abbrev totalStrands (parameters : KLRWStructure V) :=
  ∑ v : V, (parameters.BlackStrands v + parameters.RedStrands v)


/- strandSeq is a vector where each slot contains a strand's information.
   Corr_num_black ensures the number of black strands for each label in strandSeq matches that of BlackStrands in blueprint.
   Corr_num_red ensures the number of red strands for each label in strandSeq matches that of RedStrands in blueprint. -/

structure KLRWObject (parameters : KLRWStructure V) where
  strandSeq : Vector (StrandData V) (totalStrands parameters)
  corr_num_black : ∀ (i : V), parameters.BlackStrands i = numBlack strandSeq i
  corr_num_red   : ∀ (i : V), parameters.RedStrands i   = numRed strandSeq i


/- This function simplifies the process to access elements in strandSeq of a KLRWObject. -/

abbrev KLRWObject.get (M : KLRWObject parameters) (i : Fin (totalStrands parameters)) :
    StrandData V :=
  M.strandSeq.get i





/- The following section is the basis for defining homomorphisms between KLRW objects. -/

/- StrandGenerators describe what what happens to the ith strand of a specific KLRWObject -/

inductive StrandGenerator (parameters : KLRWStructure V) where
  | dot   : KLRWObject parameters → Fin (totalStrands parameters) → StrandGenerator parameters
  | cross : KLRWObject parameters → Fin (totalStrands parameters - 1) → StrandGenerator parameters
  | idem : KLRWObject parameters → StrandGenerator parameters


/- This function gives you the KLRWObject before a strand generator is applied (the domain of the morphism). -/

def StrandGenerator.domain (gen : StrandGenerator parameters) : KLRWObject parameters :=
  match gen with
  | .dot M _   => M
  | .cross M _ => M
  | .idem M      => M


/- Lemma that shows using toList and List.ofFn to turn a vector into a list results in the same list. -/

lemma toList_eq_ofFn {α : Type*} {n : Nat} (v : Vector α n) : v.toList = List.ofFn v.get := by
  apply List.ext_get (by simp)
  intro i hi1 hi2
  simp [Vector.get, List.getElem_ofFn]


/- Permuting a vector then filtering and counting results in the same count as the original. -/

lemma filter_perm_length_eq {α : Type*} {n : Nat} (v : Vector α n)
    (e : Equiv.Perm (Fin n)) (p : α → Bool) :
    ((Vector.ofFn (fun k => v.get (e k))).toList.filter p).length
      = (v.toList.filter p).length := by
  rw [Vector.toList_ofFn, toList_eq_ofFn v]
  exact ((Equiv.Perm.ofFn_comp_perm e v.get).filter p).length_eq


/- Helper function to swap two side-by-side slots, and show that is a permutation. -/

def adjSwap {n : Nat} (i : Fin (n - 1)) : Equiv.Perm (Fin n) :=
  Equiv.swap ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩


/- Function that gives you the KLRWObject after a cross (the codomain after a cross). -/

def afterCross (M : KLRWObject parameters) (i : Fin (totalStrands parameters - 1)) :
    KLRWObject parameters where
  strandSeq := Vector.ofFn (fun k => M.get (adjSwap i k))
  corr_num_black := fun v => by
    rw [M.corr_num_black v, numBlack]
    exact (filter_perm_length_eq M.strandSeq (adjSwap i) _).symm
  corr_num_red := fun v => by
    rw [M.corr_num_red v, numRed]
    exact (filter_perm_length_eq M.strandSeq (adjSwap i) _).symm


/- Function that gives you the KLRWObject after applying a strand generator. -/

def StrandGenerator.codomain (gen : StrandGenerator parameters) : KLRWObject parameters :=
  match gen with
  | .dot M _   => M
  | .cross M i => afterCross M i
  | .idem M      => M


/- Lifts StrandGenerator to a Free algebra over R[x, y]. -/

abbrev KLRWFreeAlg (R : Type*) [CommRing R] (parameters : KLRWStructure V) :=
  FreeAlgebra (MvPolynomial (Fin 2) R) (StrandGenerator parameters)


/- StrandData V is a type with a finite number of elements. -/

instance (V : Type*) [Fintype V] [DecidableEq V] : Fintype (StrandData V) :=
  Fintype.ofEquiv (V × StrandColor)
    { toFun    := fun p => ⟨p.1, p.2⟩
      invFun   := fun s => ⟨s.label, s.color⟩
      left_inv  := by intro ⟨v, c⟩; rfl
      right_inv := by intro ⟨v, c⟩; rfl }


/- Vector (StrandData V) n is a type with a finite number of elements. -/

instance (V : Type*) [Fintype V] [DecidableEq V] (n : ℕ) : Fintype (Vector (StrandData V) n) :=
  Fintype.ofEquiv (Fin n → StrandData V)
    { toFun    := fun f => Vector.ofFn f
      invFun   := fun v => v.get
      left_inv  := by intro f; ext i; simp
      right_inv := by intro v; ext i; simp; rfl }


/- KLRWObject parameters is a type with a finite number of elements. -/

noncomputable instance (parameters : KLRWStructure V) : Fintype (KLRWObject parameters) :=
  Fintype.ofInjective
    (fun X => X.strandSeq)
    (fun X Y h => by cases X; cases Y; simp at h; congr)


open StrandGenerator
open FreeAlgebra

variable {R : Type*} [CommRing R]


/- Structural/implicit KLRW algebra equality relations. -/

inductive KLRWImplicitConRel : KLRWFreeAlg R parameters → KLRWFreeAlg R parameters → Prop where

  /- If there's a dot on a red strand, set the morphism equal to zero. -/
  | dot_on_red : ∀ (M : KLRWObject parameters) i,
      (M.get i).color = .red →
      KLRWImplicitConRel
        (ι _ (.dot M i)) 0

  /- If there's a crossing with 2 red strands, set the morphism equal to zero. -/
  | cross_two_red : ∀ M i,
      (M.get ⟨i, by omega⟩).color = .red →
      (M.get ⟨i + 1, by omega⟩).color = .red →
      KLRWImplicitConRel
        (ι _ (.cross M i)) 0

  /- If there's a bad composition (domain/codomain mismatch), set the morphism equal to zero.
     g * f means g ∘ f, or first apply the morphism f, then apply the morphism g. -/
  | bad_comp : ∀ f g,
      codomain f ≠ domain g →
      KLRWImplicitConRel
        (ι _ g * ι _ f) 0


  /- .idem M from StrandGenerators acts as the left and right identity for morphisms with the respective domain or codomain. -/

  | idem_left : ∀ M g,
    domain g = M →
    KLRWImplicitConRel
      (ι _ (.idem M) * ι _ g)
      (ι _ g)

  | idem_right : ∀ M g,
    codomain g = M →
    KLRWImplicitConRel
      (ι _ g * ι _ (.idem M))
      (ι _ g)


  /- The identity is formed by summing all the idempotents. -/
  | id_sum :
    KLRWImplicitConRel
      (Finset.univ.sum (fun M : KLRWObject parameters => ι _ (.idem M))) 1


  /- The following explain when two elements are commutative.
     These all follow automatic from equality up to isotopy. -/

  /- If two neighboring crosses occur on strands that are far enough apart, then the order the crosses occur doesn't matter. -/
  | cross_cross_comm : ∀ M i j,
      dist i.val j.val > 1 →
      KLRWImplicitConRel
        (ι _ (.cross (afterCross M i) j) *
         ι _ (.cross M i))
        (ι _ (.cross (afterCross M i) i) *
         ι _ (.cross M j))

  /- The order of neighboring dots doesn't matter. -/
  | dot_dot_comm : ∀ M i j,
      KLRWImplicitConRel
        (ι _ (.dot M j) *
         ι _ (.dot M i))
        (ι _ (.dot M i) *
         ι _ (.dot M j))

  /- If neibhoring crosses and dots are far enough apart, then the order the cross and dot occurs doesn't matter. -/
  | cross_dot_far_comm : ∀ M i j,
      j.val != i.val →
      j.val != i.val + 1 →
      KLRWImplicitConRel
        (ι _ (.dot M j) *
         ι _ (.cross M i))
        (ι _ (.cross M i) *
         ι _ (.dot M j))

  /- If neibhoring crosses and dots are on strands with different labels, then the order the cross and dot occurs doesn't matter -/
  | cross_dot_diff_index_comm : ∀ M i j,
      (M.get ⟨i, by omega⟩).label ≠
      (M.get ⟨i+1, by omega⟩).label →
      KLRWImplicitConRel
        (ι _ (.dot M j) *
         ι _ (.cross M i))
        (ι _ (.cross M i) *
         ι _ (.dot M j))

  /- Given neibhoring crosses and dots, if the cross involves a red strand, then the order the cross and dot occurs doesn't matter -/
  | cross_dot_red_comm : ∀ M i j,
      (M.get ⟨i, by omega⟩).color = .red →
      KLRWImplicitConRel
        (ι _ (.dot M j) *
         ι _ (.cross M i))
        (ι _ (.cross M i) *
         ι _ (.dot M j))


/- uVar and ℏ are the names of the two polynomial variables. -/
noncomputable abbrev uVar : MvPolynomial (Fin 2) R := MvPolynomial.X 0
noncomputable abbrev ℏ : MvPolynomial (Fin 2) R := MvPolynomial.X 1

/- This is an abbreviation to simplify the process of accessing uVar and ℏ lifted into the free algebra. -/
noncomputable abbrev poly (p : MvPolynomial (Fin 2) R) :
    KLRWFreeAlg R parameters :=
  algebraMap _ _ p


-- rename u and ℏ, make R implicit -- can't do, causes errors


/- Explicit KLRW algebra equality relations. -/

inductive KLRWExplicitConRel :
    KLRWFreeAlg R parameters → KLRWFreeAlg R parameters → Prop where

  /- (a) bigon: two black strands cross twice = 0 -/
  | bigon : ∀ M i,
      (M.get ⟨i, by omega⟩).label =
        (M.get ⟨i+1, by omega⟩).label →
      (M.get ⟨i, by omega⟩).color = .black →
      (M.get ⟨i+1, by omega⟩).color = .black →
      KLRWExplicitConRel
        (ι _ (.cross M i) *
         ι _ (.cross M i)) 0

  /- (b) bigon for (j) → (i) -/
  | bigon_for_j_to_i : ∀ M i,
      parameters.Γ.Adj
        (M.get ⟨i, by omega⟩).label
        (M.get ⟨i+1, by omega⟩).label →
      (M.get ⟨i, by omega⟩).color = .black →
      (M.get ⟨i+1, by omega⟩).color = .black →
      KLRWExplicitConRel
        (ι _ (.cross M i) *
         ι _ (.cross M i))
        (poly (uVar) *
        (ι _ (.dot M ⟨i + 1, by omega⟩) -
         ι _ (.dot M ⟨i, by omega⟩)))

  /- (c) bigon with red (red on the left) -/
  | bigon_with_red_left : ∀ M i,
      (M.get ⟨i, by omega⟩).label =
        (M.get ⟨i+1, by omega⟩).label →
      (M.get ⟨i, by omega⟩).color = .red →
      (M.get ⟨i+1, by omega⟩).color = .black →
      KLRWExplicitConRel
        (ι _ (.cross M i) *
         ι _ (.cross M i))
        (poly (uVar) *
        (ι _ (.dot M ⟨i+1, by omega⟩)))

  /- (c) bigon with red (red on the right) -/
  | bigon_with_red_right : ∀ M i,
      (M.get ⟨i, by omega⟩).label =
        (M.get ⟨i+1, by omega⟩).label →
      (M.get ⟨i, by omega⟩).color = .black →
      (M.get ⟨i+1, by omega⟩).color = .red →
      KLRWExplicitConRel
        (ι _ (.cross M i) *
         ι _ (.cross M i))
        (poly (uVar) *
        (ι _ (.dot M ⟨i, by omega⟩)))

  /- (d) braid with neighbour (j) → (i) -/
  | braid_with_neighbor : ∀ M (i : Fin ((totalStrands parameters - 2))),
      parameters.Γ.Adj
        (M.get ⟨i+1, by omega⟩).label
        (M.get ⟨i, by omega⟩).label →
      (M.get ⟨i, by omega⟩).label =
        (M.get ⟨i+2, by omega⟩).label →
      (M.get ⟨i, by omega⟩).color = .black →
      (M.get ⟨i+1, by omega⟩).color = .black →
      (M.get ⟨i+2, by omega⟩).color = .black →
      KLRWExplicitConRel
        (ι _ (.cross M ⟨i, by omega⟩) *
         ι _ (.cross M ⟨i+1, by omega⟩) *
         ι _ (.cross M ⟨i, by omega⟩) -
         ι _ (.cross M ⟨i+1, by omega⟩) *
         ι _ (.cross M ⟨i, by omega⟩) *
         ι _ (.cross M ⟨i+1, by omega⟩))
        ((poly uVar) * (poly ℏ) *
        (ι _ (.idem M)))

  /- (e) braid with red -/
  | braid_with_red : ∀ M (i : Fin ((totalStrands parameters - 2))),
      (M.get ⟨i+1, by omega⟩).label = (M.get ⟨i, by omega⟩).label →
      (M.get ⟨i, by omega⟩).label = (M.get ⟨i+2, by omega⟩).label →
      (M.get ⟨i, by omega⟩).color = .black →
      (M.get ⟨i+1, by omega⟩).color = .red →
      (M.get ⟨i+2, by omega⟩).color = .black →
      KLRWExplicitConRel
        (ι _ (.cross M ⟨i, by omega⟩) *
         ι _ (.cross M ⟨i+1, by omega⟩) *
         ι _ (.cross M ⟨i, by omega⟩) -
         ι _ (.cross M ⟨i+1, by omega⟩) *
         ι _ (.cross M ⟨i, by omega⟩) *
         ι _ (.cross M ⟨i+1, by omega⟩))
        ((poly uVar) * (poly ℏ) *
        (ι _ (.idem M)))

  /- (f) dot-pass-crossing -/
  | dot_pass_cross : ∀ M (i : Fin ((totalStrands parameters - 1))),
      (M.get ⟨i, by omega⟩).label =
        (M.get ⟨i+1, by omega⟩).label →
      (M.get ⟨i, by omega⟩).color = .black →
      (M.get ⟨i+1, by omega⟩).color = .black →
      KLRWExplicitConRel
        (ι _ (.dot (afterCross M i) ⟨i, by omega⟩) *
         ι _ (.cross M i) -
         ι _ (.cross M i) *
         ι _ (.dot M ⟨i+1, by omega⟩))
        ((poly ℏ) *
        (ι _ (.idem M)))

  /- (g) another dot-pass-crossing -/
  | dot_pass_cross_2 : ∀ M (i : Fin (totalStrands parameters - 1)),
      (M.get ⟨i, by omega⟩).label =
        (M.get ⟨i+1, by omega⟩).label →
      (M.get ⟨i, by omega⟩).color = .black →
      (M.get ⟨i+1, by omega⟩).color = .black →
      KLRWExplicitConRel
        (ι _ (.cross M i) *
         ι _ (.dot M ⟨i, by omega⟩) -
         ι _ (.dot (afterCross M i) ⟨i + 1, by omega⟩) *
         ι _ (.cross M i))
        ((poly ℏ) *
        (ι _ (.idem M)))


/- KLRWRel returns the smallest ring congruence relation on the KLRW Free Algebra that contains all the relations
   (both implicit and explicit) that should be true. -/

noncomputable def KLRWRel (R : Type*) [CommRing R] (parameters : KLRWStructure V) :
    RingCon (KLRWFreeAlg R parameters) :=
  ringConGen  (fun x y => KLRWImplicitConRel x y ∨ KLRWExplicitConRel x y)


/- Quotient out KLRWRel from KLRWFreeAlg to get KLRW Algebra. -/

abbrev KLRWAlg (R : Type*) [CommRing R] (parameters : KLRWStructure V) :=
  (KLRWRel R parameters).Quotient


/- Idem_morph is a helper function to get the idempotent element e_X inside the quotient algebra (idem_morph R X = e_X) -/
-- LATER ON TASK: try to make computable (last priority), see why its not

noncomputable def idem_morph (R : Type*) [CommRing R] (X : KLRWObject parameters) :
    KLRWAlg R parameters :=
  (KLRWRel R parameters).mk' (ι (MvPolynomial (Fin 2) R) (.idem X))


/- KLRWHom uses the helper function idem_morph to get the set of all equivalence classes of morphisms in KLRAlg that start
   from X and map to Y (KLRW Hom X Y = e_X KLRWAlg e_Y) -/

noncomputable def KLRWHom (R : Type*) [CommRing R] (X Y : KLRWObject parameters) :
    Submodule R (KLRWAlg R parameters) :=
  LinearMap.range ((LinearMap.mulLeft R (idem_morph R Y)).comp (LinearMap.mulRight R (idem_morph R X)))



 end KLRW
