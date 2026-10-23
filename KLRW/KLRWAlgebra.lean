module
public import Mathlib
@[expose] public section
namespace KLRW

section basicDef

variable (V : Type*)

/- A SimpleDigraph is a loopless directed graph. -/

structure SimpleDigraph extends Digraph V where
  loopless : ∀ x : V, ¬ Adj x x
  no_two_way : ∀ x y : V, Adj x y → ¬ Adj y x

noncomputable def reprSimpleDigraph {V : Type*} [Fintype V] [DecidableEq V] [Repr V]
    (Γ : SimpleDigraph V) [DecidableRel Γ.Adj] : Std.Format :=
  let edgeList : List (V × V) :=
    (Finset.univ ×ˢ Finset.univ)
      |>.filter (fun (p : V × V) => decide (Γ.Adj p.1 p.2))
      |>.toList
  f!"SimpleDigraph {repr edgeList}"

noncomputable instance {V : Type*} [Fintype V] [DecidableEq V] [Repr V] [∀ (Γ : SimpleDigraph V) (u v : V), Decidable (Γ.Adj u v)] :
    Repr (SimpleDigraph V) where
  reprPrec Γ _ := reprSimpleDigraph Γ

noncomputable instance {V : Type*} : DecidableEq (SimpleDigraph V) :=
  Classical.decEq _


/- StrandColor holds the two color options a strand can be. -/

inductive StrandColor where
  | red   : StrandColor
  | black : StrandColor
  deriving DecidableEq, Repr, Fintype


/- KLRWStructure holds the parameters for a KLRW Algebra.
   Γ represents the directed graph with labeled verticies, BlackStrands tells you the number of
   black strands labeled a given a is in V, and RedStrands a tells you the number of red strands
   labeled a, given a is in V. -/

structure KLRWStructure where
  Γ : SimpleDigraph V
  BlackStrands : V → Nat
  RedStrands : V → Nat


/- StrandDate holds the information each strand is associated with (label and color). -/

structure StrandData where
  label : V
  color : StrandColor
  deriving DecidableEq, Repr, BEq

end basicDef


open StrandColor

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {parameters : KLRWStructure V}


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
  corr_num_red   : ∀ (i : V), parameters.RedStrands i = numRed strandSeq i


/- Two KLRWObjects are equal if their strandSeq are equal. -/

@[ext]
lemma KLRWObject.ext (X Y : KLRWObject parameters) (h : X.strandSeq = Y.strandSeq) : X = Y := by
  rcases X with ⟨x_seq, x_b, x_r⟩
  rcases Y with ⟨y_seq, y_b, y_r⟩
  dsimp at h
  subst h
  rfl


/- This function simplifies the process to access elements in strandSeq of a KLRWObject. -/

abbrev KLRWObject.get (M : KLRWObject parameters) (i : Fin (totalStrands parameters)) :
    StrandData V :=
  M.strandSeq.get i




/- ------------------------------------------------------------------------------------
   The following section is the basis for defining homomorphisms between KLRW objects.
   ------------------------------------------------------------------------------------ -/

/- StrandGenerators describe what what happens to the ith strand of a specific KLRWObject -/

inductive StrandGenerator (parameters : KLRWStructure V) where
  | dot   : KLRWObject parameters → Fin (totalStrands parameters) → StrandGenerator parameters
  | cross : KLRWObject parameters → Fin (totalStrands parameters - 1) → StrandGenerator parameters
  | idem : KLRWObject parameters → StrandGenerator parameters


/- This function gives you the KLRWObject before a strand generator is applied (the domain of the morphism). -/

def StrandGenerator.domain (gen : StrandGenerator parameters) : KLRWObject parameters :=
  match gen with
  | dot M _   => M
  | cross M _ => M
  | .idem M      => M


/- Lemma that shows using toList and List.ofFn to turn a vector into a list results in the same list. -/

lemma toList_eq_ofFn {α : Type*} {n : Nat} (v : Vector α n) : v.toList = List.ofFn v.get := by
  apply List.ext_get (by simp)
  intro i hi1 hi2
  simp [Vector.get, List.getElem_ofFn]


/- Permuting a vector then filtering and counting results in the same count as the original. -/

lemma filter_perm_length_eq {α : Type*} {n : Nat} (v : Vector α n) (e : Equiv.Perm (Fin n)) (p : α → Bool) :
    ((Vector.ofFn (fun k => v.get (e k))).toList.filter p).length = (v.toList.filter p).length := by
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

@[simp]
lemma afterCross_strandSeq (M : KLRWObject parameters) (i : Fin (totalStrands parameters - 1)) :
    (afterCross M i).strandSeq = Vector.ofFn (fun k => M.get (adjSwap i k)) := rfl

/- Function that gives you the KLRWObject after applying a strand generator. -/

def StrandGenerator.codomain (gen : StrandGenerator parameters) : KLRWObject parameters :=
  match gen with
  | dot M _   => M
  | cross M i => afterCross M i
  | .idem M      => M

/- Lifts StrandGenerator to a Free algebra over R[x, y]. -/

abbrev KLRWFreeAlg (R : Type*) [CommRing R] (parameters : KLRWStructure V) :=
  FreeAlgebra (MvPolynomial (Fin 2) R) (StrandGenerator parameters)



/- ---------------------------------------------------------------------------------------------------
   The following structures and definitions are to simplify the process of constructing specific strand morphisms.
   --------------------------------------------------------------------------------------------------- -/

section

variable {R : Type*} [CommRing R]
variable (M : KLRWObject parameters)

/- StrandGenOp holds only the operation (cross, dot, or idem) without consideration of the initial object. -/

inductive StrandGenOp (parameters : KLRWStructure V) where
  | cross : Fin (totalStrands parameters - 1) → StrandGenOp parameters
  | dot : Fin (totalStrands parameters) → StrandGenOp parameters
  | idem : StrandGenOp parameters
  deriving Repr



/- StrandGenOp.act interprets what StrandGenerator a given StrandGenOp acting on an intial
   KLRWObject M gives, crossed with the codomain KLRWObject of that given StrandGenerator. -/

def StrandGenOp.act :
    StrandGenOp parameters → StrandGenerator parameters × KLRWObject parameters
  | .cross i => (.cross M i, afterCross M i)
  | .dot i   => (.dot M i, M)
  | .idem    => (.idem M, M)


/- strandGenSeqEnd returns the codomain KLRW object after applying a list of strand generator operations. -/

def strandGenSeqEnd (M : KLRWObject parameters) (ops : List (StrandGenOp parameters)) :
    KLRWObject parameters :=
  match ops with
  | [] => M
  | op :: ops =>
      let intermediate := strandGenSeqEnd M ops
      (StrandGenOp.act intermediate op).2


/- strandGenSeq returns the morphism that is the same as applying the given list of StrandGenOp from
   right to left on an initial KLRWObject M. -/

noncomputable def strandGenSeq (M : KLRWObject parameters) (ops : List (StrandGenOp parameters)) :
    KLRWFreeAlg R parameters :=
  match ops with
  | [] =>
      FreeAlgebra.ι _ (.idem M)
  | op :: ops =>
      let M' := strandGenSeqEnd M ops
      let first := StrandGenOp.act M' op
      FreeAlgebra.ι _ first.1 * strandGenSeq M ops


/- Adding a strand operation to a strand generator sequence's list ops2 is the same as multiplying strandGenSeq
   ops2 on the right by the strand operation applied to the output of the strand generator sequence. -/

lemma strandGenSeq_cons (op : StrandGenOp parameters)
    (ops : List (StrandGenOp parameters)) :
    strandGenSeq M (op :: ops) = FreeAlgebra.ι _ (StrandGenOp.act (strandGenSeqEnd M ops) op).1 *
    strandGenSeq (R := R) M ops := by
  rfl



/- -------------------------------------------------------
   The following rules are all automatic simplifications.
   ------------------------------------------------------- -/

/- The result of taking the strandGenSeqEnd of an empty list on any KLRWObject M is just M. -/
@[simp]
lemma strandGenSeqEnd_nil : strandGenSeqEnd M [] = M := by
  rfl

/- Adding a cross to the end of a strandGenSeq is the same as first interpreting the cross, then
   interpreting the rest of the list (as multiplication is defined as being done right to left). -/
@[simp]
lemma strandGenSeqEnd_cross (i : Fin (totalStrands parameters - 1))
    (ops : List (StrandGenOp parameters)) :
    strandGenSeqEnd M (ops ++ [.cross i]) = strandGenSeqEnd (afterCross M i) ops := by
  induction ops with
  | nil =>
      rfl
  | cons op ops ih =>
      simp [strandGenSeqEnd, ih]

/- Adding a cross to the front of a strandGenSeq is the same as interpreting the list, then
   making the new cross at the front. -/
@[simp]
lemma cross_strandGenSeqEnd  (i : Fin (totalStrands parameters - 1))
    (ops : List (StrandGenOp parameters)) :
    strandGenSeqEnd M (.cross i :: ops) = afterCross (strandGenSeqEnd M ops) i := by
  rfl

/- Adding a dot to the end of a list doesn't affect the output KLRWObject of a morphism. -/
@[simp]
lemma strandGenSeqEnd_dot (i : Fin (totalStrands parameters))
    (ops : List (StrandGenOp parameters)) :
    strandGenSeqEnd M (ops ++ [.dot i]) = strandGenSeqEnd M ops := by
  induction ops with
  | nil =>
      rfl
  | cons op ops ih =>
      simp [strandGenSeqEnd, ih]

/- Adding a dot to the front of a list doesn't affect the output KLRWObject of a morphism. -/
@[simp]
lemma dot_strandGenSeqEnd  (i : Fin (totalStrands parameters))
    (ops : List (StrandGenOp parameters)) :
    strandGenSeqEnd M (.dot i :: ops) = strandGenSeqEnd M ops := by
  rfl

/- Adding an idem to the end of a list doesn't affect the output KLRWObject of a morphism. -/
@[simp]
lemma strandGenSeqEnd_idem (ops : List (StrandGenOp parameters)) :
    strandGenSeqEnd M (ops ++ [.idem]) = strandGenSeqEnd M ops := by
  induction ops with
  | nil =>
      rfl
  | cons op ops ih =>
      simp [strandGenSeqEnd, ih]

/- Adding an idem to the front of a list doesn't affect the output KLRWObject of a morphism. -/
@[simp]
lemma idem_strandGenSeqEnd (ops : List (StrandGenOp parameters)) :
    strandGenSeqEnd M (.idem :: ops) = strandGenSeqEnd M ops := by
  rfl


/- The codomain of a strand morphism resulting from appending two lists of strand generator operations
   is the same as the codomain after applying the second list then applying the first list. -/

lemma strandGenSeqEnd_append (ops₁ ops₂ : List (StrandGenOp parameters)) :
    strandGenSeqEnd M (ops₁ ++ ops₂) = strandGenSeqEnd (strandGenSeqEnd M ops₂) ops₁ := by
  induction ops₁ with
  | nil =>
      simp
  | cons op ops₁ ih =>
      simp only [List.cons_append, strandGenSeqEnd]
      rw [ih]


end


/- -------------------------------------------------------
   The following instances show these types are Fintypes.
   ------------------------------------------------------- -/

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



/- ------------------------------------------------------------------------------
   The following describes the rules for equality between KLRW strand morphisms.
   ------------------------------------------------------------------------------ -/


open StrandGenOp StrandGenerator FreeAlgebra

section

variable {R : Type*} [CommRing R]

/- Helper lemma for one rule later on. -/
def BraidHasCorrection (M : KLRWObject parameters) (i : Fin (totalStrands parameters - 2)) : Prop :=
  (M.get ⟨i, by omega⟩).color = .black ∧ (M.get ⟨i+2, by omega⟩).color = .black ∧
  (M.get ⟨i, by omega⟩).label = (M.get ⟨i+2, by omega⟩).label ∧
  (((M.get ⟨i+1, by omega⟩).color = .black ∧
      (parameters.Γ.Adj (M.get ⟨i+1, by omega⟩).label (M.get ⟨i, by omega⟩).label ∨
       parameters.Γ.Adj (M.get ⟨i, by omega⟩).label (M.get ⟨i+1, by omega⟩).label)) ∨
   ((M.get ⟨i+1, by omega⟩).color = .red ∧
      (M.get ⟨i+1, by omega⟩).label = (M.get ⟨i, by omega⟩).label))


/- Structural/implicit KLRW algebra equality relations. -/

inductive KLRWImplicitConRel : KLRWFreeAlg R parameters → KLRWFreeAlg R parameters → Prop where

  /- If there's a dot on a red strand, set the morphism equal to zero. -/
  | dot_on_red : ∀ (M : KLRWObject parameters) i,
      (M.get i).color = .red →
      KLRWImplicitConRel
        (strandGenSeq M [dot i]) 0

  /- If there's a crossing with 2 red strands, set the morphism equal to zero. -/
  | cross_two_red : ∀ M i,
      (M.get ⟨i, by omega⟩).color = .red →
      (M.get ⟨i + 1, by omega⟩).color = .red →
      KLRWImplicitConRel
        (strandGenSeq M [cross i]) 0

  /- If there's a bad composition (domain/codomain mismatch), set the morphism equal to zero.
     g * f means g ∘ f, or first apply the morphism f, then apply the morphism g. -/
  | bad_comp : ∀ f g,
      codomain f ≠ domain g →
      KLRWImplicitConRel
        (ι _ g * ι _ f) 0


  /- .idem M from StrandGenerators acts as the left and right identity for morphisms with the respective domain or codomain. -/

  | idem_left : ∀ M f,
    codomain f = M →
    KLRWImplicitConRel
      (ι _ (.idem M) * ι _ f)
      (ι _ f)

  | idem_right : ∀ M f,
    domain f = M →
    KLRWImplicitConRel
      (ι _ f * ι _ (.idem M))
      (ι _ f)

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
        (strandGenSeq M [cross j, cross i])
        (strandGenSeq M [cross i, cross j])

  /- The order of neighboring dots doesn't matter. -/
  | dot_dot_comm : ∀ M i j,
      KLRWImplicitConRel
        (strandGenSeq M [dot j, dot i])
        (strandGenSeq M [dot i, dot j])

  /- If neighboring crosses and dots are far enough apart, then the order the cross and dot occurs doesn't matter. -/
  | cross_dot_far_comm : ∀ M i j,
      j.val != i.val →
      j.val != i.val + 1 →
      KLRWImplicitConRel
        (strandGenSeq M [dot j, cross i])
        (strandGenSeq M [cross i, dot j])

  /- If two strands being crossed aren't both black or don't have the same label, then the dot and cross commute 
     (dot moves in the left direction). -/
  | dot_follows_strand_left : ∀ M (i : Fin (totalStrands parameters - 1)),
    ¬ ((M.get ⟨i, by omega⟩).color = .black ∧ (M.get ⟨i+1, by omega⟩).color = .black ∧
       (M.get ⟨i, by omega⟩).label = (M.get ⟨i+1, by omega⟩).label) →
    KLRWImplicitConRel
      (strandGenSeq M [dot ⟨i, by omega⟩, cross i])
      (strandGenSeq M [cross i, dot ⟨i+1, by omega⟩])

  /- If two strands being crossed aren't both black or don't have the same label, then the dot and cross commute 
     (dot moves in the right direction). -/
  | dot_follows_strand_right : ∀ M (i : Fin (totalStrands parameters - 1)),
      ¬ ((M.get ⟨i, by omega⟩).color = .black ∧ (M.get ⟨i+1, by omega⟩).color = .black ∧
         (M.get ⟨i, by omega⟩).label = (M.get ⟨i+1, by omega⟩).label) →
      KLRWImplicitConRel
        (strandGenSeq M [dot ⟨i+1, by omega⟩, cross i])
        (strandGenSeq M [cross i, dot ⟨i, by omega⟩])
 
  /- If black strands with different, non-adjacent labels cross twice, its the same as if they didn't cross at all. -/
  | bigon_not_adjacent : ∀ M i,
      (M.get ⟨i, by omega⟩).color = .black →
      (M.get ⟨i+1, by omega⟩).color = .black →
      (M.get ⟨i, by omega⟩).label ≠ (M.get ⟨i+1, by omega⟩).label →
      ¬ parameters.Γ.Adj
          (M.get ⟨i, by omega⟩).label
          (M.get ⟨i+1, by omega⟩).label →
      ¬ parameters.Γ.Adj
          (M.get ⟨i+1, by omega⟩).label
          (M.get ⟨i, by omega⟩).label →
      KLRWImplicitConRel
        (strandGenSeq M [cross i, cross i])
        (ι _ (.idem M))

  /- If a black and red strand with different labels cross twice, its the same as if they didn't cross at all. -/
  | bigon_black_red_diff : ∀ M i,
    (M.get ⟨i, by omega⟩).color ≠ (M.get ⟨i+1, by omega⟩).color →
    (M.get ⟨i, by omega⟩).label ≠ (M.get ⟨i+1, by omega⟩).label →
    KLRWImplicitConRel
      (strandGenSeq M [cross i, cross i])
      (ι _ (.idem M))

  /- If a braid doesn't have a "correction term," then you can "flip" the braid. -/
  | braid : ∀ M i,
    ¬ BraidHasCorrection M i →
    KLRWImplicitConRel
      (strandGenSeq M [cross ⟨i, by omega⟩, cross ⟨i+1, by omega⟩, cross ⟨i, by omega⟩])
      (strandGenSeq M [cross ⟨i+1, by omega⟩, cross ⟨i, by omega⟩, cross ⟨i+1, by omega⟩])



/- uVar and ℏ are the names of the two polynomial variables. -/
noncomputable abbrev uVar : MvPolynomial (Fin 2) R := MvPolynomial.X 0
noncomputable abbrev ℏ : MvPolynomial (Fin 2) R := MvPolynomial.X 1

/- This is an abbreviation to simplify the process of accessing uVar and ℏ lifted into the free algebra. -/
noncomputable abbrev poly (p : MvPolynomial (Fin 2) R) :
    KLRWFreeAlg R parameters :=
  algebraMap _ _ p


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
        (strandGenSeq M [cross i, cross i]) 0

  /- (b) bigon for (j) → (i) -/
  | bigon_for_j_to_i : ∀ M i,
      parameters.Γ.Adj
        (M.get ⟨i, by omega⟩).label
        (M.get ⟨i+1, by omega⟩).label →
      (M.get ⟨i, by omega⟩).color = .black →
      (M.get ⟨i+1, by omega⟩).color = .black →
      KLRWExplicitConRel
        (strandGenSeq M [cross i, cross i])
        ((poly uVar) *
         (strandGenSeq M [dot ⟨i + 1, by omega⟩] - strandGenSeq M [dot ⟨i, by omega⟩]))

  /- (b) bigon for (i) → (j) -/
  | bigon_for_i_to_j : ∀ M i,
      parameters.Γ.Adj
        (M.get ⟨i+1, by omega⟩).label
        (M.get ⟨i, by omega⟩).label →
      (M.get ⟨i, by omega⟩).color = .black →
      (M.get ⟨i+1, by omega⟩).color = .black →
      KLRWExplicitConRel
        (strandGenSeq M [cross i, cross i])
        ((poly uVar) *
         (strandGenSeq M [dot ⟨i, by omega⟩] - strandGenSeq M [dot ⟨i + 1, by omega⟩]))

  /- (c) bigon with red (red on the left) -/
  | bigon_with_red_left : ∀ M i,
      (M.get ⟨i, by omega⟩).label =
        (M.get ⟨i+1, by omega⟩).label →
      (M.get ⟨i, by omega⟩).color = .red →
      (M.get ⟨i+1, by omega⟩).color = .black →
      KLRWExplicitConRel
        (strandGenSeq M [cross i, cross i])
        ((poly uVar) *
         (strandGenSeq M [dot ⟨i+1, by omega⟩]))

  /- (c) bigon with red (red on the right) -/
  | bigon_with_red_right : ∀ M i,
      (M.get ⟨i, by omega⟩).label =
        (M.get ⟨i+1, by omega⟩).label →
      (M.get ⟨i, by omega⟩).color = .black →
      (M.get ⟨i+1, by omega⟩).color = .red →
      KLRWExplicitConRel
        (strandGenSeq M [cross i, cross i])
        ((poly uVar) *
         (strandGenSeq M [dot ⟨i, by omega⟩]))

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
        (strandGenSeq M [cross ⟨i, by omega⟩, cross ⟨i+1, by omega⟩, cross ⟨i, by omega⟩] -
         strandGenSeq M [cross ⟨i+1, by omega⟩, cross ⟨i, by omega⟩, cross ⟨i+1, by omega⟩])
        ((poly uVar) * (poly ℏ) *
         (ι _ (.idem M)))

  /- (d) braid with neighbour (i) → (j) -/
  | braid_with_neighbor_i_to_j : ∀ M (i : Fin ((totalStrands parameters - 2))),
      parameters.Γ.Adj
        (M.get ⟨i, by omega⟩).label
        (M.get ⟨i+1, by omega⟩).label →
      (M.get ⟨i, by omega⟩).label =
        (M.get ⟨i+2, by omega⟩).label →
      (M.get ⟨i, by omega⟩).color = .black →
      (M.get ⟨i+1, by omega⟩).color = .black →
      (M.get ⟨i+2, by omega⟩).color = .black →
      KLRWExplicitConRel
        (strandGenSeq M [cross ⟨i, by omega⟩, cross ⟨i+1, by omega⟩, cross ⟨i, by omega⟩] -
         strandGenSeq M [cross ⟨i+1, by omega⟩, cross ⟨i, by omega⟩, cross ⟨i+1, by omega⟩])
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
        (strandGenSeq M [cross ⟨i, by omega⟩, cross ⟨i+1, by omega⟩, cross ⟨i, by omega⟩] -
         strandGenSeq M [cross ⟨i+1, by omega⟩, cross ⟨i, by omega⟩, cross ⟨i+1, by omega⟩])
        ((poly uVar) * (poly ℏ) *
         (ι _ (.idem M)))

  /- (f) dot-pass-crossing -/
  | dot_pass_cross : ∀ M (i : Fin ((totalStrands parameters - 1))),
      (M.get ⟨i, by omega⟩).label =
        (M.get ⟨i+1, by omega⟩).label →
      (M.get ⟨i, by omega⟩).color = .black →
      (M.get ⟨i+1, by omega⟩).color = .black →
      KLRWExplicitConRel
        (strandGenSeq M [dot ⟨i, by omega⟩, cross i] -
         strandGenSeq M [cross i, dot ⟨i+1, by omega⟩])
        ((poly ℏ) *
         (ι _ (.idem M)))

  /- (g) another dot-pass-crossing -/
  | dot_pass_cross_2 : ∀ M (i : Fin (totalStrands parameters - 1)),
      (M.get ⟨i, by omega⟩).label =
        (M.get ⟨i+1, by omega⟩).label →
      (M.get ⟨i, by omega⟩).color = .black →
      (M.get ⟨i+1, by omega⟩).color = .black →
      KLRWExplicitConRel
        (strandGenSeq M [cross i, dot ⟨i, by omega⟩] -
         strandGenSeq M [dot ⟨i + 1, by omega⟩, cross i])
        ((poly ℏ) *
         (ι _ (.idem M)))

end



/- ---------------------------------------------------------------------------------
   The following acts as a foundation for turning KLRW into a well-defined category.
   --------------------------------------------------------------------------------- -/

section

variable (R : Type*) [CommRing R]

/- KLRWRel returns the smallest ring congruence relation on the KLRW Free Algebra that contains all the relations
   (both implicit and explicit) that should be true. -/

noncomputable def KLRWRel (parameters : KLRWStructure V) :
    RingCon (KLRWFreeAlg R parameters) :=
  ringConGen  (fun x y => KLRWImplicitConRel x y ∨ KLRWExplicitConRel x y)


/- Quotient out KLRWRel from KLRWFreeAlg to get KLRW Algebra. -/

abbrev KLRWAlg (parameters : KLRWStructure V) :=
  (KLRWRel R parameters).Quotient


/- Idem_morph is a helper function to get the idempotent element of the quotient algebra. -/

noncomputable def idem_morph (X : KLRWObject parameters) :
    KLRWAlg R parameters :=
  (KLRWRel R parameters).mk' (ι (MvPolynomial (Fin 2) R) (.idem X))


/- KLRWHom uses the helper function idem_morph to get the set of all equivalence classes of
   morphisms in KLRAlg that start from X and map to Y (KLRW Hom X Y = e_X KLRWAlg e_Y). -/

noncomputable def KLRWHom (X Y : KLRWObject parameters) :
    Submodule R (KLRWAlg R parameters) :=
  LinearMap.range ((LinearMap.mulLeft R (idem_morph R Y)).comp (LinearMap.mulRight R (idem_morph R X)))

end
end KLRW
