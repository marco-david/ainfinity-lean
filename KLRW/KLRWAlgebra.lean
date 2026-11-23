/-
Copyright (c) 2026 Lillian Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lillian Liu, Marco David, Hallvard Hareide
-/
module
public import Mathlib
public import KLRW.RootLattice

/-!
# KLRW algebras

This file defines KLRW (Khovanov–Lauda–Rouquier–Webster) objects and the KLRW algebra: the
quotient of the free algebra on dots, crossings and idempotents by the KLRW relations, with
coefficients in a commutative ring `S` and parameters `u ℏ : S`.

## Main definitions

* `KLRW.KLRWStructure`: a directed graph `Γ` on the labels `V`, together with the number of black
  and of red strands carrying each label.
* `KLRW.KLRWObject P`: a sequence of labeled black and red strands with the numbers of strands
  prescribed by `P : KLRWStructure V`.
* `KLRW.StrandGenerator P`: the dots, crossings and idempotents that generate the algebra.
* `KLRW.strandGenSeq S M ops`: the product of the generators described by a list of operations,
  starting at the object `M`.
* `KLRW.KLRWImplicitConRel` and `KLRW.KLRWExplicitConRel`: the KLRW relations.
* `KLRW.KLRWAlg u ℏ P`: the KLRW algebra with coefficients in `S` and parameters `u ℏ : S`.
* `KLRW.klrwHom u ℏ X Y`: the morphisms from `X` to `Y`, i.e. the elements `e_Y * a * e_X`.
* `KLRW.KLRWAlgUniv R P`: the universal KLRW algebra, with coefficients in `R[u, ℏ]`.

## Implementation notes

* Every generator records the object it starts from. Products of generators whose objects do
  not match are zero (`KLRWImplicitConRel.bad_comp`), and `klrwHom u ℏ X Y` is the subspace
  `e_Y * A * e_X` of the algebra `A`.
* A list of operations passed to `strandGenSeq` is applied from right to left, matching the
  order of multiplication.
* The relations drawn in Figure 1 of LePage–Shende (the nontrivial KLRW relations) are
  `KLRWExplicitConRel`, and their docstrings use the same letters (a)–(g). All other relations,
  including the cases where strands pass through each other freely, are `KLRWImplicitConRel`.
* Scalars in the relations are written with `•`, the simp-normal form for the `S`-module
  structure (`Algebra.smul_def` converts to `algebraMap S _ r * x` if ever needed).
* The parameters `u` and `ℏ` are arbitrary elements of `S`. The universal case `S = R[u, ℏ]`
  is `KLRWAlgUniv`.

## References

* B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796.
* E. LePage and V. Shende, *Aganagic's invariant is Khovanov homology*, arXiv:2505.00327.
-/

@[expose] public section
namespace KLRW

/-! ## KLRW structures and objects -/

section BasicDefs

/-- The two colors a strand can have. -/
inductive StrandColor where
  | red
  | black
  deriving DecidableEq, Repr

/-- There are two strand colors. (Written out by hand: on Lean 4.35, `deriving Fintype` fails
outside Mathlib.) -/
instance : Fintype StrandColor where
  elems := {.red, .black}
  complete := by intro c; cases c <;> simp

variable (V : Type*)

/-- The data defining a KLRW algebra: a directed graph `Γ` on the set of labels `V`, and for
each label the number of black and of red strands carrying it. -/
structure KLRWStructure where
  /-- The graph on the labels. -/
  Γ : SimpleGraph V
  /-- The graph is acyclic and connected -/
  isTree : Γ.IsTree
  /-- The number of black strands with each label. -/
  blackStrands : V → ℕ
  /-- Number of red strands-/
  numRed : ℕ
  /-- The number of red strands with each label. -/
  redStrands : Fin numRed → DominantWeight Γ

  /- TODO: finalize KLRWStructure by having blackStrands : SimpleRoots → ℕ -/
  /- have a mapping SimpleRoots → RootCoords so that cartan is applicable.-/

/-- The data carried by a single strand: its label and its color. -/
structure StrandData where
  /-- The label of the strand. -/
  label : V
  /-- The color of the strand. -/
  color : StrandColor
  deriving DecidableEq, Repr

variable {V} in
/-- There are finitely many kinds of strand: a strand is a label together with a color. -/
instance [Fintype V] : Fintype (StrandData V) :=
  Fintype.ofEquiv (V × StrandColor)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun s => (s.label, s.color)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end BasicDefs

variable {V : Type*} [DecidableEq V]

/-! ### Counting strands

These only need to compare strands, so they come before `[Fintype V]` is introduced. -/

/-- The number of strands in `s` with label `k` and color `c`. -/
def numColor {m : ℕ} (s : Fin m → StrandData V) (k : V) (c : StrandColor) : ℕ :=
  (Finset.univ.filter (fun i => s i = ⟨k, c⟩)).card

/-- The number of black strands in `s` with label `k`. -/
abbrev numBlack {m : ℕ} (s : Fin m → StrandData V) (k : V) : ℕ := numColor s k .black

/-- The number of red strands in `s` with label `k`. -/
abbrev numRed {m : ℕ} (s : Fin m → StrandData V) (k : V) : ℕ := numColor s k .red

/-- Rearranging the strands does not change how many have a given label and color. -/
lemma numColor_comp_perm {m : ℕ} (s : Fin m → StrandData V) (e : Equiv.Perm (Fin m))
    (k : V) (c : StrandColor) : numColor (s ∘ e) k c = numColor s k c :=
  Finset.card_equiv e (by simp)

variable [Fintype V] {P : KLRWStructure V}

/-! ### KLRW objects -/

/-- The total number of strands, black and red, in a KLRW structure. -/
abbrev KLRWStructure.numStrands (P : KLRWStructure V) : ℕ :=
  ∑ v : V, (P.blackStrands v + P.redStrands v)

/-- An object of the KLRW category: a sequence of strands in which the number of black and of
red strands with each label is the one prescribed by `P`. -/
@[ext]
structure KLRWObject (P : KLRWStructure V) where
  /-- The strand at each position, from left to right. -/
  strandSeq : Fin P.numStrands → StrandData V
  /-- There are `P.blackStrands i` black strands with label `i`. -/
  corr_num_black : ∀ i : V, P.blackStrands i = numBlack strandSeq i
  /-- There are `P.redStrands i` red strands with label `i`. -/
  corr_num_red : ∀ i : V, P.redStrands i = numRed strandSeq i

/-- There are finitely many KLRW objects, since an object is determined by its strands. -/
noncomputable instance : Fintype (KLRWObject P) :=
  Fintype.ofInjective KLRWObject.strandSeq fun _ _ => KLRWObject.ext

/-! ## Strand generators

Dots, crossings and idempotents, each attached to the object it starts from. They generate the
free algebra whose quotient is the KLRW algebra. -/

/-- The generators of the KLRW algebra. Each one records the object it starts from. -/
inductive StrandGenerator (P : KLRWStructure V) where
  /-- A dot on one strand of an object. -/
  | dot : KLRWObject P → Fin P.numStrands → StrandGenerator P
  /-- A crossing of two adjacent strands of an object. -/
  | cross : KLRWObject P → Fin (P.numStrands - 1) → StrandGenerator P
  /-- The idempotent (identity) of an object. -/
  | idem : KLRWObject P → StrandGenerator P

/-! ### Adjacent strands

A crossing index `i : Fin (n - 1)` names the gap between strands `adjLeft i` and
`adjRight i`; `adjSwap i` swaps those two strands. A braid index `i : Fin (n - 2)` names the
three strands `braidLeft i`, `braidMid i`, `braidRight i` and the two crossings
`braidCrossLeft i`, `braidCrossRight i` between them. -/

/-- The left strand of the adjacent pair indexed by `i`. -/
def adjLeft {n : ℕ} (i : Fin (n - 1)) : Fin n := ⟨i, by omega⟩

/-- The right strand of the adjacent pair indexed by `i`. -/
def adjRight {n : ℕ} (i : Fin (n - 1)) : Fin n := ⟨i + 1, by omega⟩

/-- The position of `adjLeft i` is `i`. -/
@[simp] lemma val_adjLeft {n : ℕ} (i : Fin (n - 1)) : (adjLeft i).val = i.val := rfl

/-- The position of `adjRight i` is `i + 1`. -/
@[simp] lemma val_adjRight {n : ℕ} (i : Fin (n - 1)) : (adjRight i).val = i.val + 1 := rfl

/-- The two strands at a gap are different strands. -/
lemma adjLeft_ne_adjRight {n : ℕ} (i : Fin (n - 1)) : adjLeft i ≠ adjRight i :=
  fun h => by simpa using congrArg Fin.val h

/-- The permutation swapping the two strands on either side of gap `i`. -/
def adjSwap {n : ℕ} (i : Fin (n - 1)) : Equiv.Perm (Fin n) :=
  Equiv.swap (adjLeft i) (adjRight i)

/-- `adjSwap i` on positions: it exchanges `i` and `i + 1` and fixes every other position.
(Still used by the crossing-sequence lemmas in `UBranes.lean`; it can be removed once those go
through `adjSwap_adjLeft`, `adjSwap_adjRight` and `adjSwap_apply_of_ne`.) -/
lemma adjSwap_val {m : ℕ} (i : Fin (m - 1)) (r : Fin m) :
    (adjSwap i r).val =
      if r.val = i.val then i.val + 1 else if r.val = i.val + 1 then i.val else r.val := by
  simp only [adjSwap, Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> simp_all

/-- `adjSwap i` sends the left strand of gap `i` to the right one. -/
@[simp] lemma adjSwap_adjLeft {n : ℕ} (i : Fin (n - 1)) : adjSwap i (adjLeft i) = adjRight i :=
  Equiv.swap_apply_left _ _

/-- `adjSwap i` sends the right strand of gap `i` to the left one. -/
@[simp] lemma adjSwap_adjRight {n : ℕ} (i : Fin (n - 1)) : adjSwap i (adjRight i) = adjLeft i :=
  Equiv.swap_apply_right _ _

/-- `adjSwap i` fixes every strand other than the two at gap `i`. -/
lemma adjSwap_apply_of_ne {n : ℕ} (i : Fin (n - 1)) {r : Fin n}
    (h₁ : r ≠ adjLeft i) (h₂ : r ≠ adjRight i) : adjSwap i r = r :=
  Equiv.swap_apply_of_ne_of_ne h₁ h₂

/-- For a braid index `i : Fin (n - 2)`, the left strand (position `i`). -/
def braidLeft {n : ℕ} (i : Fin (n - 2)) : Fin n := ⟨i, by omega⟩

/-- For a braid index `i : Fin (n - 2)`, the middle strand (position `i + 1`). -/
def braidMid {n : ℕ} (i : Fin (n - 2)) : Fin n := ⟨i + 1, by omega⟩

/-- For a braid index `i : Fin (n - 2)`, the right strand (position `i + 2`). -/
def braidRight {n : ℕ} (i : Fin (n - 2)) : Fin n := ⟨i + 2, by omega⟩

/-- The crossing between the left and middle strands of the braid at `i`. -/
def braidCrossLeft {n : ℕ} (i : Fin (n - 2)) : Fin (n - 1) := ⟨i, by omega⟩

/-- The crossing between the middle and right strands of the braid at `i`. -/
def braidCrossRight {n : ℕ} (i : Fin (n - 2)) : Fin (n - 1) := ⟨i + 1, by omega⟩

/-! The positions of the braid strands and crossings. -/

@[simp] lemma val_braidLeft {n : ℕ} (i : Fin (n - 2)) : (braidLeft i).val = i.val := rfl
@[simp] lemma val_braidMid {n : ℕ} (i : Fin (n - 2)) : (braidMid i).val = i.val + 1 := rfl
@[simp] lemma val_braidRight {n : ℕ} (i : Fin (n - 2)) : (braidRight i).val = i.val + 2 := rfl
@[simp] lemma val_braidCrossLeft {n : ℕ} (i : Fin (n - 2)) :
    (braidCrossLeft i).val = i.val := rfl
@[simp] lemma val_braidCrossRight {n : ℕ} (i : Fin (n - 2)) :
    (braidCrossRight i).val = i.val + 1 := rfl

/-! The strands on either side of each braid crossing. -/

@[simp] lemma adjLeft_braidCrossLeft {n : ℕ} (i : Fin (n - 2)) :
    adjLeft (braidCrossLeft i) = braidLeft i := rfl
@[simp] lemma adjRight_braidCrossLeft {n : ℕ} (i : Fin (n - 2)) :
    adjRight (braidCrossLeft i) = braidMid i := rfl
@[simp] lemma adjLeft_braidCrossRight {n : ℕ} (i : Fin (n - 2)) :
    adjLeft (braidCrossRight i) = braidMid i := rfl
@[simp] lemma adjRight_braidCrossRight {n : ℕ} (i : Fin (n - 2)) :
    adjRight (braidCrossRight i) = braidRight i := rfl

/-! ### Domains and codomains of generators -/

/-- The object a strand generator starts from (the domain of the morphism). -/
def StrandGenerator.domain : StrandGenerator P → KLRWObject P
  | .dot M _ => M
  | .cross M _ => M
  | .idem M => M

/-- The object obtained from `M` by crossing strands `i` and `i + 1` (the codomain of a
crossing). -/
def KLRWObject.afterCross (M : KLRWObject P) (i : Fin (P.numStrands - 1)) : KLRWObject P where
  strandSeq := M.strandSeq ∘ adjSwap i
  corr_num_black v := (M.corr_num_black v).trans (numColor_comp_perm _ _ _ _).symm
  corr_num_red v := (M.corr_num_red v).trans (numColor_comp_perm _ _ _ _).symm

/-- After a crossing at `i`, the strand at position `r` is the one that was at
`adjSwap i r`. -/
@[simp]
lemma KLRWObject.afterCross_strandSeq (M : KLRWObject P) (i : Fin (P.numStrands - 1)) :
    (M.afterCross i).strandSeq = M.strandSeq ∘ adjSwap i := rfl

/-- The object a strand generator ends at (the codomain of the morphism). -/
def StrandGenerator.codomain : StrandGenerator P → KLRWObject P
  | .dot M _ => M
  | .cross M i => M.afterCross i
  | .idem M => M

/-- The free `S`-algebra on the strand generators. -/
abbrev KLRWFreeAlg (S : Type*) [CommRing S] (P : KLRWStructure V) :=
  FreeAlgebra S (StrandGenerator P)

/-! ### Building elements from lists of operations

A `StrandGenOp` is a generator without its starting object. A list of them, read from right to
left, describes a product of generators once a starting object is chosen. -/

section StrandGenOps

variable {S : Type*} [CommRing S]
variable (M : KLRWObject P)

/-- A strand operation without a starting object: a dot, a crossing, or the identity. The
constructors are in the same order as those of `StrandGenerator`. -/
inductive StrandGenOp (P : KLRWStructure V) where
  /-- Put a dot on a strand. -/
  | dot : Fin P.numStrands → StrandGenOp P
  /-- Cross two adjacent strands. -/
  | cross : Fin (P.numStrands - 1) → StrandGenOp P
  /-- Do nothing. -/
  | idem : StrandGenOp P
  deriving Repr

/-- The strand generator that `op` gives when applied to the object `M`. -/
def StrandGenOp.toGenerator : StrandGenOp P → StrandGenerator P
  | .dot i => .dot M i
  | .cross i => .cross M i
  | .idem => .idem M

/-- The object obtained by applying `op` to `M`. -/
def StrandGenOp.apply : StrandGenOp P → KLRWObject P
  | .dot _ => M
  | .cross i => M.afterCross i
  | .idem => M

/-- The generator produced by `op` ends where `op` sends `M`. -/
@[simp]
lemma StrandGenOp.codomain_toGenerator (op : StrandGenOp P) :
    (op.toGenerator M).codomain = op.apply M := by
  cases op <;> rfl

/-- The generator produced by `op` starts at `M`. -/
@[simp]
lemma StrandGenOp.domain_toGenerator (op : StrandGenOp P) :
    (op.toGenerator M).domain = M := by
  cases op <;> rfl

/-- The object reached from `M` after applying `ops`, right to left. -/
def strandGenSeqEnd (M : KLRWObject P) (ops : List (StrandGenOp P)) : KLRWObject P :=
  ops.foldr (fun op N => op.apply N) M

variable (S) in
/-- The product of the generators described by `ops`, applied right to left starting at `M`,
as an element of the free `S`-algebra. `S` is explicit because nothing else in the arguments
determines it. -/
def strandGenSeq (M : KLRWObject P) : List (StrandGenOp P) → KLRWFreeAlg S P
  | [] => FreeAlgebra.ι _ (.idem M)
  | op :: ops =>
      FreeAlgebra.ι _ (op.toGenerator (strandGenSeqEnd M ops)) * strandGenSeq M ops

/-- `strandGenSeq` of a nonempty list: the first operation, applied after the rest. -/
lemma strandGenSeq_cons (op : StrandGenOp P) (ops : List (StrandGenOp P)) :
    strandGenSeq S M (op :: ops) =
      FreeAlgebra.ι _ (op.toGenerator (strandGenSeqEnd M ops)) * strandGenSeq S M ops := rfl

/-! #### Simp lemmas for `strandGenSeqEnd` -/

/-- Applying no operations leaves `M` unchanged. -/
@[simp]
lemma strandGenSeqEnd_nil : strandGenSeqEnd M [] = M := rfl

/-- Applying `ops₁ ++ ops₂` means applying `ops₂` first, then `ops₁`. -/
lemma strandGenSeqEnd_append (ops₁ ops₂ : List (StrandGenOp P)) :
    strandGenSeqEnd M (ops₁ ++ ops₂) = strandGenSeqEnd (strandGenSeqEnd M ops₂) ops₁ := by
  simp only [strandGenSeqEnd, List.foldr_append]

/-- A crossing at the end of the list is applied first. -/
@[simp]
lemma strandGenSeqEnd_cross (i : Fin (P.numStrands - 1)) (ops : List (StrandGenOp P)) :
    strandGenSeqEnd M (ops ++ [.cross i]) = strandGenSeqEnd (M.afterCross i) ops :=
  strandGenSeqEnd_append M ops [.cross i]

/-- A crossing at the front of the list is applied last. -/
@[simp]
lemma cross_strandGenSeqEnd (i : Fin (P.numStrands - 1)) (ops : List (StrandGenOp P)) :
    strandGenSeqEnd M (.cross i :: ops) = (strandGenSeqEnd M ops).afterCross i := rfl

/-- A dot at the end of the list does not change the resulting object. -/
@[simp]
lemma strandGenSeqEnd_dot (i : Fin P.numStrands) (ops : List (StrandGenOp P)) :
    strandGenSeqEnd M (ops ++ [.dot i]) = strandGenSeqEnd M ops :=
  strandGenSeqEnd_append M ops [.dot i]

/-- A dot at the front of the list does not change the resulting object. -/
@[simp]
lemma dot_strandGenSeqEnd (i : Fin P.numStrands) (ops : List (StrandGenOp P)) :
    strandGenSeqEnd M (.dot i :: ops) = strandGenSeqEnd M ops := rfl

/-- An identity at the end of the list does not change the resulting object. -/
@[simp]
lemma strandGenSeqEnd_idem (ops : List (StrandGenOp P)) :
    strandGenSeqEnd M (ops ++ [.idem]) = strandGenSeqEnd M ops :=
  strandGenSeqEnd_append M ops [.idem]

/-- An identity at the front of the list does not change the resulting object. -/
@[simp]
lemma idem_strandGenSeqEnd (ops : List (StrandGenOp P)) :
    strandGenSeqEnd M (.idem :: ops) = strandGenSeqEnd M ops := rfl

end StrandGenOps

/-! ## Relations between strand morphisms -/

open FreeAlgebra

section Relations

variable {S : Type*} [CommRing S]

/-! ### Conditions used by the relations -/

/-- The two strands at gap `i` are both black. -/
def BothBlack (M : KLRWObject P) (i : Fin (P.numStrands - 1)) : Prop :=
  (M.strandSeq (adjLeft i)).color = .black ∧ (M.strandSeq (adjRight i)).color = .black

/-- The two strands at gap `i` have the same label. -/
def SameLabel (M : KLRWObject P) (i : Fin (P.numStrands - 1)) : Prop :=
  (M.strandSeq (adjLeft i)).label = (M.strandSeq (adjRight i)).label

/-- Braid correction case: three black strands, the outer two with the same label, and
`Γ.Adj middle left`. -/
def BraidNeighborLeft (M : KLRWObject P) (i : Fin (P.numStrands - 2)) : Prop :=
  (M.strandSeq (braidLeft i)).color = .black ∧ (M.strandSeq (braidMid i)).color = .black ∧
  (M.strandSeq (braidRight i)).color = .black ∧
  (M.strandSeq (braidLeft i)).label = (M.strandSeq (braidRight i)).label ∧
  P.Γ.Adj (M.strandSeq (braidMid i)).label (M.strandSeq (braidLeft i)).label

/-- Braid correction case: three black strands, the outer two with the same label, and
`Γ.Adj left middle`. -/
def BraidNeighborRight (M : KLRWObject P) (i : Fin (P.numStrands - 2)) : Prop :=
  (M.strandSeq (braidLeft i)).color = .black ∧ (M.strandSeq (braidMid i)).color = .black ∧
  (M.strandSeq (braidRight i)).color = .black ∧
  (M.strandSeq (braidLeft i)).label = (M.strandSeq (braidRight i)).label ∧
  P.Γ.Adj (M.strandSeq (braidLeft i)).label (M.strandSeq (braidMid i)).label

/-- Braid correction case: black outer strands with the same label, and a red middle strand
with that label too. -/
def BraidRedMiddle (M : KLRWObject P) (i : Fin (P.numStrands - 2)) : Prop :=
  (M.strandSeq (braidLeft i)).color = .black ∧ (M.strandSeq (braidMid i)).color = .red ∧
  (M.strandSeq (braidRight i)).color = .black ∧
  (M.strandSeq (braidLeft i)).label = (M.strandSeq (braidRight i)).label ∧
  (M.strandSeq (braidMid i)).label = (M.strandSeq (braidLeft i)).label

/-- The braid at `i` has a correction term. These are exactly the cases of
`KLRWExplicitConRel.braid_with_neighbor_j_to_i`,
`KLRWExplicitConRel.braid_with_neighbor_i_to_j` and
`KLRWExplicitConRel.braid_with_red`; the plain `KLRWImplicitConRel.braid` relation covers every
other case. -/
def BraidHasCorrection (M : KLRWObject P) (i : Fin (P.numStrands - 2)) : Prop :=
  BraidNeighborLeft M i ∨ BraidNeighborRight M i ∨ BraidRedMiddle M i

/-! ### Implicit relations -/

/-- The KLRW relations not drawn in Figure 1 of LePage–Shende: the bookkeeping relations for
idempotents and mismatched compositions, the commutation relations, and the cases where strands
pass through each other freely. None of them involves the parameters `u` and `ℏ`. -/
inductive KLRWImplicitConRel : KLRWFreeAlg S P → KLRWFreeAlg S P → Prop where
  /-- A dot on a red strand is zero. -/
  | dot_on_red : ∀ (M : KLRWObject P) (i : Fin P.numStrands),
      (M.strandSeq i).color = .red →
      KLRWImplicitConRel (strandGenSeq S M [.dot i]) 0
  /-- A crossing of two red strands is zero. -/
  | cross_two_red : ∀ (M : KLRWObject P) (i : Fin (P.numStrands - 1)),
      (M.strandSeq (adjLeft i)).color = .red →
      (M.strandSeq (adjRight i)).color = .red →
      KLRWImplicitConRel (strandGenSeq S M [.cross i]) 0
  /-- A composition with mismatched domain and codomain is zero.
  Here `g * f` means "first `f`, then `g`". -/
  | bad_comp : ∀ (f g : StrandGenerator P),
      f.codomain ≠ g.domain →
      KLRWImplicitConRel (ι _ g * ι _ f) 0
  /-- `idem M` is a left identity for generators ending at `M`. -/
  | idem_left : ∀ (M : KLRWObject P) (f : StrandGenerator P),
      f.codomain = M →
      KLRWImplicitConRel (ι _ (.idem M) * ι _ f) (ι _ f)
  /-- `idem M` is a right identity for generators starting at `M`. -/
  | idem_right : ∀ (M : KLRWObject P) (f : StrandGenerator P),
      f.domain = M →
      KLRWImplicitConRel (ι _ f * ι _ (.idem M)) (ι _ f)
  /-- The identity is the sum of all the idempotents. -/
  | id_sum :
      KLRWImplicitConRel (∑ M : KLRWObject P, ι _ (.idem M)) 1
  /-- Crossings that are far apart commute. -/
  | cross_cross_comm : ∀ (M : KLRWObject P) (i j : Fin (P.numStrands - 1)),
      i.val + 1 < j.val ∨ j.val + 1 < i.val →
      KLRWImplicitConRel
        (strandGenSeq S M [.cross j, .cross i])
        (strandGenSeq S M [.cross i, .cross j])
  /-- Dots commute. -/
  | dot_dot_comm : ∀ (M : KLRWObject P) (i j : Fin P.numStrands),
      KLRWImplicitConRel
        (strandGenSeq S M [.dot j, .dot i])
        (strandGenSeq S M [.dot i, .dot j])
  /-- A dot on a strand not involved in a crossing commutes with that crossing. -/
  | cross_dot_far_comm : ∀ (M : KLRWObject P) (i : Fin (P.numStrands - 1))
      (j : Fin P.numStrands),
      j ≠ adjLeft i →
      j ≠ adjRight i →
      KLRWImplicitConRel
        (strandGenSeq S M [.dot j, .cross i])
        (strandGenSeq S M [.cross i, .dot j])
  /-- Unless the two strands are black with the same label, a dot slides along its strand
  through a crossing: a dot on the right strand before the crossing equals a dot on the left
  strand after it. -/
  | dot_follows_strand_left : ∀ (M : KLRWObject P) (i : Fin (P.numStrands - 1)),
      ¬ (BothBlack M i ∧ SameLabel M i) →
      KLRWImplicitConRel
        (strandGenSeq S M [.dot (adjLeft i), .cross i])
        (strandGenSeq S M [.cross i, .dot (adjRight i)])
  /-- Unless the two strands are black with the same label, a dot slides along its strand
  through a crossing: a dot on the left strand before the crossing equals a dot on the right
  strand after it. -/
  | dot_follows_strand_right : ∀ (M : KLRWObject P) (i : Fin (P.numStrands - 1)),
      ¬ (BothBlack M i ∧ SameLabel M i) →
      KLRWImplicitConRel
        (strandGenSeq S M [.dot (adjRight i), .cross i])
        (strandGenSeq S M [.cross i, .dot (adjLeft i)])
  /-- Two black strands with different, non-adjacent labels crossing twice is the identity. -/
  | bigon_not_adjacent : ∀ (M : KLRWObject P) (i : Fin (P.numStrands - 1)),
      (M.strandSeq (adjLeft i)).color = .black →
      (M.strandSeq (adjRight i)).color = .black →
      (M.strandSeq (adjLeft i)).label ≠ (M.strandSeq (adjRight i)).label →
      ¬ P.Γ.Adj (M.strandSeq (adjLeft i)).label (M.strandSeq (adjRight i)).label →
      ¬ P.Γ.Adj (M.strandSeq (adjRight i)).label (M.strandSeq (adjLeft i)).label →
      KLRWImplicitConRel (strandGenSeq S M [.cross i, .cross i]) (ι _ (.idem M))
  /-- A black and a red strand with different labels crossing twice is the identity. -/
  | bigon_black_red_diff : ∀ (M : KLRWObject P) (i : Fin (P.numStrands - 1)),
      (M.strandSeq (adjLeft i)).color ≠ (M.strandSeq (adjRight i)).color →
      (M.strandSeq (adjLeft i)).label ≠ (M.strandSeq (adjRight i)).label →
      KLRWImplicitConRel (strandGenSeq S M [.cross i, .cross i]) (ι _ (.idem M))
  /-- Without a correction term, the two sides of a braid are equal. -/
  | braid : ∀ (M : KLRWObject P) (i : Fin (P.numStrands - 2)),
      ¬ BraidHasCorrection M i →
      KLRWImplicitConRel
        (strandGenSeq S M [.cross (braidCrossLeft i), .cross (braidCrossRight i),
          .cross (braidCrossLeft i)])
        (strandGenSeq S M [.cross (braidCrossRight i), .cross (braidCrossLeft i),
          .cross (braidCrossRight i)])

/-! ### Explicit relations -/

/-- The nontrivial KLRW relations, drawn in Figure 1 of LePage–Shende and labeled (a)–(g) as
there. They involve the parameters `u ℏ : S`. -/
inductive KLRWExplicitConRel (u ℏ : S) : KLRWFreeAlg S P → KLRWFreeAlg S P → Prop where
  /-- (a) Two black strands with the same label crossing twice is zero. -/
  | bigon : ∀ (M : KLRWObject P) (i : Fin (P.numStrands - 1)),
      BothBlack M i → SameLabel M i →
      KLRWExplicitConRel u ℏ (strandGenSeq S M [.cross i, .cross i]) 0
  /-- (b) Bigon of black strands with `Γ.Adj left right`. -/
  | bigon_for_j_to_i : ∀ (M : KLRWObject P) (i : Fin (P.numStrands - 1)),
      BothBlack M i →
      P.Γ.Adj (M.strandSeq (adjLeft i)).label (M.strandSeq (adjRight i)).label →
      KLRWExplicitConRel u ℏ
        (strandGenSeq S M [.cross i, .cross i])
        (u • (strandGenSeq S M [.dot (adjRight i)] - strandGenSeq S M [.dot (adjLeft i)]))
  /-- (b) Bigon of black strands with `Γ.Adj right left`. -/
  | bigon_for_i_to_j : ∀ (M : KLRWObject P) (i : Fin (P.numStrands - 1)),
      BothBlack M i →
      P.Γ.Adj (M.strandSeq (adjRight i)).label (M.strandSeq (adjLeft i)).label →
      KLRWExplicitConRel u ℏ
        (strandGenSeq S M [.cross i, .cross i])
        (u • (strandGenSeq S M [.dot (adjLeft i)] - strandGenSeq S M [.dot (adjRight i)]))
  /-- (c) Bigon with a red strand on the left, both strands with the same label. -/
  | bigon_with_red_left : ∀ (M : KLRWObject P) (i : Fin (P.numStrands - 1)),
      SameLabel M i →
      (M.strandSeq (adjLeft i)).color = .red →
      (M.strandSeq (adjRight i)).color = .black →
      KLRWExplicitConRel u ℏ
        (strandGenSeq S M [.cross i, .cross i])
        (u • strandGenSeq S M [.dot (adjRight i)])
  /-- (c) Bigon with a red strand on the right, both strands with the same label. -/
  | bigon_with_red_right : ∀ (M : KLRWObject P) (i : Fin (P.numStrands - 1)),
      SameLabel M i →
      (M.strandSeq (adjLeft i)).color = .black →
      (M.strandSeq (adjRight i)).color = .red →
      KLRWExplicitConRel u ℏ
        (strandGenSeq S M [.cross i, .cross i])
        (u • strandGenSeq S M [.dot (adjLeft i)])
  /-- (d) Braid with a neighboring label: outer strands `(i)`, middle strand `(j)`, with the arrow
  `(j) → (i)` (`Γ.Adj middle left`). -/
  | braid_with_neighbor_j_to_i : ∀ (M : KLRWObject P) (i : Fin (P.numStrands - 2)),
      BraidNeighborLeft M i →
      KLRWExplicitConRel u ℏ
        (strandGenSeq S M [.cross (braidCrossLeft i), .cross (braidCrossRight i),
            .cross (braidCrossLeft i)] -
          strandGenSeq S M [.cross (braidCrossRight i), .cross (braidCrossLeft i),
            .cross (braidCrossRight i)])
        ((u * ℏ) • ι _ (.idem M))
  /-- (d) Braid with a neighboring label, with the arrow reversed: `(i) → (j)`
  (`Γ.Adj left middle`). As in the caption of Figure 1, the right-hand side gets an extra
  sign. -/
  | braid_with_neighbor_i_to_j : ∀ (M : KLRWObject P) (i : Fin (P.numStrands - 2)),
      BraidNeighborRight M i →
      KLRWExplicitConRel u ℏ
        (strandGenSeq S M [.cross (braidCrossLeft i), .cross (braidCrossRight i),
            .cross (braidCrossLeft i)] -
          strandGenSeq S M [.cross (braidCrossRight i), .cross (braidCrossLeft i),
            .cross (braidCrossRight i)])
        ((-(u * ℏ)) • ι _ (.idem M))
  /-- (e) Braid around a red middle strand with the same label as the outer strands. -/
  | braid_with_red : ∀ (M : KLRWObject P) (i : Fin (P.numStrands - 2)),
      BraidRedMiddle M i →
      KLRWExplicitConRel u ℏ
        (strandGenSeq S M [.cross (braidCrossLeft i), .cross (braidCrossRight i),
            .cross (braidCrossLeft i)] -
          strandGenSeq S M [.cross (braidCrossRight i), .cross (braidCrossLeft i),
            .cross (braidCrossRight i)])
        ((u * ℏ) • ι _ (.idem M))
  /-- (f) A dot passing a crossing of two black strands with the same label
  (the same diagrams as `KLRWImplicitConRel.dot_follows_strand_left`). -/
  | dot_pass_cross_left : ∀ (M : KLRWObject P) (i : Fin (P.numStrands - 1)),
      BothBlack M i → SameLabel M i →
      KLRWExplicitConRel u ℏ
        (strandGenSeq S M [.dot (adjLeft i), .cross i] -
          strandGenSeq S M [.cross i, .dot (adjRight i)])
        (ℏ • ι _ (.idem M))
  /-- (g) A dot passing a crossing of two black strands with the same label
  (the same diagrams as `KLRWImplicitConRel.dot_follows_strand_right`). -/
  | dot_pass_cross_right : ∀ (M : KLRWObject P) (i : Fin (P.numStrands - 1)),
      BothBlack M i → SameLabel M i →
      KLRWExplicitConRel u ℏ
        (strandGenSeq S M [.cross i, .dot (adjLeft i)] -
          strandGenSeq S M [.dot (adjRight i), .cross i])
        (ℏ • ι _ (.idem M))

end Relations

/-! ## The KLRW algebra -/

section Algebra

variable {S : Type*} [CommRing S] (u ℏ : S)

/-- The smallest ring congruence on the free algebra containing all the KLRW relations. -/
def klrwRel (P : KLRWStructure V) : RingCon (KLRWFreeAlg S P) :=
  ringConGen (fun x y => KLRWImplicitConRel x y ∨ KLRWExplicitConRel u ℏ x y)

/-- The KLRW algebra with coefficients in `S` and parameters `u`, `ℏ`. -/
abbrev KLRWAlg (P : KLRWStructure V) :=
  (klrwRel u ℏ P).Quotient

/-- The idempotent `e_X` of the object `X` in the KLRW algebra. -/
def idemMorph (X : KLRWObject P) : KLRWAlg u ℏ P :=
  (klrwRel u ℏ P).mk' (ι S (.idem X))

/-- The morphisms from `X` to `Y`: the elements of the form `e_Y * a * e_X`. -/
def klrwHom (X Y : KLRWObject P) : Submodule S (KLRWAlg u ℏ P) :=
  LinearMap.range ((LinearMap.mulLeft S (idemMorph u ℏ Y)).comp
    (LinearMap.mulRight S (idemMorph u ℏ X)))

end Algebra

/-! ### The universal KLRW algebra

Taking `S = R[u, ℏ]` with `u = X 0` and `ℏ = X 1` gives the construction with formal
parameters. Every other choice of `u` and `ℏ` should be a specialization of this one; that is
not proved here yet (see issue #75). -/

section Universal

variable (R : Type*) [CommRing R]

/-- The parameter `u` in the universal coefficient ring `R[u, ℏ]`. -/
noncomputable abbrev univU : MvPolynomial (Fin 2) R := MvPolynomial.X 0

/-- The parameter `ℏ` in the universal coefficient ring `R[u, ℏ]`. -/
noncomputable abbrev univHbar : MvPolynomial (Fin 2) R := MvPolynomial.X 1

/-- The universal KLRW algebra over `R`, with coefficients in `R[u, ℏ]`. -/
abbrev KLRWAlgUniv (P : KLRWStructure V) :=
  KLRWAlg (univU R) (univHbar R) P

end Universal
end KLRW
