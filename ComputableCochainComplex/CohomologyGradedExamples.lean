/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.CohomologyOneBlackStrand

/-! # Graded diagrammatic acceptance tests

The cohomological degree is the target degree one of `T₀ --2·id--> T₀`.
At internal degree two the representative of its nonzero `ℤ/2` class is the one-dot diagram.
The shifted example checks the convention `M⟨s⟩_q = M_(q+s)`.
-/

@[expose] public section

namespace ComputableCohomology.OneBlackStrand.Examples

open CategoryTheory AInfinityTheory
open scoped Matrix

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The black strand lies to the left of the one red strand. -/
def leftObject : KLRWCategory 1 ℤ := ⟨0⟩

/-- The black strand lies to the right of the one red strand. -/
def rightObject : KLRWCategory 1 ℤ := ⟨1⟩

example : size leftObject rightObject 0 = 0 := by decide +kernel
example : size leftObject rightObject 1 = 1 := by decide +kernel
example : size leftObject rightObject 3 = 1 := by decide +kernel
example : size leftObject rightObject (-1) = 0 := by decide +kernel

example : CategoryStruct.comp (X := leftObject) (Y := rightObject) (Z := leftObject)
    (DFinsupp.single 0 (2 : ℤ)) (DFinsupp.single 0 (3 : ℤ)) = DFinsupp.single 1 (6 : ℤ) :=
  single_comp_single leftObject rightObject leftObject 0 0 2 3

example : (gradedCoordinates (R := ℤ) (n := 1)).compose
    leftObject rightObject leftObject 1 1 (fun _ => 2) (fun _ => 3) = fun _ => 6 := by
  decide +kernel

example : (scalarCoordinates leftObject (2 : ℤ) 2 0).incoming = fun _ _ => 2 := by
  decide +kernel

/-- Computed integral cohomology of the actual homogeneous strand modules. -/
def strandTwo : IntegerCohomologyCertificate
    (scalarCoordinates leftObject (2 : ℤ) 2 0).incoming
    (scalarCoordinates leftObject (2 : ℤ) 2 0).outgoing :=
  (computeInteger _ _).toOption.get (by decide +kernel)

example : strandTwo.quotient.freeRank = 0 := by decide +kernel
example : strandTwo.quotient.torsionFactors = [2] := by decide +kernel

/-- The nonzero class is represented by the original one-dot strand diagram. -/
lemma strandTwo_representative :
    ((scalarCoordinates leftObject (2 : ℤ) 2 0).integerRepresentative strandTwo
      (strandTwo.normalize ![1])).val = DFinsupp.single 1 (1 : ℤ) := by
  change @Eq (StrandSpace ℤ) _ _
  decide +kernel

/-- The computed group is explicitly `ℤ/2`, not only a report of an invariant factor. -/
def strandTwoEquiv : strandTwo.Model ≃ₗ[ℤ] ZMod 2 := by
  refine strandTwo.quotient.splitEquiv.symm.trans
    (show strandTwo.quotient.Coordinates ≃ₗ[ℤ] ZMod 2 from ?_)
  change (∀ i, ZMod (strandTwo.quotient.diagonal i)) ≃ₗ[ℤ] ZMod 2
  rw [show strandTwo.quotient.diagonal = fun _ => 2 from by decide +kernel]
  exact (LinearEquiv.funCongrLeft ℤ (ZMod 2) (finCongr (by decide +kernel))).trans
    (LinearEquiv.funUnique (Fin 1) ℤ (ZMod 2))

example : Nonempty ((scalarPiece leftObject (2 : ℤ) 2 0).homology ≅ ModuleCat.of ℤ (ZMod 2)) :=
  ⟨(scalarCoordinates leftObject (2 : ℤ) 2 0).integerHomologyIso strandTwo ≪≫
    strandTwoEquiv.toModuleIso⟩

example : (strandTwo.boundaryPreimage ![2] (by decide +kernel)).map
    (fun y => y.val ⟨0, by decide +kernel⟩) = some 1 := by decide +kernel

example : (scalarCoordinates leftObject (2 : ℤ) 4 (-2)).incoming = fun _ _ => 2 := by
  decide +kernel

example : ((computeInteger (scalarCoordinates leftObject (2 : ℤ) 1 0).incoming
    (scalarCoordinates leftObject (2 : ℤ) 1 0).outgoing).toOption.get
      (by decide +kernel)).quotient.freeRank = 0 := by decide +kernel

end ComputableCohomology.OneBlackStrand.Examples
