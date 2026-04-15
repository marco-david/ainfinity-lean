module

public import Mathlib

@[expose] public section

open ChainComplex CategoryTheory DirectSum GradedMonoid GradedObject

namespace AInfinityCategoryTheory

universe u v w

-- Specific names like `GradingIndex` are better than names like `Grading`.
class GradingIndex (β : Type u) extends AddCommGroupWithOne β where
  -- We want this to be in the project namespace rather than just the `GraidngIndex` namespace,
  -- so we define it to be `protected` here and then redefine it in the root namespace.
  -- `export` is another way to achieve something similar.
  -- Also, it is best to avoid unnecessary abbreviations like `Parity` for `ZMod 2`.
  protected parity : β →+ ZMod 2
  -- This is sufficient to prove `parity_intCast`, so it is better to add the easier to prove
  -- hypothesis here and prove the generalization from it later.
  protected parity_one : parity 1 = 1

def parity {β : Type u} [GradingIndex β] : β →+ ZMod 2 := GradingIndex.parity

/--
This is declared as a `@[simp]` lemma because it is an acceptable "greedy" rewriting rule, meaning
it is always safe to apply and the right-hand side is less complex than the left-hand side.
Acceptable greedy rewriting rules should almost always be tagged as `@[simp]` provided they preserve
a property known as confluence.
-/
@[simp]
theorem parity_one {β : Type u} [GradingIndex β] : parity (1 : β) = 1 := GradingIndex.parity_one

@[simp]
theorem parity_intCast {β : Type u} [GradingIndex β] (n : ℤ) : parity (n : β) = (n : ZMod 2) := by
  rw [← zsmul_one, map_zsmul, parity_one, zsmul_one]

class GQuiver (β : Type u) (obj : Type v) where
  /-- The type of morphisms between a given source and target. -/
  data : obj → obj → GradedObject β (Type w)

end AInfinityCategoryTheory
