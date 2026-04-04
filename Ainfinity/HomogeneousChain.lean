module

public import Mathlib
public import Ainfinity.Grading

@[expose] public section

namespace AInfinityCategoryTheory

/- Chain policy (18 Sep 2025)
based on advice of Kim Morrison

A GQuiver is turned into an ordinary Quiver object whose arrows
are additionally labeled with their degree. Then a homogeneous
chain is defined as a Quiver.Path object on that quiver.
-/

universe u v w

-- bundle degree with the arrow so we can use plain `Quiver.Path`
def toQuiver {β : Type u} {obj : Type v} (gquiver : GQuiver.{u, v, w} β obj) : Quiver obj where
  Hom X Y := Σ d : β, gquiver.data X Y d

abbrev HomogeneousChain {β : Type u} {obj : Type v} {gquiver : GQuiver.{u, v, w} β obj} (X : obj) (Y : obj) :=
  @Quiver.Path obj (toQuiver gquiver) X Y

def total_deg {β : Type u} [GradingCore β] {obj : Type v} {gquiver : GQuiver.{u, v, w} β obj} {X : obj} {Y : obj} (chain : HomogeneousChain (gquiver := gquiver) X Y) : β :=
  match chain with
  | @Quiver.Path.nil obj (toQuiver gquiver) _ => (0 : β)
  | @Quiver.Path.cons obj (toQuiver gquiver) _ _ _ most ⟨d, mor⟩ => (total_deg most) + d

def correct_output_deg {β : Type u} [inst : GradingCore β] {obj : Type v} {gquiver : GQuiver.{u, v, w} β obj} {X : obj} {Y : obj} (chain : HomogeneousChain (gquiver := gquiver) X Y) : β :=
  let path : @Quiver.Path obj (toQuiver gquiver) X Y := chain
  let len := @Quiver.Path.length obj (toQuiver gquiver) X Y path
  total_deg chain + (inst.deg_cast (nat_to_correct_type inst.kind (2 - (len : ℤ))))

end AInfinityCategoryTheory
