module

public import Mathlib
public import KLRW.UBranes

/-!
# The cube complex of a U-brane diagram

Turns a commutative cube in a preadditive category into an iterated complex, and applies this to
the cube of a U-brane diagram and to the stages of a peeling.

## Main definitions

* `KLRW.CubeData K m`: commutative `m`-dimensional cubes in `K`, and the category they form.
* `KLRW.CubeData.split`: an `(m + 1)`-cube as a morphism between two `m`-cubes.
* `KLRW.twoTermFunctor`: the two-term complex of a morphism.
* `KLRW.cubeToComplex`: the functor from `m`-cubes to `m`-fold iterated complexes.
* `KLRW.klrwCubeData` and `KLRW.klrwComplex`: the cube and the iterated complex of a U-brane
  diagram.
* `KLRW.peelComplexHom` and `KLRW.peelChainComplex`: the maps between the stages of a peeling,
  and the chain complex they form.

## Implementation notes

* An `(m + 1)`-fold iterated complex is a two-term complex of `m`-fold iterated complexes, of
  shape `twoTermShape` (one differential, from `0` to `1`). The cube is not totalized here.
* Two proofs are still missing (`sorry`): that the squares of `klrwCubeData` commute, and that
  the stage maps of a peeling commute with the edges (`peelCubeHom`).
* `peelChainComplex` assumes that consecutive stage maps compose to zero.
-/

@[expose] public section

namespace KLRW

/-! ## From cubes to iterated complexes -/

open CategoryTheory Limits FreeAlgebra

section IteratedComplexes

/-- A bundled preadditive category. -/
structure PreadCat where
  /-- The objects of the category. -/
  carrier : Type
  [instCategory : Category carrier]
  [instPreadditive : Preadditive carrier]

attribute [instance] PreadCat.instCategory PreadCat.instPreadditive

/-- The category of `d`-fold iterated complexes of shape `shape` over `C`. -/
def iteratedPreadCat {A : Type} (shape : ComplexShape A) (C : PreadCat) : ℕ → PreadCat
  | 0 => C
  | d + 1 =>
      let prev := iteratedPreadCat shape C d
      { carrier := HomologicalComplex prev.carrier shape }

/-- The type of `d`-fold iterated complexes of shape `shape` over `C`. -/
abbrev IteratedComplex {A : Type} (shape : ComplexShape A) (C : PreadCat) (d : ℕ) : Type :=
  (iteratedPreadCat shape C d).carrier

/-- A `(d + 1)`-fold iterated complex, seen as a complex of `d`-fold iterated complexes. -/
abbrev IteratedComplex.unfold {A : Type} {shape : ComplexShape A} {C : PreadCat} {d : ℕ}
    (X : IteratedComplex shape C (d + 1)) :
    HomologicalComplex (IteratedComplex shape C d) shape :=
  X

end IteratedComplexes

/-- The complex shape of a two-term complex: a single differential from `0` to `1`. -/
def twoTermShape : ComplexShape (Fin 2) where
  Rel i j := i = 0 ∧ j = 1
  next_eq := by
    intro i j k ⟨hij1, hij2⟩ ⟨hjk1, hjk2⟩
    simp only [Fin.ext_iff] at *
    omega
  prev_eq := by
    intro i j k ⟨hij1, hij2⟩ ⟨hki1, hki2⟩
    simp only [Fin.ext_iff] at *
    omega

/-- In `twoTermShape`, the only differential goes from `0` to `1`. -/
@[simp] lemma twoTermShape_rel (i j : Fin 2) :
    twoTermShape.Rel i j ↔ i = 0 ∧ j = 1 := Iff.rfl

/-- A commutative `m`-dimensional cube in the category `K`: an object at each vertex, a
morphism along each edge, and commuting squares. -/
structure CubeData (K : Type*) [Category K] (m : ℕ) where
  /-- The object at each vertex. -/
  obj : CubeVertex m → K
  /-- The morphism along each edge. -/
  edge : ∀ {v w : CubeVertex m}, IsEdge v w → (obj v ⟶ obj w)
  /-- Every square commutes. -/
  square : ∀ {v w₁ w₂ u : CubeVertex m}
    (h₁ : IsEdge v w₁) (h₂ : IsEdge w₁ u) (h₃ : IsEdge v w₂) (h₄ : IsEdge w₂ u),
    edge h₁ ≫ edge h₂ = edge h₃ ≫ edge h₄

namespace CubeData

variable {K : Type*} [Category K] {m : ℕ}

/-- A morphism of cubes: a morphism at each vertex, commuting with the edges. -/
@[ext]
structure Hom (D D' : CubeData K m) where
  /-- The morphism at each vertex. -/
  app : ∀ v, D.obj v ⟶ D'.obj v
  /-- The vertex morphisms commute with the edges. -/
  comm : ∀ {v w : CubeVertex m} (h : IsEdge v w), D.edge h ≫ app w = app v ≫ D'.edge h

/-- The identity morphism of a cube. -/
def Hom.id (D : CubeData K m) : Hom D D where
  app _ := 𝟙 _
  comm _ := by simp

/-- The composition of two morphisms of cubes. -/
def Hom.comp {D D' D'' : CubeData K m} (f : Hom D D') (g : Hom D' D'') : Hom D D'' where
  app v := f.app v ≫ g.app v
  comm h := by
    rw [← Category.assoc, f.comm h, Category.assoc, g.comm h, ← Category.assoc]

/-- Cubes in `K` form a category. -/
instance category : Category (CubeData K m) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext (funext fun _ => Category.id_comp _)
  comp_id _ := Hom.ext (funext fun _ => Category.comp_id _)
  assoc _ _ _ := Hom.ext (funext fun _ => Category.assoc _ _ _)

/-- Two morphisms of cubes are equal if they agree at every vertex. -/
@[ext]
lemma hom_ext {D D' : CubeData K m} {f g : D ⟶ D'} (h : ∀ v, f.app v = g.app v) : f = g :=
  Hom.ext (funext h)

/-- The face of an `(m + 1)`-cube where the first coordinate is `b`. For a `3`-cube, `face D 0`
contains the vertices `000, 001, 010, 011` and `face D 1` the vertices `100, 101, 110, 111`,
together with the edges and squares lying inside each face. -/
def face (D : CubeData K (m + 1)) (b : Fin 2) : CubeData K m where
  obj v := D.obj (vcons b v)
  edge h := D.edge (h.cons b)
  square h₁ h₂ h₃ h₄ := D.square (h₁.cons b) (h₂.cons b) (h₃.cons b) (h₄.cons b)

/-- The morphism from `face D 0` to `face D 1` given by the edges in direction `0`. -/
def dir0 (D : CubeData K (m + 1)) : D.face 0 ⟶ D.face 1 where
  app v := D.edge (IsEdge.dir0 v)
  comm h := D.square (h.cons 0) (IsEdge.dir0 _) (IsEdge.dir0 _) (h.cons 1)

/-- The morphism between faces induced by a morphism of cubes. -/
def Hom.face {D D' : CubeData K (m + 1)} (f : D ⟶ D') (b : Fin 2) :
    D.face b ⟶ D'.face b where
  app v := f.app (vcons b v)
  comm h := f.comm (h.cons b)

variable (K) in
/-- Splitting an `(m + 1)`-cube into its two faces and the morphism `dir0` between them. -/
def split (m : ℕ) : CubeData K (m + 1) ⥤ Arrow (CubeData K m) where
  obj D := Arrow.mk D.dir0
  map f :=
    { left := Hom.face f 0
      right := Hom.face f 1
      w := by ext v; exact (f.comm (IsEdge.dir0 v)).symm }
  map_id _ := rfl
  map_comp _ _ := rfl

end CubeData

section TwoTerm

variable {D : Type*} [Category D] [HasZeroMorphisms D]

/-- The differentials of `twoTerm φ`: `φ` from `0` to `1`, and zero otherwise. -/
def twoTermD {X₀ X₁ : D} (φ : X₀ ⟶ X₁) : (i j : Fin 2) → (![X₀, X₁] i ⟶ ![X₀, X₁] j)
  | 0, 1 => φ
  | _, _ => 0

/-- The two-term complex `X₀ ⟶ X₁` with differential `φ`. -/
def twoTerm {X₀ X₁ : D} (φ : X₀ ⟶ X₁) : HomologicalComplex D twoTermShape where
  X := ![X₀, X₁]
  d := twoTermD φ
  shape i j hij := by fin_cases i <;> fin_cases j <;> first | rfl | simp at hij
  d_comp_d' := by
    rintro i j k ⟨-, rfl⟩ ⟨h, -⟩
    simp at h

/-- The components of `twoTermHom a b w`: `a` in degree `0` and `b` in degree `1`. -/
def twoTermHomComponents {X₀ X₁ Y₀ Y₁ : D} (a : X₀ ⟶ Y₀) (b : X₁ ⟶ Y₁) :
    (i : Fin 2) → (![X₀, X₁] i ⟶ ![Y₀, Y₁] i)
  | 0 => a
  | 1 => b

/-- The morphism of two-term complexes `twoTerm φ ⟶ twoTerm ψ` with components `a` and `b`,
given that the square `a ≫ ψ = φ ≫ b` commutes. -/
def twoTermHom {X₀ X₁ Y₀ Y₁ : D} {φ : X₀ ⟶ X₁} {ψ : Y₀ ⟶ Y₁}
    (a : X₀ ⟶ Y₀) (b : X₁ ⟶ Y₁) (w : a ≫ ψ = φ ≫ b) : twoTerm φ ⟶ twoTerm ψ where
  f := twoTermHomComponents a b
  comm' := by
    rintro i j ⟨rfl, rfl⟩
    exact w

variable (D) in
/-- The functor sending an arrow `φ : X₀ ⟶ X₁` of `D` to the two-term complex `twoTerm φ`. -/
def twoTermFunctor : Arrow D ⥤ HomologicalComplex D twoTermShape where
  obj φ := twoTerm φ.hom
  map sq := twoTermHom sq.left sq.right (Arrow.w sq)
  map_id _ := by ext i; fin_cases i <;> rfl
  map_comp _ _ := by ext i; fin_cases i <;> rfl

end TwoTerm

/-- The functor from `m`-cubes to `m`-fold iterated complexes. An `(m + 1)`-cube is split into
two `m`-cubes and a morphism between them (`CubeData.split`), each part is turned into an
iterated complex by recursion, and the result is assembled into a two-term complex
(`twoTermFunctor`). -/
def cubeToComplex (C : PreadCat) : (m : ℕ) →
    CubeData C.carrier m ⥤ IteratedComplex twoTermShape C m
  | 0 =>
    { obj := fun D => D.obj Fin.elim0
      map := fun f => f.app Fin.elim0
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  | m + 1 =>
    CubeData.split C.carrier m ⋙ (cubeToComplex C m).mapArrow ⋙
      twoTermFunctor (IteratedComplex twoTermShape C m)

/-! ## The cube complex of a U-brane diagram -/

section KLRWCube

variable {n : ℕ} {V : Type} [DecidableEq V] [Fintype V] {k : ℕ}
variable {S : Type} [CommRing S] (u ℏ : S) (Γ : SimpleDigraph V)

/-- The KLRW category of `k` black strands labelled by `labels` and the red strands of `disk`,
as a `PreadCat`. The cubes of all U-brane diagrams on `disk` with these labels live here. -/
def klrwPreadCat (disk : @MarkedDisk V n) (labels : Fin k → V) : PreadCat where
  carrier := KLRWObject.WithRing u ℏ (KLRWStructure.ofDisk Γ disk labels)

/-- The cube of a U-brane diagram: the KLRW object `vertexObject` at each vertex and the
morphism `edgeHom` along each edge. -/
def klrwCubeData {disk : @MarkedDisk V n} {labels : Fin k → V}
    (diag : UBraneDiagram disk labels) :
    CubeData (klrwPreadCat u ℏ Γ disk labels).carrier k where
  obj v := vertexObjectWithRing u ℏ Γ diag v
  edge := fun {v w} h => edgeHom u ℏ Γ diag v w h
  square := by sorry

/-- The iterated complex of a U-brane diagram, obtained from its cube by `cubeToComplex`. -/
def klrwComplex {disk : @MarkedDisk V n} {labels : Fin k → V}
    (diag : UBraneDiagram disk labels) :
    IteratedComplex twoTermShape (klrwPreadCat u ℏ Γ disk labels) k :=
  (cubeToComplex (klrwPreadCat u ℏ Γ disk labels) k).obj (klrwCubeData u ℏ Γ diag)

/-! ### The cubes of a peeling

All stages of a peeling have the same disk and labels, so their cubes are objects of the same
category `CubeData (klrwPreadCat u ℏ Γ disk labels).carrier k`. This is what makes it possible
to define morphisms between consecutive stages. -/

/-- The cube after peeling the first `j` branes. -/
def peelCube (disk : @MarkedDisk V n) (labels : Fin k → V) (p : PeelData n) (j : ℕ) :
    CubeData (klrwPreadCat u ℏ Γ disk labels).carrier k :=
  klrwCubeData u ℏ Γ (p.diagram disk labels j)

/-- The iterated complex after peeling the first `j` branes. -/
def peelComplex (disk : @MarkedDisk V n) (labels : Fin k → V)
    (p : PeelData n) (j : ℕ) :
    IteratedComplex twoTermShape (klrwPreadCat u ℏ Γ disk labels) k :=
  klrwComplex u ℏ Γ (p.diagram disk labels j)

/-- The map from stage `j` to stage `j + 1` of a peeling, as a morphism of cubes: `peelHom` at
each vertex. -/
def peelCubeHom (disk : @MarkedDisk V n) (labels : Fin k → V) (p : PeelData n)
    (j : ℕ) (hj : j < k) :
    peelCube u ℏ Γ disk labels p j ⟶ peelCube u ℏ Γ disk labels p (j + 1) where
  app v := peelHom u ℏ Γ disk labels p j hj v
  comm h := by sorry

/-- The map from stage `j` to stage `j + 1` of a peeling, as a morphism of iterated
complexes. -/
def peelComplexHom (disk : @MarkedDisk V n) (labels : Fin k → V)
    (p : PeelData n) (j : ℕ) (hj : j < k) :
    peelComplex u ℏ Γ disk labels p j ⟶ peelComplex u ℏ Γ disk labels p (j + 1) :=
  (cubeToComplex (klrwPreadCat u ℏ Γ disk labels) k).map (peelCubeHom u ℏ Γ disk labels p j hj)

/-- The complex shape of a chain `0 → 1 → ⋯ → k`: one differential from each `j` to
`j + 1`, and nothing out of `k`. -/
def chainShape (k : ℕ) : ComplexShape (Fin (k + 1)) where
  Rel i j := i.val + 1 = j.val
  next_eq := fun {i j j'} (h : i.val + 1 = j.val) (h' : i.val + 1 = j'.val) => Fin.ext (by omega)
  prev_eq := fun {i i' j} (h : i.val + 1 = j.val) (h' : i'.val + 1 = j.val) => Fin.ext (by omega)

/-- The peeling as a chain complex of iterated complexes,
`peelComplex 0 ⟶ peelComplex 1 ⟶ ⋯ ⟶ peelComplex k`, with the stage maps as differentials.
This is only a complex if any two consecutive stage maps compose to zero, which is the
hypothesis `hd`. -/
def peelChainComplex (disk : @MarkedDisk V n) (labels : Fin k → V) (p : PeelData n)
    (hd : ∀ (j : ℕ) (hj : j + 1 < k),
      peelComplexHom u ℏ Γ disk labels p j (by omega) ≫
        peelComplexHom u ℏ Γ disk labels p (j + 1) hj = 0) :
    HomologicalComplex (IteratedComplex twoTermShape (klrwPreadCat u ℏ Γ disk labels) k)
      (chainShape k) where
  X j := peelComplex u ℏ Γ disk labels p j.val
  d i j :=
    if h : i.val + 1 = j.val then
      peelComplexHom u ℏ Γ disk labels p i.val (by omega) ≫
        eqToHom (congrArg (peelComplex u ℏ Γ disk labels p) h)
    else 0
  shape i j hij := dif_neg (c := i.val + 1 = j.val) hij
  d_comp_d' := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ ⟨l, hl⟩ (hij : i + 1 = j) (hjl : j + 1 = l)
    subst hij hjl
    simp only [Fin.val_mk, dif_pos, eqToHom_refl, Category.comp_id]
    exact hd i (by omega)

end KLRWCube
end KLRW
