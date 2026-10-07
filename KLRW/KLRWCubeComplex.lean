module
public import Mathlib
public import KLRW.KLRWAlgebra
public import KLRW.KLRWCategory
public import KLRW.U-Branes
@[expose] public section

namespace KLRW
open CategoryTheory Limits FreeAlgebra

section iteratedComplex

/-- PreadCat is a bundled category that carries both Category and Preadditive. -/
structure PreadCat where
  Carrier : Type
  [instCategory : Category Carrier]
  [instPreadditive : Preadditive Carrier]

attribute [instance] PreadCat.instCategory PreadCat.instPreadditive


variable {V : Type} [inst : DecidableEq V] [inst2 : Fintype V]
variable (R : Type) [inst3 : CommRing R]
variable (n : ℕ) 
variable (Γ : SimpleDigraph V)

/-- This is an iterated homological complex. -/
def iteratedPreadCat {A : Type} (shape : ComplexShape A) (C : PreadCat) : ℕ → PreadCat
  | 0 => C
  | n + 1 =>
      let prev := iteratedPreadCat shape C n
      { Carrier := HomologicalComplex prev.Carrier shape}

/-- Type of an n-dimensional iterated complex. -/
abbrev IteratedComplex {A : Type} (shape : ComplexShape A) (C : PreadCat) (d : ℕ) : Type :=
  (iteratedPreadCat shape C d).Carrier

abbrev IteratedComplex.unfold {A : Type} {shape : ComplexShape A} {C : PreadCat} {d : ℕ}
    (X : IteratedComplex shape C (d + 1)) :
    HomologicalComplex (IteratedComplex shape C d) shape :=
  X

/- This is to feed the KLRWObject.WithRing type to the PreadCat. -/
noncomputable def KLRWPreadCat {disk : @MarkedDisk V n} {k : ℕ} (R : Type) [CommRing R]
    (Γ : SimpleDigraph V) (diag : UBraneDiagram disk k) : PreadCat where
  Carrier := KLRWObject.WithRing R (UBraneKLRWStruct Γ diag)

end iteratedComplex

abbrev oneSimplex : SimplexCategory :=
  SimplexCategory.mk 1

def oneSimplexShape : ComplexShape (Fin 2) where
  Rel i j := i = 0 ∧ j = 1
  next_eq := by
    intro i j k ⟨hij1, hij2⟩ ⟨hjk1, hjk2⟩
    simp only [Fin.ext_iff] at *
    omega
  prev_eq := by
    intro i j k ⟨hij1, hij2⟩ ⟨hki1, hki2⟩
    simp only [Fin.ext_iff] at *
    omega

@[simp] lemma oneSimplexShape_rel (i j : Fin 2) :
    oneSimplexShape.Rel i j ↔ i = 0 ∧ j = 1 := Iff.rfl


/- CubeData holds all the information in a "subcube." If we let K be the KLRW category, CubData has the vertices and 
   associated KLRWObjects in that cube, the edges and associated KLRWmorphisms in that cube, and proofs that the 
   edges/morphisms commute. -/

structure CubeData (K : Type*) [Category K] (m : ℕ) where
  obj : Vertex m → K
  edge : ∀ {v w : Vertex m}, IsEdge v w → (obj v ⟶ obj w)
  square : ∀ {v w₁ w₂ u : Vertex m}
    (h₁ : IsEdge v w₁) (h₂ : IsEdge w₁ u) (h₃ : IsEdge v w₂) (h₄ : IsEdge w₂ u),
    edge h₁ ≫ edge h₂ = edge h₃ ≫ edge h₄
 


namespace CubeData
 
variable {K : Type*} [Category K] {m : ℕ}
 
/- Hom represents a morphism between two CubeDatas. It needs maps between each object in 
   CubeData, along with a proof of commutativity. -/
@[ext] 
structure Hom (D D' : CubeData K m) where
  app : ∀ v, D.obj v ⟶ D'.obj v
  comm : ∀ {v w : Vertex m} (h : IsEdge v w), D.edge h ≫ app w = app v ≫ D'.edge h 

/- Identity morphism from any CubeData to itself. -/
def Hom.id (D : CubeData K m) : Hom D D where
  app _ := 𝟙 _
  comm _ := by simp

/- Proof composition of morphsims between CubeData works as expected. -/
def Hom.comp {D D' D'' : CubeData K m} (f : Hom D D') (g : Hom D' D'') : Hom D D'' where
  app v := f.app v ≫ g.app v
  comm h := by
    rw [← Category.assoc, f.comm h, Category.assoc, g.comm h, ← Category.assoc]
 
/- Proves CubeData K m is a category. -/
instance category : Category (CubeData K m) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext (funext fun _ => Category.id_comp _)
  comp_id _ := Hom.ext (funext fun _ => Category.comp_id _)
  assoc _ _ _ := Hom.ext (funext fun _ => Category.assoc _ _ _)
 

/- Two morphisms are equivalent if their app field is equivalent. -/
@[ext]
lemma hom_ext {D D' : CubeData K m} {f g : D ⟶ D'} (h : ∀ v, f.app v = g.app v) : f = g :=
  Hom.ext (funext h)
 
/- Split CubeData K (m + 1) into two CubeData K m. e.g. for D which is a CubeData K 3, looking at the vertices, the idea is 
   face D 0 has the information about 000, 001, 010, 011 and face D 1 has information about 100, 101, 110, 111. Also splits 
   edges and square so only the ones contained completely in each CubeData m is in that respective CubeData m. -/

def face (D : CubeData K (m + 1)) (b : Fin 2) : CubeData K m where
  obj v := D.obj (vcons b v)
  edge h := D.edge (h.cons b)
  square h₁ h₂ h₃ h₄ := D.square (h₁.cons b) (h₂.cons b) (h₃.cons b) (h₄.cons b)
 
/- Returns a morphsim between the two split-off faces of D, made using the morphsims in D that
   didn't belong completely to either face. -/
def dir0 (D : CubeData K (m + 1)) : D.face 0 ⟶ D.face 1 where
  app v := D.edge (IsEdge.dir0 v)
  comm h := D.square (h.cons 0) (IsEdge.dir0 _) (IsEdge.dir0 _) (h.cons 1)
 
/- Uses a morphism between D and D' to get a morphsim between the faces of D and D'. -/
def Hom.face {D D' : CubeData K (m + 1)} (f : D ⟶ D') (b : Fin 2) :
    D.face b ⟶ D'.face b where
  app v := f.app (vcons b v)
  comm h := f.comm (h.cons b)

/- Split CubeData K (m + 1) into Arrow (CubeData K m), which holds two CubeData K m along with a morphism between them. This   
   will use face, and is for recusion later on. -/
variable (K) in
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

/- Helper to make morphisms for twoTerm. -/
def twoTermD {X₀ X₁ : D} (φ : X₀ ⟶ X₁) : (i j : Fin 2) → (![X₀, X₁] i ⟶ ![X₀, X₁] j)
  | 0, 1 => φ
  | _, _ => 0

/- Take a morphism (and implicitly from that morphism, take its start and end objects) to make a homological complex. -/
def twoTerm {X₀ X₁ : D} (φ : X₀ ⟶ X₁) : HomologicalComplex D oneSimplexShape where
  X := ![X₀, X₁]
  d := twoTermD φ
  shape i j hij := by fin_cases i <;> fin_cases j <;> first | rfl | simp at hij
  d_comp_d' := by
    rintro i j k ⟨-, rfl⟩ ⟨h, -⟩
    simp at h

/- Helper to make morphisms for twoTermHom. -/
def twoTermHomF {X₀ X₁ Y₀ Y₁ : D} (a : X₀ ⟶ Y₀) (b : X₁ ⟶ Y₁) :
    (i : Fin 2) → (![X₀, X₁] i ⟶ ![Y₀, Y₁] i)
  | 0 => a
  | 1 => b


/- Implicitly have homological complexs twoTerm φ (which is X₀ → X₁) and twoTerm ψ which is (Y₀ → Y₁). Take in two morphisms 
   connecting X₀ to Y₀ and X₁ to Y₁, along with a proof that the square commutes (which is what implicitly gives us φ and ψ, 
   and the twoTerm complexes) and use that to form a morphism between X₀ → X₁ and Y₀ → Y₁. -/
def twoTermHom {X₀ X₁ Y₀ Y₁ : D} {φ : X₀ ⟶ X₁} {ψ : Y₀ ⟶ Y₁}
    (a : X₀ ⟶ Y₀) (b : X₁ ⟶ Y₁) (w : a ≫ ψ = φ ≫ b) : twoTerm φ ⟶ twoTerm ψ where
  f := twoTermHomF a b
  comm' := by
    rintro i j ⟨rfl, rfl⟩
    exact w


/- Take in an Arrow of any category D (Arrow D contains a morphism between two objects in D, its starting object, and its 
   target object) and returns a 2-term homological complex. E.g. If Arrow D contains obj₀ -- map₀ --> obj₁, then 
   twoTermFunctor makes it officially a HomologicalComplex with objects obj₀ and obj₁, and the map map₀. (Arrow.w sq is a 
   proof of commutativity.) -/

variable (D) in
def twoTermFunctor : Arrow D ⥤ HomologicalComplex D oneSimplexShape where
  obj φ := twoTerm φ.hom
  map sq := twoTermHom sq.left sq.right (Arrow.w sq)
  map_id _ := by ext i; fin_cases i <;> rfl
  map_comp _ _ := by ext i; fin_cases i <;> rfl

end TwoTerm



/- A functor from CubeData m to IteratedComplex with depth m. It does this by recursion: first split the CubeData m+1 into 2 
   CubeData m plus a morphism between them, then apply cubeToComplex to all three of them (iterative step) and then glue all
   three back together into a homological complex using twoTermFunctor. -/

def cubeToComplex (C : PreadCat) : (m : ℕ) →
    CubeData C.Carrier m ⥤ IteratedComplex oneSimplexShape C m
  | 0 =>
    { obj := fun D => D.obj Fin.elim0
      map := fun f => f.app Fin.elim0
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  | m + 1 =>
    CubeData.split C.Carrier m ⋙ (cubeToComplex C m).mapArrow ⋙
      twoTermFunctor (IteratedComplex oneSimplexShape C m)

/- Make a CubeData that holds all the verticies and morphisms and proofs needed to build an iterated chain complex, and holds
   all the information in the right levels of the cube. -/
noncomputable def klrwCubeData (n : ℕ) {V : Type} [DecidableEq V] [Fintype V] {disk : @MarkedDisk V n} {k : ℕ}
    (R : Type) [CommRing R] (Γ : SimpleDigraph V) (diag : UBraneDiagram disk k) :
    CubeData (KLRWPreadCat n R Γ diag).Carrier k where
  obj v := vertexObject.WithRing R Γ diag v
  edge := fun {v w} h => edgeHom R Γ diag v w h
  square := by sorry

/- Final function to make the whole cube. Uses cubeToComplex to translates klrwCubeData to an iterated complex. -/
noncomputable def generatedCube (n : ℕ) {V : Type} [DecidableEq V] [Fintype V]
    {disk : @MarkedDisk V n} {k : ℕ} (R : Type) [CommRing R]
    (Γ : SimpleDigraph V) (diag : UBraneDiagram disk k) :
    IteratedComplex oneSimplexShape (KLRWPreadCat n R Γ diag) k :=
  (cubeToComplex (KLRWPreadCat n R Γ diag) k).obj (klrwCubeData n R Γ diag)

end KLRW
