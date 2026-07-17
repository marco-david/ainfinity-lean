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
-- Γ represents the directed graph with labeled verticies
-- dᵢ (a) tells you the number of black strands labeled a, given a is in Fin n
-- red_Strands (a) tells you the number of red strands labeled a, given a is in Fin n

structure KLRWStructure (V : Type*) where
  Γ : SimpleDigraph (V)
  black_strands : V → Nat
  red_strands : V → Nat

-- holds information for each strand (each strand has a label and a color)
structure StrandData (V : Type*) where
  label : V
  color : StrandColor
  deriving DecidableEq


def num_black [DecidableEq V] (v : Vector (StrandData V) m) (k : V) : Nat :=
  (v.toList.filter (fun p => p.label == k && p.color == StrandColor.black)).length

def num_red [DecidableEq V] (v : Vector (StrandData V) m) (k : V) : Nat :=
  (v.toList.filter (fun p => p.label == k && p.color == StrandColor.red)).length

abbrev total_strands [DecidableEq V] [Fintype V] (parameters : KLRWStructure V) :=
  ∑ v : V, (parameters.black_strands v + parameters.red_strands v)


-- strand_seq is a vector where each slot contains the strand's label (vertex number associated with it) and color
-- num_black_right makes sure the number of black strands for each label in strand_seq matches that of dᵢ in blueprint
-- num_red_right makes sure the number of red strands for each label in strand_seq matches that of red_strands in blueprint


structure KLRWObject {V : Type*} [DecidableEq V] [Fintype V] (parameters : KLRWStructure V) where
  strand_seq : Vector (StrandData V) (total_strands parameters)
  corr_num_black : ∀ (i : V), parameters.black_strands i = num_black strand_seq i
  corr_num_red   : ∀ (i : V), parameters.red_strands i   = num_red strand_seq i



-- Examples of the previous structures

def exGraph : SimpleDigraph (Fin 3) where
  Adj i j := i.val < j.val
  loopless := by
    intro i h
    exact Nat.lt_irrefl i.val h

def exReq : KLRWStructure (Fin 3) where
  Γ := exGraph
  black_strands := ![2, 1, 0]
  red_strands := ![1, 0, 1]


def exObj : KLRWObject exReq where
  strand_seq := ⟨#[⟨0, .black⟩ , ⟨0, .black⟩, ⟨0, .red⟩,
                 ⟨1, .black⟩, ⟨2, .red⟩], by decide⟩
  corr_num_black := by
    intro i
    fin_cases i <;> decide
  corr_num_red := by
    intro i
    fin_cases i <;> decide















-- Basis for defining homomorphisms between KLRW objects

-- strandGenerators are basic elements like dot 4, cross 3, etc. that describe what what happens to
-- the ith strand and is meant to describes crosses and dots in a diagram in order from bottom up

inductive StrandGenerator [DecidableEq V] [Fintype V] (parameters : KLRWStructure V) where
  | dot   : KLRWObject parameters → Fin (total_strands parameters) → StrandGenerator parameters
  | cross : KLRWObject parameters → Fin (total_strands parameters - 1) → StrandGenerator parameters
  | id : KLRWObject parameters → StrandGenerator parameters


-- function that gives you the KLRWObject after before a strand generator (the domain of the morphism)

def gen_domain [DecidableEq V] [Fintype V] {parameters : KLRWStructure V}
    (gen : StrandGenerator parameters) : KLRWObject parameters :=
  match gen with
  | .dot M _   => M
  | .cross M _ => M
  | .id M      => M


-- lemma that shows using toList and List.ofFn to turn a vector into a list results in the same list

lemma toList_eq_ofFn {α : Type _} {n : Nat} (v : Vector α n) : v.toList = List.ofFn v.get := by
  apply List.ext_get
  · simp [List.length_ofFn]
  · intro i hi₁ hi₂
    rw [List.get_ofFn]
    rfl


def codomain_after_cross [DecidableEq V] [Fintype V] {parameters : KLRWStructure V}
    (M : KLRWObject parameters) (i : Fin (total_strands parameters - 1)) :
    KLRWObject parameters where
  strand_seq := Vector.ofFn (fun k =>
    M.strand_seq.get (Equiv.swap ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩ k))
  corr_num_black := by
    intro v
    rw [M.corr_num_black v]
    simp only [num_black, Vector.toList_ofFn]
    have hperm : (List.ofFn (fun k => M.strand_seq.get (Equiv.swap ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩ k))).Perm
        M.strand_seq.toList := by
      have h := Equiv.Perm.ofFn_comp_perm
        (Equiv.swap (α := Fin (total_strands parameters)) ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩)
        M.strand_seq.get
      convert h using 1
      rw [toList_eq_ofFn]
    exact (hperm.filter _).length_eq.symm
  corr_num_red := by
    intro v
    rw [M.corr_num_red v]
    simp only [num_red, Vector.toList_ofFn]
    have hperm : (List.ofFn (fun k => M.strand_seq.get (Equiv.swap ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩ k))).Perm
        M.strand_seq.toList := by
      have h := Equiv.Perm.ofFn_comp_perm
        (Equiv.swap (α := Fin (total_strands parameters)) ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩)
        M.strand_seq.get
      convert h using 1
      rw [toList_eq_ofFn]
    exact (hperm.filter _).length_eq.symm


-- function that gives you the KLRWObject after applying a strand generator

def gen_codomain [DecidableEq V] [Fintype V] {parameters : KLRWStructure V} (gen : StrandGenerator parameters)
    : KLRWObject parameters :=
  match gen with
  | .dot M _   => M
  | .cross M i => codomain_after_cross M i
  | .id M      => M




-- lifts the StrandGenerator to a Free algebra over R[x, y]

abbrev KLRWFreeAlg [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (parameters : KLRWStructure V) :=
  FreeAlgebra (MvPolynomial (Fin 2) R) (StrandGenerator parameters)



-- structural/innate/implicit KLRW algebra equality relations

inductive KLRWImplicitConRel [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]
    (parameters : KLRWStructure V) :
    KLRWFreeAlg R parameters → KLRWFreeAlg R parameters → Prop where

  -- dot on red strand → zero
  | dot_on_red : ∀ M i,
      (M.strand_seq.get ⟨i, by omega⟩).color = StrandColor.red →
      KLRWImplicitConRel R parameters
        (FreeAlgebra.ι _ (StrandGenerator.dot M i)) 0

  -- crossing with 2 red strands → zero
  | cross_two_red : ∀ M i,
      (M.strand_seq.get ⟨i, by omega⟩).color = StrandColor.red →
      (M.strand_seq.get ⟨i+1, by omega⟩).color = StrandColor.red →
      KLRWImplicitConRel R parameters
        (FreeAlgebra.ι _ (StrandGenerator.cross M i)) 0

  -- bad composition (domain/codomain mismatch) → zero
  | bad_comp : ∀ f g,
      gen_codomain f ≠ gen_domain g →
      KLRWImplicitConRel R parameters
        (FreeAlgebra.ι _ g * FreeAlgebra.ι _ f) 0


  -- id is the left and right identity

  | id_left : ∀ M g,
    gen_domain g = M →
    KLRWImplicitConRel R parameters
      (FreeAlgebra.ι _ (StrandGenerator.id M) * FreeAlgebra.ι _ g)
      (FreeAlgebra.ι _ g)

  | id_right : ∀ M g,
    gen_codomain g = M →
    KLRWImplicitConRel R parameters
      (FreeAlgebra.ι _ g * FreeAlgebra.ι _ (StrandGenerator.id M))
      (FreeAlgebra.ι _ g)



  -- when commutative: not official relation but automatic from equality up to isotopy

  | crs_crs_comm : ∀ M i j,
      dist i.val j.val > 1 →
      KLRWImplicitConRel R parameters
        (FreeAlgebra.ι _ (StrandGenerator.cross (codomain_after_cross M i) j) *
         FreeAlgebra.ι _ (StrandGenerator.cross M i))
        (FreeAlgebra.ι _ (StrandGenerator.cross (codomain_after_cross M i) i) *
        FreeAlgebra.ι _ (StrandGenerator.cross M j))

  | dot_dot_comm : ∀ M i j,
      KLRWImplicitConRel R parameters
        (FreeAlgebra.ι _ (StrandGenerator.dot M j) *
         FreeAlgebra.ι _ (StrandGenerator.dot M i))
        (FreeAlgebra.ι _ (StrandGenerator.dot M i) *
         FreeAlgebra.ι _ (StrandGenerator.dot M j))

  -- PLACEHOLDER, need to write still
  | crs_dot_comm : ∀ M i j,
      KLRWImplicitConRel R parameters
        (FreeAlgebra.ι _ (StrandGenerator.dot M j) *
         FreeAlgebra.ι _ (StrandGenerator.dot M i))
        (FreeAlgebra.ι _ (StrandGenerator.dot M i) *
         FreeAlgebra.ι _ (StrandGenerator.dot M j))



noncomputable abbrev uVar (R : Type*) [CommRing R] : MvPolynomial (Fin 2) R := MvPolynomial.X 0
noncomputable abbrev hVar (R : Type*) [CommRing R] : MvPolynomial (Fin 2) R := MvPolynomial.X 1


-- explicit KLRW algebra equality relations

inductive KLRWExplicitConRel [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]
    (parameters : KLRWStructure V) :
    KLRWFreeAlg R parameters → KLRWFreeAlg R parameters → Prop where

  -- (a) bigon: two black strands cross twice = 0
  | bigon : ∀ M i,
      (M.strand_seq.get ⟨i, by omega⟩).label =
        (M.strand_seq.get ⟨i+1, by omega⟩).label →
      (M.strand_seq.get ⟨i, by omega⟩).color = StrandColor.black →
      (M.strand_seq.get ⟨i+1, by omega⟩).color = StrandColor.black →
      KLRWExplicitConRel R parameters
        (FreeAlgebra.ι _ (StrandGenerator.cross M i) *
         FreeAlgebra.ι _ (StrandGenerator.cross M i)) 0

  -- (b) bigon for (j) → (i)
  | bigon_for_j_to_i : ∀ M i,
      parameters.Γ.Adj
        (M.strand_seq.get ⟨i, by omega⟩).label
        (M.strand_seq.get ⟨i+1, by omega⟩).label →
      (M.strand_seq.get ⟨i, by omega⟩).color = StrandColor.black →
      (M.strand_seq.get ⟨i+1, by omega⟩).color = StrandColor.black →
      KLRWExplicitConRel R parameters
        (FreeAlgebra.ι _ (StrandGenerator.cross M i) *
         FreeAlgebra.ι _ (StrandGenerator.cross M i))
        (algebraMap _ _ (uVar R) *
        (FreeAlgebra.ι _ (StrandGenerator.dot M ⟨i + 1, by omega⟩) -
         FreeAlgebra.ι _ (StrandGenerator.dot M ⟨i, by omega⟩)))

  -- (c)
  | bigon_with_red : ∀ M i,
      (M.strand_seq.get ⟨i, by omega⟩).label =
        (M.strand_seq.get ⟨i+1, by omega⟩).label →
      (M.strand_seq.get ⟨i, by omega⟩).color = StrandColor.red →
      (M.strand_seq.get ⟨i+1, by omega⟩).color = StrandColor.black →
      KLRWExplicitConRel R parameters
        (FreeAlgebra.ι _ (StrandGenerator.cross M i) *
         FreeAlgebra.ι _ (StrandGenerator.cross M i))
        (algebraMap _ _ (uVar R) *
        (FreeAlgebra.ι _ (StrandGenerator.dot M ⟨i + 1, by omega⟩)))

  -- (d)
  | braid_with_neighbor : ∀ M (i : Fin ((total_strands parameters - 2))),
      parameters.Γ.Adj
        (M.strand_seq.get ⟨i+1, by omega⟩).label
        (M.strand_seq.get ⟨i, by omega⟩).label →
      (M.strand_seq.get ⟨i, by omega⟩).label =
        (M.strand_seq.get ⟨i+2, by omega⟩).label →
      (M.strand_seq.get ⟨i, by omega⟩).color = StrandColor.black →
      (M.strand_seq.get ⟨i+1, by omega⟩).color = StrandColor.black →
      (M.strand_seq.get ⟨i+2, by omega⟩).color = StrandColor.black →
      KLRWExplicitConRel R parameters
        (FreeAlgebra.ι _ (StrandGenerator.cross M ⟨i, by omega⟩) *
         FreeAlgebra.ι _ (StrandGenerator.cross M ⟨i+1, by omega⟩) *
         FreeAlgebra.ι _ (StrandGenerator.cross M ⟨i, by omega⟩) -
         FreeAlgebra.ι _ (StrandGenerator.cross M ⟨i+1, by omega⟩) *
         FreeAlgebra.ι _ (StrandGenerator.cross M ⟨i, by omega⟩) *
         FreeAlgebra.ι _ (StrandGenerator.cross M ⟨i+1, by omega⟩))
        ((algebraMap _ _ (uVar R)) * (algebraMap _ _ (hVar R)) *
        (FreeAlgebra.ι _ (StrandGenerator.id M)))

  -- (e)
  | braid_with_red : ∀ M (i : Fin ((total_strands parameters - 2))),
      (M.strand_seq.get ⟨i+1, by omega⟩).label =
        (M.strand_seq.get ⟨i, by omega⟩).label →
      (M.strand_seq.get ⟨i, by omega⟩).label =
        (M.strand_seq.get ⟨i+2, by omega⟩).label →
      (M.strand_seq.get ⟨i, by omega⟩).color = StrandColor.black →
      (M.strand_seq.get ⟨i+1, by omega⟩).color = StrandColor.red →
      (M.strand_seq.get ⟨i+2, by omega⟩).color = StrandColor.black →
      KLRWExplicitConRel R parameters
        (FreeAlgebra.ι _ (StrandGenerator.cross M ⟨i, by omega⟩) *
         FreeAlgebra.ι _ (StrandGenerator.cross M ⟨i+1, by omega⟩) *
         FreeAlgebra.ι _ (StrandGenerator.cross M ⟨i, by omega⟩) -
         FreeAlgebra.ι _ (StrandGenerator.cross M ⟨i+1, by omega⟩) *
         FreeAlgebra.ι _ (StrandGenerator.cross M ⟨i, by omega⟩) *
         FreeAlgebra.ι _ (StrandGenerator.cross M ⟨i+1, by omega⟩))
        ((algebraMap _ _ (uVar R)) * (algebraMap _ _ (hVar R)) *
        (FreeAlgebra.ι _ (StrandGenerator.id M)))

  -- (f)
  | dot_pass_cross : ∀ M i,
      (M.strand_seq.get ⟨i, by omega⟩).label =
        (M.strand_seq.get ⟨i+1, by omega⟩).label →
      (M.strand_seq.get ⟨i, by omega⟩).color = StrandColor.black →
      (M.strand_seq.get ⟨i+1, by omega⟩).color = StrandColor.black →
      KLRWExplicitConRel R parameters
        (FreeAlgebra.ι _ (StrandGenerator.cross M i) *
         FreeAlgebra.ι _ (StrandGenerator.dot M ⟨i, by omega⟩) -
         FreeAlgebra.ι _ (StrandGenerator.dot M ⟨i, by omega⟩) *
         FreeAlgebra.ι _ (StrandGenerator.cross M i))
        (algebraMap _ _ (hVar R) *
        (FreeAlgebra.ι _ (StrandGenerator.id M)))

  -- (g)
  | dot_pass_cross_2 : ∀ M (i : Fin (total_strands parameters - 1)),
      (M.strand_seq.get ⟨i, by omega⟩).label =
        (M.strand_seq.get ⟨i+1, by omega⟩).label →
      (M.strand_seq.get ⟨i, by omega⟩).color = StrandColor.black →
      (M.strand_seq.get ⟨i+1, by omega⟩).color = StrandColor.black →
      KLRWExplicitConRel R parameters
        (FreeAlgebra.ι _ (StrandGenerator.dot M ⟨i, by omega⟩) *
         FreeAlgebra.ι _ (StrandGenerator.cross M i) -
         FreeAlgebra.ι _ (StrandGenerator.cross M i) *
         FreeAlgebra.ι _ (StrandGenerator.dot M ⟨i, by omega⟩))
        (algebraMap _ _ (hVar R) *
        (FreeAlgebra.ι _ (StrandGenerator.id M)))

-- returns the smallest ring congruence relation on the KLRW Free Algebra that contains all the relations (both implicit and explicit) we want

noncomputable def KLRWRel [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]
    (parameters : KLRWStructure V) : RingCon (KLRWFreeAlg R parameters) :=
  ringConGen  (fun x y =>
    KLRWImplicitConRel R parameters x y ∨
    KLRWExplicitConRel R parameters x y)




-- quotients out KLRWRel from KLRWFreeAlg to get KLRW Algebra

abbrev KLRWAlg [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (parameters : KLRWStructure V) :=
  (KLRWRel R parameters).Quotient


-- helper function to get the idempotent element e_X inside the quotient algebra (id_morph R X = e_X)
-- LATER ON TASK: try to make computable (last priority), see why its not

noncomputable def id_morph [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] {parameters : KLRWStructure V}
    (X : KLRWObject parameters) : KLRWAlg R parameters :=
  (KLRWRel R parameters).mk' (FreeAlgebra.ι (MvPolynomial (Fin 2) R) (StrandGenerator.id X))


-- uses helper function e to get the set of all equivalence classes of morphisms in KLRAlg that start
-- from X and map to Y (KLRW Hom X Y = e_X KLRWAlg e_Y)

noncomputable def KLRWHom [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] (parameters : KLRWStructure V)
    (X Y : KLRWObject parameters) : Submodule R (KLRWAlg R parameters) :=
  LinearMap.range ((LinearMap.mulLeft R (id_morph R X)).comp (LinearMap.mulRight R (id_morph R Y)))



open CategoryTheory


-- if f and g are equal by a rule in KLRWImplicit, then f and g are equal

lemma implicit_rel_eq_rel [DecidableEq V] [Fintype V] {R : Type*} [CommRing R] {parameters : KLRWStructure V}
    {f g : KLRWFreeAlg R parameters} (h : KLRWImplicitConRel R parameters f g) :
    KLRWRel R parameters f g :=
  RingConGen.Rel.of f g (Or.inl h)


-- if f and g are equal by a rule in KLRWExplicit, then f and g are equal

lemma explicit_rel_eq_rel  [DecidableEq V] [Fintype V] {R : Type*} [CommRing R] {parameters : KLRWStructure V}
    {f g : KLRWFreeAlg R parameters} (h : KLRWExplicitConRel R parameters f g) :
    KLRWRel R parameters f g :=
  RingConGen.Rel.of f g (Or.inr h)


-- if f and g are equal, then they are in the same equivalence class

lemma rel_eq_same_con_class [DecidableEq V] [Fintype V] {R : Type*} [CommRing R] {parameters : KLRWStructure V}
    {x y : KLRWFreeAlg R parameters} (h : KLRWRel R parameters x y) :
    (KLRWRel R parameters).mk' x = (KLRWRel R parameters).mk' y := by
  exact (KLRWRel R parameters).eq.mpr h


-- shows that the identity in KLRWAlg is idempotent (using id_left in KLRW Implicit relations for the KLRW free algebra's id generator)

lemma id_is_idem [DecidableEq V] [Fintype V] {R : Type*} [CommRing R] {parameters : KLRWStructure V}
    (M : KLRWObject parameters) :
    id_morph R M * id_morph R M = id_morph R M := by
  apply rel_eq_same_con_class
  apply implicit_rel_eq_rel
  exact KLRWImplicitConRel.id_left M (StrandGenerator.id M) rfl


-- shows the id * f = f for the identity in KLRWAlg

lemma id_mul_left [DecidableEq V] [Fintype V] {R : Type*} [CommRing R] {parameters : KLRWStructure V}
    {X Y : KLRWObject parameters} (f : KLRWAlg R parameters)
    (hf : f ∈ KLRWHom R parameters X Y) : id_morph R X * f = f := by
  obtain ⟨a, ha⟩ := hf
  dsimp [LinearMap.mulLeft, LinearMap.mulRight, LinearMap.comp] at ha
  rw [← ha, ← mul_assoc, id_is_idem]



-- shows the f * id = f for the identity in KLRWAlg

lemma id_mul_right [DecidableEq V] [Fintype V] {R : Type*} [CommRing R]
    {parameters : KLRWStructure V}
    {X Y : KLRWObject parameters} (f : KLRWAlg R parameters)
    (hf : f ∈ KLRWHom R parameters X Y) : f * id_morph R Y = f := by
  obtain ⟨a, ha⟩ := hf
  dsimp [LinearMap.mulLeft, LinearMap.mulRight, LinearMap.comp] at ha
  rw [← ha, ← mul_assoc, mul_assoc, id_is_idem]


-- shows connection between f ∈ KLRWHom X Y and e_X * f * e_Y = f

lemma mem_KLRWHom_iff [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] {parameters : KLRWStructure V}
    {X Y : KLRWObject parameters} (f : KLRWAlg R parameters) :
    f ∈ KLRWHom R parameters X Y ↔ id_morph R X * f * id_morph R Y = f := by
  constructor
  · -- forward direction: if f ∈ range, then e_X * f * e_Y = f
    intro h
    rcases h with ⟨a, rfl⟩
    dsimp at *
    simp [mul_assoc, id_is_idem]
    simp [← mul_assoc, id_is_idem]
  · -- backward direction: if e_X * f * e_Y = f, then f ∈ range
    intro h
    use f
    dsimp
    simp only [← mul_assoc]
    exact h


--

lemma KLRWHom_comp_mem [DecidableEq V] [Fintype V] {R : Type*} [CommRing R]
    {parameters : KLRWStructure V}
    {X Y Z : KLRWObject parameters} {f g : KLRWAlg R parameters}
    (hf : f ∈ KLRWHom R parameters X Y) (hg : g ∈ KLRWHom R parameters Y Z) :
    f * g ∈ KLRWHom R parameters X Z := by
  rw [mem_KLRWHom_iff, mul_assoc, mul_assoc, id_mul_right g hg]
  rw [← mul_assoc, id_mul_left f hf]


-- just adds R to KLRWObject so that user can specify what ring they are working in, syntatically
-- needed by lean when defining the category

structure KLRWObjectR {V : Type*} [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]
    (parameters : KLRWStructure V) where
  obj : KLRWObject parameters



-- prove KLRWObjectR R parameters is actually a category

noncomputable instance {R : Type*} [CommRing R] {V : Type*} [DecidableEq V] [Fintype V]
    {parameters : KLRWStructure V} : Category (KLRWObjectR R parameters) where

  Hom X Y := ↥(KLRWHom R parameters X.obj Y.obj)

  id X := ⟨id_morph R X.obj, by
    rw [mem_KLRWHom_iff]
    simp [id_is_idem]⟩

  comp f g := ⟨f.val * g.val, KLRWHom_comp_mem f.property g.property⟩

  id_comp f := by ext; exact id_mul_left f.val f.property

  comp_id f := by ext; exact id_mul_right f.val f.property

  assoc f g h := by ext; simp [mul_assoc]





 end KLRW
