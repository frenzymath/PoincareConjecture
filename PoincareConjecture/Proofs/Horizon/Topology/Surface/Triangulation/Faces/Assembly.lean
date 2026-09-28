import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Incidence
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u v w

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem nonempty_finiteSmoothTriangulation_of_coordinate_triangle_cover
    {F : Type v} {E : Type w} [Finite F] [Finite E]
    (face : F → SmoothFace M) (edge : E → SmoothEdge M)
    (face_edge : F → Fin 3 → E)
    (hboundary : ∀ f k, (face f).boundary k = edge (face_edge f k))
    (hused : ∀ i, ∃ f k, face_edge f k = i)
    (hinj : ∀ i, InjOn (edge i).map (Icc (0 : ℝ) 1))
    (hmeet : ∀ i j, i ≠ j →
      (edge i).map '' Icc (0 : ℝ) 1 ∩ (edge j).map '' Icc (0 : ℝ) 1 ⊆
        {(edge i).map 0, (edge i).map 1})
    (coordinates : F → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (basis : F → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsource : ∀ f, convexHull ℝ (range (basis f)) ⊆ (coordinates f).source)
    (hcarrier : ∀ f, (face f).carrier = coordinates f '' convexHull ℝ (range (basis f)))
    (hinter : ∀ f g, f ≠ g →
      (face f).carrier ∩ (face g).carrier ⊆ frontier (face f).carrier)
    (hcover : (⋃ f, (face f).carrier) = univ)
    (vertices : Finset M)
    (hintersection : ∀ f g, f ≠ g →
      (∃ i : E, (face f).carrier ∩ (face g).carrier = (edge i).map '' Icc (0 : ℝ) 1) ∨
      ∃ p ∈ vertices, (face f).carrier ∩ (face g).carrier ⊆ {p}) :
    Nonempty (FiniteSmoothTriangulation (M := M)) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fintype E := Fintype.ofFinite E
  let fidx := Fintype.equivFin F
  let eidx := Fintype.equivFin E
  let vidx := Fintype.equivFin vertices
  choose left right hdistinct hincident using fun i =>
    exists_exactly_two_faces_of_coordinate_triangle_cover face edge face_edge
      hboundary hused hinj hmeet coordinates basis hsource hcarrier hinter hcover i
  refine ⟨{
    faces := Fin (Fintype.card F)
    edges := Fin (Fintype.card E)
    vertices := Fin (Fintype.card vertices)
    face := fun f => face (fidx.symm f)
    edge := fun e => edge (eidx.symm e)
    vertex := fun p => (vidx.symm p : M)
    face_edge := fun f k => eidx (face_edge (fidx.symm f) k)
    edge_face := fun e j =>
      if j = 0 then fidx (left (eidx.symm e)) else fidx (right (eidx.symm e))
    face_edge_map := ?_
    edge_face_boundary := ?_
    edge_faces_distinct := ?_
    edge_face_exact := ?_
    face_cover := ?_
    face_intersection := ?_ }⟩
  · intro f k
    simpa only [Equiv.symm_apply_apply] using hboundary (fidx.symm f) k
  · intro e j
    fin_cases j
    · obtain ⟨k, hk⟩ := (hincident (eidx.symm e) (left (eidx.symm e))).mpr (Or.inl rfl)
      refine ⟨k, ?_⟩
      simpa using congrArg eidx hk
    · obtain ⟨k, hk⟩ := (hincident (eidx.symm e) (right (eidx.symm e))).mpr (Or.inr rfl)
      refine ⟨k, ?_⟩
      simpa using congrArg eidx hk
  · intro e h
    apply hdistinct (eidx.symm e)
    exact fidx.injective h
  · intro e f k hk
    have hk' : face_edge (fidx.symm f) k = eidx.symm e := by
      apply eidx.injective
      simpa only [Equiv.apply_symm_apply] using hk
    rcases (hincident (eidx.symm e) (fidx.symm f)).mp ⟨k, hk'⟩ with hf | hf
    · left
      simpa only [ite_true, Equiv.apply_symm_apply] using congrArg fidx hf
    · right
      simpa only [Fin.isValue, one_ne_zero, ite_false, Equiv.apply_symm_apply] using
        congrArg fidx hf
  · apply subset_antisymm (subset_univ _)
    intro p hp
    obtain ⟨f, hf⟩ := mem_iUnion.mp (hcover.symm ▸ hp)
    exact mem_iUnion.mpr ⟨fidx f, by simpa only [Equiv.symm_apply_apply] using hf⟩
  · intro f g hfg
    have hfg' : fidx.symm f ≠ fidx.symm g := fun h => hfg (fidx.symm.injective h)
    rcases hintersection (fidx.symm f) (fidx.symm g) hfg' with ⟨e, he⟩ | ⟨p, hp, h⟩
    · left
      exact ⟨eidx e, by simpa only [Equiv.symm_apply_apply] using he⟩
    · right
      exact ⟨vidx ⟨p, hp⟩, by simpa only [Equiv.symm_apply_apply] using h⟩

theorem nonempty_finiteSmoothTriangulationWithCoordinates_of_coordinate_triangle_cover
    {F : Type v} {E : Type w} [Finite F] [Finite E]
    (face : F → SmoothFace M) (edge : E → SmoothEdge M)
    (face_edge : F → Fin 3 → E)
    (hboundary : ∀ f k, (face f).boundary k = edge (face_edge f k))
    (hused : ∀ i, ∃ f k, face_edge f k = i)
    (hinj : ∀ i, InjOn (edge i).map (Icc (0 : ℝ) 1))
    (hmeet : ∀ i j, i ≠ j →
      (edge i).map '' Icc (0 : ℝ) 1 ∩ (edge j).map '' Icc (0 : ℝ) 1 ⊆
        {(edge i).map 0, (edge i).map 1})
    (coordinates : F → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (basis : F → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hcoordinates : ∀ f, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (coordinates f)
      (coordinates f).source)
    (hcoordinates_symm : ∀ f, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (coordinates f).symm
      (coordinates f).target)
    (hsource : ∀ f, convexHull ℝ (range (basis f)) ⊆ (coordinates f).source)
    (hcarrier : ∀ f, (face f).carrier =
      coordinates f '' convexHull ℝ (range (basis f)))
    (hside : ∀ f k, ((face f).boundary k).map '' Icc (0 : ℝ) 1 =
      coordinates f '' affineSegment ℝ (basis f (k.succAbove 0))
        (basis f (k.succAbove 1)))
    (hinter : ∀ f g, f ≠ g →
      (face f).carrier ∩ (face g).carrier ⊆ frontier (face f).carrier)
    (hcover : (⋃ f, (face f).carrier) = univ)
    (vertices : Finset M)
    (hintersection : ∀ f g, f ≠ g →
      (∃ i : E, (face f).carrier ∩ (face g).carrier =
        (edge i).map '' Icc (0 : ℝ) 1) ∨
      ∃ p ∈ vertices, (face f).carrier ∩ (face g).carrier ⊆ {p}) :
    Nonempty (FiniteSmoothTriangulationWithCoordinates (M := M)) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fintype E := Fintype.ofFinite E
  let fidx := Fintype.equivFin F
  let eidx := Fintype.equivFin E
  let vidx := Fintype.equivFin vertices
  choose left right hdistinct hincident using fun i =>
    exists_exactly_two_faces_of_coordinate_triangle_cover face edge face_edge
      hboundary hused hinj hmeet coordinates basis hsource hcarrier hinter hcover i
  let T : FiniteSmoothTriangulation (M := M) := {
    faces := Fin (Fintype.card F)
    edges := Fin (Fintype.card E)
    vertices := Fin (Fintype.card vertices)
    face := fun f => face (fidx.symm f)
    edge := fun e => edge (eidx.symm e)
    vertex := fun p => (vidx.symm p : M)
    face_edge := fun f k => eidx (face_edge (fidx.symm f) k)
    edge_face := fun e j =>
      if j = 0 then fidx (left (eidx.symm e)) else fidx (right (eidx.symm e))
    face_edge_map := by
      intro f k
      simpa only [Equiv.symm_apply_apply] using hboundary (fidx.symm f) k
    edge_face_boundary := by
      intro e j
      fin_cases j
      · obtain ⟨k, hk⟩ := (hincident (eidx.symm e) (left (eidx.symm e))).mpr
          (Or.inl rfl)
        refine ⟨k, ?_⟩
        simpa using congrArg eidx hk
      · obtain ⟨k, hk⟩ := (hincident (eidx.symm e) (right (eidx.symm e))).mpr
          (Or.inr rfl)
        refine ⟨k, ?_⟩
        simpa using congrArg eidx hk
    edge_faces_distinct := by
      intro e h
      apply hdistinct (eidx.symm e)
      exact fidx.injective h
    edge_face_exact := by
      intro e f k hk
      have hk' : face_edge (fidx.symm f) k = eidx.symm e := by
        apply eidx.injective
        simpa only [Equiv.apply_symm_apply] using hk
      rcases (hincident (eidx.symm e) (fidx.symm f)).mp ⟨k, hk'⟩ with hf | hf
      · left
        simpa only [ite_true, Equiv.apply_symm_apply] using congrArg fidx hf
      · right
        simpa only [Fin.isValue, one_ne_zero, ite_false, Equiv.apply_symm_apply] using
          congrArg fidx hf
    face_cover := by
      apply subset_antisymm (subset_univ _)
      intro p hp
      obtain ⟨f, hf⟩ := mem_iUnion.mp (hcover.symm ▸ hp)
      exact mem_iUnion.mpr ⟨fidx f, by simpa only [Equiv.symm_apply_apply] using hf⟩
    face_intersection := by
      intro f g hfg
      have hfg' : fidx.symm f ≠ fidx.symm g :=
        fun h => hfg (fidx.symm.injective h)
      rcases hintersection (fidx.symm f) (fidx.symm g) hfg' with ⟨e, he⟩ | ⟨p, hp, h⟩
      · left
        exact ⟨eidx e, by simpa only [Equiv.symm_apply_apply] using he⟩
      · right
        exact ⟨vidx ⟨p, hp⟩, by simpa only [Equiv.symm_apply_apply] using h⟩ }
  refine ⟨{
    triangulation := T
    coordinates := fun f => coordinates (fidx.symm f)
    basis := fun f => basis (fidx.symm f)
    coordinates_smooth := fun f => hcoordinates (fidx.symm f)
    coordinates_symm_smooth := fun f => hcoordinates_symm (fidx.symm f)
    basis_subset_source := fun f => hsource (fidx.symm f)
    carrier_eq_coordinates := fun f => hcarrier (fidx.symm f)
    boundary_side_image := fun f k => hside (fidx.symm f) k }⟩

end PoincareConjecture.Topology.Surface
