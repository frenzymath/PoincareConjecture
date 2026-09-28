import PoincareConjecture.Proofs.M76.Mathlib.SimplicialGenerators
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false

open Set Geometry

namespace Polygon

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}

noncomputable def edgeVertices (P : Polygon E n) (i : Fin n) : Finset E := by
  classical
  exact {P i, P (finRotate n i)}

theorem edgeSet_eq_convexHull (P : Polygon E n) (i : Fin n) :
    P.edgeSet ℝ i = convexHull ℝ (P.edgeVertices i : Set E) := by
  simp only [edgeSet, edgeVertices, Finset.coe_pair, convexHull_pair,
    affineSegment_eq_segment]

def HasSimplicialEdges (P : Polygon E n) : Prop :=
  ∀ i j, P.edgeSet ℝ i ∩ P.edgeSet ℝ j ⊆
    convexHull ℝ ((P.edgeVertices i : Set E) ∩ P.edgeVertices j)

private theorem independent_edgeVertices (P : Polygon E n) (i : Fin n) :
    AffineIndependent ℝ ((↑) : P.edgeVertices i → E) := by
  classical
  change AffineIndependent ℝ ((↑) : ↥(P.edgeVertices i : Set E) → E)
  rw [show (P.edgeVertices i : Set E) = {P i, P (finRotate n i)} by
    simp only [edgeVertices, Finset.coe_pair]]
  by_cases h : P i = P (finRotate n i)
  · rw [h, Set.pair_eq_singleton]
    exact affineIndependent_of_subsingleton ℝ _
  · have h' := (affineIndependent_of_ne ℝ h).range
    rw [Matrix.range_cons_cons_empty] at h'
    exact h'

private theorem edge_generators_inter (P : Polygon E n) (hP : P.HasSimplicialEdges) :
    ∀ s ∈ range P.edgeVertices, ∀ t ∈ range P.edgeVertices,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ t) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  simpa only [← P.edgeSet_eq_convexHull] using hP i j

noncomputable def simplicialComplex (P : Polygon E n) (hP : P.HasSimplicialEdges) :
    SimplicialComplex ℝ E :=
  SimplicialComplex.ofGenerators (range P.edgeVertices)
    (by rintro _ ⟨i, rfl⟩; exact independent_edgeVertices P i)
    (edge_generators_inter P hP)

theorem mem_simplicialComplex_faces (P : Polygon E n) (hP : P.HasSimplicialEdges)
    (s : Finset E) :
    s ∈ (P.simplicialComplex hP).faces ↔ s.Nonempty ∧ ∃ i, s ⊆ P.edgeVertices i := by
  change (s.Nonempty ∧ ∃ t ∈ range P.edgeVertices, s ⊆ t) ↔ _
  constructor
  · rintro ⟨hs, _, ⟨i, rfl⟩, hsi⟩
    exact ⟨hs, i, hsi⟩
  · rintro ⟨hs, i, hsi⟩
    exact ⟨hs, _, mem_range_self i, hsi⟩

theorem edgeVertices_mem_faces (P : Polygon E n) (hP : P.HasSimplicialEdges)
    (i : Fin n) : P.edgeVertices i ∈ (P.simplicialComplex hP).faces := by
  classical
  exact (P.mem_simplicialComplex_faces hP _).mpr
    ⟨Finset.insert_nonempty _ _, i, Finset.Subset.refl _⟩

theorem finite_simplicialComplex_faces (P : Polygon E n) (hP : P.HasSimplicialEdges) :
    (P.simplicialComplex hP).faces.Finite :=
  SimplicialComplex.finite_ofGenerators_faces (finite_range _) _ _

theorem simplicialComplex_space (P : Polygon E n) (hP : P.HasSimplicialEdges) :
    (P.simplicialComplex hP).space = P.boundary ℝ := by
  rw [simplicialComplex, SimplicialComplex.space_ofGenerators, Polygon.boundary]
  rw [Set.biUnion_range]
  simp only [← P.edgeSet_eq_convexHull]

theorem simplicialComplex_vertices (P : Polygon E n) (hP : P.HasSimplicialEdges) :
    (P.simplicialComplex hP).vertices = range P := by
  ext x
  change ({x} : Finset E) ∈ (P.simplicialComplex hP).faces ↔ _
  rw [P.mem_simplicialComplex_faces]
  simp only [Finset.singleton_nonempty, true_and, Finset.singleton_subset_iff,
    edgeVertices, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl | rfl⟩
    · exact mem_range_self _
    · exact mem_range_self _
  · rintro ⟨i, rfl⟩
    exact ⟨i, Or.inl rfl⟩

end Polygon
