import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Regions.RegionNesting

set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}

def polygonVertexTriangle (p : Polygon E n) (k : Fin n) : Set E :=
  convexHull ℝ {p k, p ((finRotate n).symm k), p (finRotate n k)}

def IsAdmissibleVertex (p : Polygon E n) (k : Fin n) : Prop :=
  polygonVertexTriangle p k ∩ p.boundary ℝ =
    segment ℝ (p k) (p ((finRotate n).symm k)) ∪ segment ℝ (p k) (p (finRotate n k))

end Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n m : ℕ}

theorem polygonIncidentEdges_subset_triangle_inter_boundary (p : Polygon E n) (k : Fin n) :
    segment ℝ (p k) (p ((finRotate n).symm k)) ∪ segment ℝ (p k) (p (finRotate n k)) ⊆
      polygonVertexTriangle p k ∩ p.boundary ℝ := by
  have hk : p k ∈ ({p k, p ((finRotate n).symm k), p (finRotate n k)} : Set E) := by simp
  have hpred : p ((finRotate n).symm k) ∈
      ({p k, p ((finRotate n).symm k), p (finRotate n k)} : Set E) := by simp
  have hsucc : p (finRotate n k) ∈
      ({p k, p ((finRotate n).symm k), p (finRotate n k)} : Set E) := by simp
  intro x hx
  rcases hx with hx | hx
  · refine ⟨segment_subset_convexHull hk hpred hx, ?_⟩
    apply polygon_edgeSet_subset_boundary p ((finRotate n).symm k)
    rw [polygon_edgeSet_eq_segment, Equiv.apply_symm_apply, segment_symm]
    exact hx
  · refine ⟨segment_subset_convexHull hk hsucc hx, ?_⟩
    apply polygon_edgeSet_subset_boundary p k
    rw [polygon_edgeSet_eq_segment]
    exact hx

theorem IsSimplePolygon.admissibleVertex_of_child [FiniteDimensional ℝ E]
    {p : Polygon E n} {q : Polygon E m} (hq : IsSimplePolygon q)
    (hdim : Module.finrank ℝ E = 2) (k : Fin m) (l : Fin n)
    (hk : q k = p l)
    (hpred : q ((finRotate m).symm k) = p ((finRotate n).symm l))
    (hsucc : q (finRotate m k) = p (finRotate n l))
    (hI : polygonInterior q ⊆ polygonInterior p)
    (hT : polygonVertexTriangle q k ⊆ closure (polygonInterior q))
    (had : IsAdmissibleVertex q k) :
    IsAdmissibleVertex p l ∧ polygonVertexTriangle p l ⊆ closure (polygonInterior p) := by
  have hTeq : polygonVertexTriangle q k = polygonVertexTriangle p l := by
    unfold polygonVertexTriangle
    rw [hk, hpred, hsucc]
  refine ⟨?_, ?_⟩
  · change polygonVertexTriangle p l ∩ p.boundary ℝ = _
    apply subset_antisymm _ (polygonIncidentEdges_subset_triangle_inter_boundary p l)
    rintro x ⟨hxT, hxB⟩
    have hxqT : x ∈ polygonVertexTriangle q k := hTeq.symm ▸ hxT
    have hxq := hT hxqT
    rw [hq.closure_polygonInterior hdim] at hxq
    rcases hxq with hxq | hxq
    · exact ((hI hxq).1 hxB).elim
    · have hxC : x ∈ polygonVertexTriangle q k ∩ q.boundary ℝ := ⟨hxqT, hxq⟩
      change polygonVertexTriangle q k ∩ q.boundary ℝ = _ at had
      rw [had] at hxC
      simpa only [hk, hpred, hsucc] using hxC
  · rw [← hTeq]
    exact hT.trans (closure_mono hI)

end Poincare.Manifold.Schoenflies.Plane
