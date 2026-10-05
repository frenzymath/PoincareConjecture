import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.RadialSegmentGerms
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.LinkGraphIncidence
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.FaceLinkCofaceCount

/-!
# Actual graph degree at a half-segment endpoint

A finite geometric carrier that is locally one nondegenerate radial
segment has one link point at its endpoint. Thus its actual edge graph
has degree one there, regardless of the carrier away from that point.
This is the endpoint incidence step after Prime034, section 4.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

/-- A genuine half-segment germ determines the actual graph degree of
its marked endpoint. No global dimension or graph-purity input is used. -/
theorem ncard_neighborSet_eq_one_of_local_segment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzero : (0 : E) ∈ K.vertices) {u : E} (hu : u ≠ 0)
    (hlocal : ∀ᶠ x in 𝓝 (0 : E), x ∈ K.space ↔ x ∈ segment ℝ 0 u) :
    (K.vertexAbstractComplex.edgeGraph.neighborSet ⟨0, hzero⟩).ncard = 1 := by
  have hlocal' : ∀ᶠ x in 𝓝 (0 : E),
      x ∈ K.space ∩ {y | (0 : E →ₗ[ℝ] ℝ) y = 0} ↔
        x ∈ segment ℝ 0 u ∪ segment ℝ 0 u := by
    simpa using hlocal
  have hnorm : NormedSpace.normalize '' (K.link 0).space = {NormedSpace.normalize u} := by
    simpa using K.normalize_image_link_zero_of_local_segments hK hzero
      (0 : E →ₗ[ℝ] ℝ) hu hu hlocal'
  have hcard : (K.link 0).space.ncard = 1 := by
    rw [← K.injOn_normalize_link.ncard_image, hnorm, ncard_singleton]
  obtain ⟨v, hv⟩ := ncard_eq_one.mp hcard
  have hvertices : (K.link 0).vertices = {v} := by
    apply Subset.antisymm
    · exact (K.link 0).vertices_subset_space.trans hv.subset
    · have hvspace : v ∈ (K.link 0).space := hv.symm ▸ mem_singleton v
      obtain ⟨a, ha, _⟩ := mem_space_iff.mp hvspace
      obtain ⟨w, hw⟩ := (K.link 0).nonempty_of_mem_faces ha
      have hwv : w = v := hv.subset ((K.link 0).subset_space ha hw)
      exact singleton_subset_iff.mpr (hwv ▸ (K.link 0).face_subset_vertices ha hw)
  rw [K.ncard_edgeGraph_neighborSet, K.faceLink_singleton_eq_link, hvertices,
    ncard_singleton]

end Geometry.SimplicialComplex
