import PoincareConjecture.Proofs.M76.Mathlib.CoreCompressionDisplacement
import PoincareConjecture.Proofs.M76.Mathlib.AffineInterpolationBound










set_option autoImplicit false

open Set Metric

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : SimplicialComplex ℝ E} {p : E → E}




theorem AffineOnFaces.norm_sub_coreCompression_le (hp : K.AffineOnFaces p)
    (hvertex : EqOn p NormedSpace.coreCompression K.vertices)
    {D : ℝ} (hmesh : ∀ s ∈ K.faces, diam (convexHull ℝ (s : Set E)) ≤ D)
    {x : E} (hx : x ∈ K.space) :
    ‖p x - NormedSpace.coreCompression x‖ ≤
      2 * D * (2 - ‖NormedSpace.coreCompression x‖) := by
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  apply hp.norm_sub_le_of_vertex_bound hs hxs
  intro v hv
  have hvK : v ∈ K.vertices := by
    rw [vertices_eq]
    exact mem_biUnion hs hv
  rw [hvertex hvK, norm_sub_rev]
  have hdist : ‖x - v‖ ≤ D := by
    rw [← dist_eq_norm]
    exact (dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull ℝ).isBounded
      hxs (subset_convexHull ℝ _ hv)).trans (hmesh s hs)
  exact (NormedSpace.norm_coreCompression_sub_le_deficit x v).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdist (by norm_num))
      (sub_pos.mpr (NormedSpace.norm_coreCompression_lt_two x)).le)

end Geometry.SimplicialComplex
