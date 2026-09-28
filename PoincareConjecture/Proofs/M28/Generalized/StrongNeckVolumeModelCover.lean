import PoincareConjecture.Proofs.M28.Generalized.StrongNeckVolumeCharts

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M28

private abbrev E := EuclideanSpace ℝ (Fin 3)

theorem exists_neckVolumeModelChart_finite_cover (S : ℝ) :
    ∃ t : Finset (univ ×ˢ Icc (-2 * S) (2 * S) : Set RoundCylinderSpace),
      (univ ×ˢ Icc (-2 * S) (2 * S) : Set RoundCylinderSpace) ⊆
        ⋃ z ∈ t, neckVolumeModelChart z.val.1 z.val.2 '' Metric.ball (0 : E) 1 := by
  let K : Set RoundCylinderSpace := univ ×ˢ Icc (-2 * S) (2 * S)
  let U (z : K) : Set RoundCylinderSpace :=
    neckVolumeModelChart z.val.1 z.val.2 '' Metric.ball (0 : E) 1
  have hU (z : K) : IsOpen (U z) := by
    apply (neckVolumeModelChart z.val.1 z.val.2).isOpen_image_of_subset_source
      Metric.isOpen_ball
    rw [neckVolumeModelChart_source]
    exact subset_univ _
  have hcover : K ⊆ ⋃ z : K, U z := by
    intro z hz
    apply mem_iUnion.mpr
    refine ⟨⟨z, hz⟩, 0, by simp, ?_⟩
    exact neckVolumeModelChart_zero z.1 z.2
  exact (isCompact_univ.prod isCompact_Icc).elim_finite_subcover U hU hcover

end PoincareConjecture.M28
