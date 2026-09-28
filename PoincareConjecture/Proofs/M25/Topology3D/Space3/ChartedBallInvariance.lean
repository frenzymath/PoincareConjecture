import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldChartTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlowFirstIntegral
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.TangentFlow












set_option autoImplicit false

open Set Metric
open scoped ContDiff InnerProductSpace NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]



theorem boundedFlow_mapsTo_charted_ball (B : BallNeighborhoodChart E F)
    (f : F → F) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ B.chart.target) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ y, ‖f y‖ ≤ L)
    (htan : ∀ x : E, ‖x‖ = 1 →
      ⟪x, fderiv ℝ B.chart.symm (B.chart x) (f (B.chart x))⟫_ℝ = 0) (t : ℝ) :
    MapsTo (fun y => boundedFlow f hK hL y t) B.closedRegion B.closedRegion := by
  obtain ⟨g, hg, hgc, _, hag⟩ := exists_chart_field_extension
    B.chart.symm B.smooth_symm B.smooth f hf hfc hfs
  obtain ⟨k, l, hk, hl⟩ := compactField_bounds g hg hgc
  have hgtan (x : E) (hx : ‖x‖ = 1) : ⟪x, g x⟫_ℝ = 0 := by
    have hxs := B.closedBall_subset_source (mem_closedBall_zero_iff.mpr hx.le)
    have heq := hag (B.chart x) (B.chart.map_source hxs)
    rw [B.chart.left_inv hxs] at heq
    rw [heq]
    exact htan x hx
  have hzero (y : F) (hy : y ∉ B.chart.target) : f y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hy (hfs h))
  rintro y ⟨x, hx, rfl⟩
  have hxs := B.closedBall_subset_source hx
  have hmem (s : ℝ) : boundedFlow f hK hL (B.chart x) s ∈ B.chart.target :=
    boundedFlow_mapsTo_set f hK hL hzero s (B.chart.map_source hxs)
  have hd (s : ℝ) : HasDerivAt
      (fun v => B.chart.symm (boundedFlow f hK hL (B.chart x) v))
      (g (B.chart.symm (boundedFlow f hK hL (B.chart x) s))) s := by
    rw [hag _ (hmem s)]
    have hi := (B.smooth_symm.contDiffAt (B.chart.open_target.mem_nhds (hmem s))).differentiableAt
      (by simp)
    simpa only [Function.comp_def] using
      hi.hasFDerivAt.comp_hasDerivAt s (boundedFlow_hasDerivAt f hK hL (B.chart x) s)
  have heq := boundedField_solution_unique g hk hd (boundedFlow_hasDerivAt g hk hl x)
    (by simp only [boundedFlow_zero, B.chart.left_inv hxs])
  refine ⟨boundedFlow g hk hl x t, tangentFlow_mapsTo_closedBall g hk hl hgtan t hx, ?_⟩
  rw [← congrFun heq t, B.chart.right_inv (hmem t)]



theorem boundedFlow_image_charted_ball (B : BallNeighborhoodChart E F)
    (f : F → F) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ B.chart.target) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ y, ‖f y‖ ≤ L)
    (htan : ∀ x : E, ‖x‖ = 1 →
      ⟪x, fderiv ℝ B.chart.symm (B.chart x) (f (B.chart x))⟫_ℝ = 0) (t : ℝ) :
    (fun y => boundedFlow f hK hL y t) '' B.closedRegion = B.closedRegion := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact boundedFlow_mapsTo_charted_ball B f hf hfc hfs hK hL htan t hx
  · intro y hy
    refine ⟨boundedFlow f hK hL y (-t),
      boundedFlow_mapsTo_charted_ball B f hf hfc hfs hK hL htan (-t) hy, ?_⟩
    simpa only [neg_neg] using boundedFlow_neg f hK hL y (-t)

end PoincareConjecture.M25.Topology3D
