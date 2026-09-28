import PoincareConjecture.Proofs.M25.Topology3D.Space3.OrientedCollarCorrection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood












set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]



theorem exists_ball_chart_collar_match (B : BallNeighborhoodChart E E)
    (R : OpenPartialHomeomorph E E)
    (hR : ContDiffOn ℝ ∞ R R.source) (hRi : ContDiffOn ℝ ∞ R.symm R.target)
    (hS : sphere (0 : E) 1 ⊆ R.source)
    (hboundary : ∀ x ∈ sphere (0 : E) 1, R x = B.chart x)
    (hout : ∀ x ∈ R.source, 1 < ‖x‖ → R x ∉ B.closedRegion) :
    ∃ C : BallNeighborhoodChart E E,
      C.inside = B.inside ∧ C.closedRegion = B.closedRegion ∧ C.boundary = B.boundary ∧
      ∀ᶠ x in 𝓝ˢ (sphere (0 : E) 1), C.chart x = R x := by
  let T := R.trans B.chart.symm
  have hTS : sphere (0 : E) 1 ⊆ T.source := by
    intro x hx
    refine ⟨hS hx, ?_⟩
    change R x ∈ B.chart.target
    rw [hboundary x hx]
    exact B.chart.map_source (B.closedBall_subset_source (sphere_subset_closedBall hx))
  have hT : ContDiffOn ℝ ∞ T T.source :=
    B.smooth_symm.comp (hR.mono inter_subset_left) (fun _ hx => hx.2)
  have hTi : ContDiffOn ℝ ∞ T.symm T.target :=
    hRi.comp (B.smooth.mono inter_subset_left) (fun _ hx => hx.2)
  have hfix (x : E) (hx : x ∈ sphere (0 : E) 1) : T x = x := by
    change B.chart.symm (R x) = x
    rw [hboundary x hx]
    exact B.chart.left_inv (B.closedBall_subset_source (sphere_subset_closedBall hx))
  have htext (x : E) (hx : x ∈ sphere (0 : E) 1) :
      ∀ᶠ y in 𝓝 x, 1 ≤ ‖y‖ → 1 ≤ ‖T y‖ := by
    filter_upwards [T.open_source.mem_nhds (hTS hx)] with y hy hnorm
    rcases eq_or_lt_of_le hnorm with heq | hlt
    · rw [hfix y (mem_sphere_zero_iff_norm.mpr heq.symm), heq]
    · by_contra h
      apply hout y hy.1 hlt
      refine ⟨T y, mem_closedBall_zero_iff.mpr (le_of_lt (lt_of_not_ge h)), ?_⟩
      exact B.chart.right_inv hy.2
  obtain ⟨F, hFS, hFT, hFball, hFclosed, _⟩ :=
    exists_oriented_collar_extension T hT hTi hTS hfix htext
  let C : BallNeighborhoodChart E E := {
    chart := F.toHomeomorph.toOpenPartialHomeomorph.trans B.chart
    closedBall_subset_source := by
      intro x hx
      exact ⟨mem_univ _, B.closedBall_subset_source (hFclosed ▸ mem_image_of_mem F hx)⟩
    smooth := B.smooth.comp F.contDiff.contDiffOn (fun _ hx => hx.2)
    smooth_symm := F.symm.contDiff.comp_contDiffOn
      (B.smooth_symm.mono inter_subset_left) }
  have hinside : C.inside = B.inside := by
    change (B.chart ∘ F) '' ball 0 1 = B.chart '' ball 0 1
    rw [image_comp, hFball]
  have hclosed : C.closedRegion = B.closedRegion := by
    change (B.chart ∘ F) '' closedBall 0 1 = B.chart '' closedBall 0 1
    rw [image_comp, hFclosed]
  have hbd : C.boundary = B.boundary := by
    apply image_congr
    intro x hx
    change B.chart (F x) = B.chart x
    rw [hFS x hx]
  refine ⟨C, hinside, hclosed, hbd, ?_⟩
  filter_upwards [hFT, T.open_source.mem_nhdsSet.mpr hTS] with x hx hxs
  change B.chart (F x) = R x
  rw [hx]
  exact B.chart.right_inv hxs.2

end PoincareConjecture.M25.Topology3D
