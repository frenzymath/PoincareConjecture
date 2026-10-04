import PoincareLib.Topology.Manifold.Separation.Connected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Compact balls inside an actual open chart

A closed ball strictly inside an open ball chart has the expected
interior and frontier. Its exterior is connected when the ambient space
is connected and locally connected and the model dimension is at least
two. The last step reuses the lower Horizon boundary-neighborhood theorem.
These are StandardEnd E, sections 2-3 of
`tasks/M25/gluing-collar/standard-end-e-plan.md`, for Morgan--Tian A.21,
pp. 510-514.
-/

set_option autoImplicit false

open Set Metric

/-- A nonempty open norm annulus in real dimension at least two is path
connected. StandardEnd E, section 3, for MT A.21, pp. 510-514. -/
theorem isPathConnected_norm_annulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hrank : 1 < Module.rank ℝ E) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    IsPathConnected {x : E | r < ‖x‖ ∧ ‖x‖ < R} := by
  have hprod := (isPathConnected_sphere hrank (0 : E) zero_le_one).prod
    ((convex_Ioo r R).isPathConnected (nonempty_Ioo.mpr hrR))
  have himage : (fun p : E × ℝ => p.2 • p.1) ''
      (sphere (0 : E) 1 ×ˢ Ioo r R) = {x : E | r < ‖x‖ ∧ ‖x‖ < R} := by
    ext x
    constructor
    · rintro ⟨⟨q, s⟩, ⟨hq, hs⟩, rfl⟩
      change r < ‖s • q‖ ∧ ‖s • q‖ < R
      rw [norm_smul, Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp hq,
        mul_one, abs_of_pos (hr.trans_lt hs.1)]
      exact hs
    · intro hx
      have hn : 0 < ‖x‖ := hr.trans_lt hx.1
      refine ⟨(‖x‖⁻¹ • x, ‖x‖), ⟨?_, hx⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
      · exact smul_inv_smul₀ hn.ne' x
  rw [← himage]
  exact hprod.image (continuous_snd.smul continuous_fst)

namespace OpenPartialHomeomorph

variable {E W : Type*} [NormedAddCommGroup E]
  [TopologicalSpace W] (D : OpenPartialHomeomorph E W) {R r : ℝ}

/-- A closed ball strictly inside the chart source maps into its actual
target. StandardEnd E, section 2, for MT A.21, pp. 510-514. -/
theorem image_closedBall_subset_target (hsource : D.source = ball 0 R) (hrR : r < R) :
    D '' closedBall 0 r ⊆ D.target := by
  rintro x ⟨z, hz, rfl⟩
  apply D.map_source
  rw [hsource]
  exact closedBall_subset_ball hrR hz

/-- A compact model ball strictly inside the chart source has compact
image. StandardEnd E, section 2, for MT A.21, pp. 510-514. -/
theorem isCompact_image_closedBall [ProperSpace E]
    (hsource : D.source = ball 0 R) (hrR : r < R) :
    IsCompact (D '' closedBall 0 r) := by
  apply (isCompact_closedBall (0 : E) r).image_of_continuousOn
  apply D.continuousOn.mono
  rw [hsource]
  exact closedBall_subset_ball hrR

/-- Closed balls contained in the source correspond to their actual
images. StandardEnd E, section 2, for MT A.21, pp. 510-514. -/
theorem isImage_closedBall (hsource : D.source = ball 0 R) (hrR : r < R) :
    D.IsImage (closedBall 0 r) (D '' closedBall 0 r) := by
  apply IsImage.of_image_eq
  rw [inter_eq_right.mpr (D.image_closedBall_subset_target hsource hrR), hsource,
    inter_eq_right.mpr (closedBall_subset_ball hrR)]

/-- The interior of a buffered chart ball is exactly the image of the
open model ball. StandardEnd E, section 2, for MT A.21, pp. 510-514. -/
theorem interior_image_closedBall [NormedSpace ℝ E] (hsource : D.source = ball 0 R)
    (hr : 0 < r) (hrR : r < R) :
    interior (D '' closedBall 0 r) = D '' ball 0 r := by
  have h := (D.isImage_closedBall hsource hrR).interior.image_eq
  rw [interior_closedBall (0 : E) hr.ne', hsource,
    inter_eq_right.mpr (ball_subset_ball hrR.le),
    inter_eq_right.mpr (interior_subset.trans
      (D.image_closedBall_subset_target hsource hrR))] at h
  exact h.symm

/-- Compactness excludes any additional frontier outside the actual
target of the chart. StandardEnd E, section 2, for MT A.21, pp. 510-514. -/
theorem frontier_image_closedBall [NormedSpace ℝ E] [ProperSpace E] [T2Space W]
    (hsource : D.source = ball 0 R) (hr : 0 < r) (hrR : r < R) :
    frontier (D '' closedBall 0 r) = D '' sphere 0 r := by
  have hclosed := (D.isCompact_image_closedBall hsource hrR).isClosed
  have hfront : frontier (D '' closedBall 0 r) ⊆ D.target :=
    hclosed.frontier_subset.trans (D.image_closedBall_subset_target hsource hrR)
  have h := (D.isImage_closedBall hsource hrR).frontier.image_eq
  rw [frontier_closedBall (0 : E) hr.ne', hsource,
    inter_eq_right.mpr (sphere_subset_closedBall.trans (closedBall_subset_ball hrR)),
    inter_eq_right.mpr hfront] at h
  exact h.symm

/-- The chart-visible exterior of a closed chart ball is precisely the
image of the open norm annulus. StandardEnd E, section 3, for MT A.21,
pp. 510-514. -/
theorem compl_image_closedBall_inter_target (hsource : D.source = ball 0 R)
    (hrR : r < R) :
    (D '' closedBall 0 r)ᶜ ∩ D.target = D '' {z : E | r < ‖z‖ ∧ ‖z‖ < R} := by
  ext x
  constructor
  · rintro ⟨hx, hxt⟩
    have hzs := D.map_target hxt
    have hzR : ‖D.symm x‖ < R := by
      simpa only [hsource, mem_ball_zero_iff] using hzs
    refine ⟨D.symm x, ⟨?_, hzR⟩, D.right_inv hxt⟩
    by_contra hn
    exact hx ⟨D.symm x, mem_closedBall_zero_iff.mpr (le_of_not_gt hn), D.right_inv hxt⟩
  · rintro ⟨z, hz, rfl⟩
    have hzs : z ∈ D.source := by simpa only [hsource, mem_ball_zero_iff] using hz.2
    refine ⟨?_, D.map_source hzs⟩
    rintro ⟨v, hv, heq⟩
    have hvs : v ∈ D.source := by
      rw [hsource]
      exact closedBall_subset_ball hrR hv
    have hvz : v = z := D.injOn hvs hzs heq
    exact (not_le_of_gt hz.1) (hvz ▸ mem_closedBall_zero_iff.mp hv)

/-- The exterior of a compact chart ball is connected. The annular
boundary neighborhood is connected, so the lower Horizon separation
theorem applies. StandardEnd E, section 3, for MT A.21, pp. 510-514. -/
theorem m25_isConnected_compl_image_closedBall [NormedSpace ℝ E] [ProperSpace E] [T2Space W]
    [ConnectedSpace W] [LocallyConnectedSpace W]
    (hsource : D.source = ball 0 R) (hr : 0 < r) (hrR : r < R)
    (hrank : 1 < Module.rank ℝ E) : IsConnected (D '' closedBall 0 r)ᶜ := by
  have hclosed := (D.isCompact_image_closedBall hsource hrR).isClosed
  have hAU : IsConnected ((D '' closedBall 0 r)ᶜ ∩ D.target) := by
    rw [D.compl_image_closedBall_inter_target hsource hrR]
    apply (isPathConnected_norm_annulus hrank hr.le hrR).isConnected.image D
    apply D.continuousOn.mono
    intro x hx
    simpa only [hsource, mem_ball_zero_iff] using hx.2
  apply Poincare.Topology.isConnected_of_inter_of_frontier_subset
    hclosed.isOpen_compl D.open_target hAU
  · rw [frontier_compl]
    exact hclosed.frontier_subset.trans (D.image_closedBall_subset_target hsource hrR)
  · intro heq
    have hx : D 0 ∈ (D '' closedBall 0 r)ᶜ := heq.symm ▸ mem_univ _
    exact hx ⟨0, by simpa using hr.le, rfl⟩

/-- In a locally path connected ambient space the same chart-ball
exterior is path connected. StandardEnd E, section 3, for MT A.21,
pp. 510-514. -/
theorem isPathConnected_compl_image_closedBall [NormedSpace ℝ E] [ProperSpace E] [T2Space W]
    [ConnectedSpace W] [LocallyPathConnectedSpace W]
    (hsource : D.source = ball 0 R) (hr : 0 < r) (hrR : r < R)
    (hrank : 1 < Module.rank ℝ E) : IsPathConnected (D '' closedBall 0 r)ᶜ := by
  have hopen := (D.isCompact_image_closedBall hsource hrR).isClosed.isOpen_compl
  apply hopen.isConnected_iff_isPathConnected.mp
  exact D.m25_isConnected_compl_image_closedBall hsource hr hrR hrank

end OpenPartialHomeomorph
