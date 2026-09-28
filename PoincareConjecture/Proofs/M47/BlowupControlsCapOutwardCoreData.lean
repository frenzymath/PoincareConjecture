import PoincareConjecture.Proofs.M47.BlowupControlsCapOutwardBall
import PoincareConjecture.Proofs.M47.BlowupControlsCapOutwardRadius
import PoincareConjecture.Proofs.M47.BlowupControlsCapOutwardConstant
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNormalizedBalls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {g : RiemannianMetric 3 M}

theorem exists_cap_outward_core_data (N : CapCertificate g)
    (hcomplete : MetricComplete g) (hsmall : N.epsilon ≤ 1 / 1200)
    {b : ℝ} (hb : -N.epsilon⁻¹ < b) (hmargin : b + 8 < N.epsilon⁻¹) :
    ∃ radius : M → ℝ, ∃ bound : ℝ, N.cap_constant⁻¹ < bound ∧
      (∀ y ∈ N.core, radius y = N.core_radius y) ∧
      ∀ y ∈ N.recutCarrier b,
        0 < radius y ∧
        scalarCurvatureSupOn g N.connection (g.ball y (radius y)) = (radius y)⁻¹ ^ 2 ∧
        IsCompact (closure (g.ball y (radius y))) ∧
        closure (g.ball y (radius y)) ⊆ N.carrier ∧
        ENNReal.ofReal (bound * radius y ^ 3) ≤ calibratedMetricVolume g (g.ball y (radius y)) := by
  classical
  obtain ⟨oldBound, hOldBound, hOldVolume⟩ := N.core_ball_volume_lower
  let bound := min oldBound (1 / 432 : ℝ)
  have hC := cap_constant_gt_nine_hundred N hsmall
  have hInv : N.cap_constant⁻¹ < (1 / 432 : ℝ) := by
    simpa only [one_div] using
      one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 432)
        (show (432 : ℝ) < N.cap_constant by linarith)
  have hbound : N.cap_constant⁻¹ < bound := lt_min hOldBound hInv
  have hsmallEnd : N.end_neck.epsilon ≤ 1 / 1200 := by rwa [N.end_neck_epsilon]
  have hsmallBoundary : N.boundary_neck.epsilon ≤ 1 / 1200 := by
    rwa [N.boundary_neck_epsilon]
  have hnew (y : M) (hy : y ∈ N.recutCarrier b) (hyold : y ∉ N.core) :
      ∃ r : ℝ, 0 < r ∧ scalarCurvatureSupOn g N.connection (g.ball y r) = r⁻¹ ^ 2 ∧
        IsCompact (closure (g.ball y r)) ∧ closure (g.ball y r) ⊆ N.carrier ∧
        ENNReal.ofReal (bound * r ^ 3) ≤ calibratedMetricVolume g (g.ball y r) := by
    obtain ⟨r, hr, _, hnormal, hcompact⟩ := g.exists_scalar_normalized_ball N.connection
      hcomplete y (N.scalar_pos y (N.recutCarrier_subset_carrier b hy))
    have hbounded : BddAbove (N.connection.scalarCurvature '' g.ball y r) :=
      (hcompact.image (M34.contMDiff_scalarCurvature N.connection).continuous).bddAbove.mono
        (image_mono subset_closure)
    have hcoefficient : bound * r ^ 3 ≤ r ^ 3 / 432 := by
      have h := mul_le_mul_of_nonneg_right (min_le_right oldBound (1 / 432 : ℝ))
        (pow_nonneg hr.le 3)
      dsimp [bound]
      nlinarith only [h]
    rcases hy with hcore | hend
    · have hcentral : y ∈ N.boundary_neck.central_sphere := by
        rw [← N.boundary_eq_neck_sphere, ← N.core_frontier_eq_boundary, frontier,
          N.closed_core_compact.isClosed.closure_eq, ← N.core_eq_interior_closed_core]
        exact ⟨hcore, hyold⟩
      have hrscale := cap_neck_normalized_radius_le N.boundary_neck hsmallBoundary
        (N.boundary_neck.central_sphere_subset hcentral) hr
        (by simpa only [N.boundary_neck_connection] using hbounded)
        (by simpa only [N.boundary_neck_connection] using hnormal)
      have hcapture := Proofs.M47.scalar_normalized_core_ball_captured N N.end_neck
        N.connection N.end_neck_connection rfl rfl hcore hr hbounded hnormal
      have hvolume := cap_neck_central_ball_volume N.boundary_neck hsmallBoundary
        hcentral hr hrscale
      exact ⟨r, hr, hnormal, hcompact, hcapture.2,
        (ENNReal.ofReal_le_ofReal hcoefficient).trans hvolume⟩
    · have hrscale := cap_neck_normalized_radius_le N.end_neck hsmallEnd hend.1 hr
        (by simpa only [N.end_neck_connection] using hbounded)
        (by simpa only [N.end_neck_connection] using hnormal)
      have hcapture := cap_outward_small_ball_captured N hb hmargin (Or.inr hend) hr hrscale
      have hz : -N.end_neck.epsilon⁻¹ < (N.end_neck.coordinate_inverse y).2 := by
        simpa only [N.end_neck_epsilon] using hend.2.1
      have hright : (N.end_neck.coordinate_inverse y).2 + 1 < N.end_neck.epsilon⁻¹ := by
        rw [N.end_neck_epsilon]
        linarith [hend.2.2]
      have hvolume := cap_neck_small_ball_volume N.end_neck
        (N.end_neck.coordinate_inverse y).1 hz hright hr hrscale
      rw [show N.end_neck.coordinate_map
          ((N.end_neck.coordinate_inverse y).1, (N.end_neck.coordinate_inverse y).2) = y
        from M36.neck_coordinate_inverse N.end_neck hend.1] at hvolume
      exact ⟨r, hr, hnormal, hcompact, hcapture.2,
        (ENNReal.ofReal_le_ofReal hcoefficient).trans hvolume⟩
  have hchoice : ∀ y : M, ∃ r : ℝ, (y ∈ N.core → r = N.core_radius y) ∧
      (y ∈ N.recutCarrier b → 0 < r ∧
        scalarCurvatureSupOn g N.connection (g.ball y r) = r⁻¹ ^ 2 ∧
        IsCompact (closure (g.ball y r)) ∧ closure (g.ball y r) ⊆ N.carrier ∧
        ENNReal.ofReal (bound * r ^ 3) ≤ calibratedMetricVolume g (g.ball y r)) := by
    intro y
    by_cases hyold : y ∈ N.core
    · refine ⟨N.core_radius y, fun _ => rfl, fun _ =>
        ⟨N.core_radius_pos y hyold, N.core_radius_eq y hyold,
          N.core_ball_compact y hyold, N.core_ball_subset y hyold, ?_⟩⟩
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (pow_nonneg (N.core_radius_pos y hyold).le 3))).trans (hOldVolume y hyold)
    · by_cases hy : y ∈ N.recutCarrier b
      · obtain ⟨r, hdata⟩ := hnew y hy hyold
        exact ⟨r, fun h => (hyold h).elim, fun _ => hdata⟩
      · exact ⟨1, fun h => (hyold h).elim, fun h => (hy h).elim⟩
  choose radius hradius using hchoice
  exact ⟨radius, bound, hbound, fun y hy => (hradius y).1 hy,
    fun y hy => (hradius y).2 hy⟩

end PoincareConjecture.M47
