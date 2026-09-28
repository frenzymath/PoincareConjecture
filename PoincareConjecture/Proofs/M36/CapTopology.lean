import PoincareConjecture.Proofs.M36.CollapseMap
import PoincareConjecture.Proofs.M36.ClosedCapImage










set_option autoImplicit false

open scoped Manifold ContDiff ENNReal Topology

universe u

namespace PoincareConjecture.M36

theorem radialArclength_norm_nonneg (g₀ : StandardInitialMetric) (x : StandardCapSpace) :
    0 ≤ radialArclength g₀ ‖x‖ := by
  simpa only [radialArclength_zero] using
    (radialArclength_strictMono g₀).monotone (norm_nonneg x)

theorem standard_mem_ball_radial (g₀ : StandardInitialMetric) {r : ℝ} (hr : 0 < r)
    (x : StandardCapSpace) :
    x ∈ g₀.metric.ball 0 r ↔ radialArclength g₀ ‖x‖ < r := by
  change g₀.metric.edist 0 x < ENNReal.ofReal r ↔ _
  rw [standard_edist_zero, ENNReal.ofReal_lt_ofReal_iff hr]

theorem standard_ball_subset_output (g₀ : StandardInitialMetric)
    {r L : ℝ} (hr : 0 < r) (hrL : r ≤ L) :
    g₀.metric.ball 0 r ⊆ Metric.ball 0 (radialEuclideanRadius g₀ L) := by
  rw [standard_ball_eq_euclidean g₀ hr]
  exact Metric.ball_subset_ball ((radialEuclideanRadius_strictMono g₀).monotone hrL)

theorem surgeryBallChart_image_of_subset (g₀ : StandardInitialMetric) (L : ℝ)
    [Nonempty (SurgeryBall.{u} g₀ L)] {U : Set StandardCapSpace}
    (hU : U ⊆ Metric.ball 0 (radialEuclideanRadius g₀ L)) :
    surgeryBallChart.{u} g₀ L '' U = surgeryBallInclusion g₀ L ⁻¹' U := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change surgeryBallInclusion g₀ L (surgeryBallChart g₀ L x) ∈ U
    rwa [surgeryBallChart_right_inverse g₀ L (hU hx)]
  · intro hy
    exact ⟨surgeryBallInclusion g₀ L y, hy, surgeryBallChart_left_inverse g₀ L y⟩

theorem surgeryBallChart_image_standardBall (g₀ : StandardInitialMetric)
    (L : ℝ) [Nonempty (SurgeryBall.{u} g₀ L)] {r : ℝ} (hr : 0 < r) (hrL : r ≤ L) :
    surgeryBallChart.{u} g₀ L '' g₀.metric.ball 0 r =
      {y | radialArclength g₀ ‖surgeryBallInclusion g₀ L y‖ < r} := by
  rw [surgeryBallChart_image_of_subset g₀ L (standard_ball_subset_output g₀ hr hrL)]
  ext y
  exact standard_mem_ball_radial g₀ hr _

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem surgeryOuterRadius_gt_chartRadius (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    g₀.cylindrical_end.radius + 5 < surgeryOuterRadius g₀ N.epsilon := by
  have he : N.epsilon < 1 := lt_trans N.epsilon_lt_half (by norm_num)
  have hi := (one_lt_inv₀ N.epsilon_pos).mpr he
  dsimp [surgeryOuterRadius, surgeryCapRadius]
  linarith

theorem surgeryCapChart_contMDiffOn (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (surgeryBallChart.{u} g₀ (surgeryOuterRadius g₀ N.epsilon))
      (g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5)) :=
  (surgeryBallChart_contMDiffOn g₀ _).mono
    (standard_ball_subset_output g₀ (by linarith [g₀.cylindrical_end.radius_pos])
      (surgeryOuterRadius_gt_chartRadius g₀ N).le)

theorem surgeryCapChart_closed_image (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    surgeryBallChart.{u} g₀ (surgeryOuterRadius g₀ N.epsilon) ''
      {x | g₀.metric.edist 0 x ≤ ENNReal.ofReal (surgeryCapRadius g₀)} =
      closure (surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon) ''
        g₀.metric.ball 0 (surgeryCapRadius g₀)) :=
  surgery_closed_cap_image g₀ (surgeryCapChart_contMDiffOn g₀ N).continuousOn

theorem surgeryCapChart_closure_radial (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    closure (surgeryBallChart.{u} g₀ (surgeryOuterRadius g₀ N.epsilon) ''
      g₀.metric.ball 0 (surgeryCapRadius g₀)) =
      {y | radialArclength g₀
        ‖surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y‖ ≤ surgeryCapRadius g₀} := by
  rw [← surgeryCapChart_closed_image g₀ N]
  have hU : {x | g₀.metric.edist 0 x ≤ ENNReal.ofReal (surgeryCapRadius g₀)} ⊆
      Metric.ball 0 (radialEuclideanRadius g₀ (surgeryOuterRadius g₀ N.epsilon)) := by
    apply Set.Subset.trans _ (standard_ball_subset_output g₀
      (by linarith [g₀.cylindrical_end.radius_pos]) (surgeryOuterRadius_gt_chartRadius g₀ N).le)
    intro x hx
    exact lt_of_le_of_lt hx (ENNReal.ofReal_lt_ofReal_iff
      (show 0 < g₀.cylindrical_end.radius + 5 by linarith [g₀.cylindrical_end.radius_pos])
        |>.mpr (by dsimp [surgeryCapRadius]; linarith))
  rw [surgeryBallChart_image_of_subset g₀ _ hU]
  ext y
  change g₀.metric.edist 0 _ ≤ ENNReal.ofReal (surgeryCapRadius g₀) ↔ _
  rw [standard_edist_zero, ENNReal.ofReal_le_ofReal_iff (surgeryCapRadius_pos g₀).le]
  rfl

theorem surgeryCapChart_frontier_radial (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    frontier (surgeryBallChart.{u} g₀ (surgeryOuterRadius g₀ N.epsilon) ''
      g₀.metric.ball 0 (surgeryCapRadius g₀)) =
      {y | radialArclength g₀
        ‖surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y‖ = surgeryCapRadius g₀} := by
  have hsub := standard_ball_subset_output g₀ (surgeryCapRadius_pos g₀)
    (show surgeryCapRadius g₀ ≤ surgeryOuterRadius g₀ N.epsilon from
      le_add_of_nonneg_right (inv_pos.mpr N.epsilon_pos).le)
  rw [surgeryBallChart_image_of_subset g₀ _ hsub,
    ← (surgeryBallInclusion_isOpenEmbedding g₀ _).isOpenMap.preimage_frontier_eq_frontier_preimage
      (surgeryBallInclusion_isOpenEmbedding g₀ _).continuous,
    standard_frontier_ball g₀ (surgeryCapRadius_pos g₀)]
  ext y
  change g₀.metric.edist 0 _ = ENNReal.ofReal (surgeryCapRadius g₀) ↔ _
  rw [standard_edist_zero, ENNReal.ofReal_eq_ofReal_iff
    (radialArclength_norm_nonneg g₀ _) (surgeryCapRadius_pos g₀).le]
  rfl

theorem surgeryRetainedInverse_height (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)) :
    (N.coordinate_inverse (surgeryRetainedInverse g₀ N y)).2 =
      surgeryCapRadius g₀ - radialArclength g₀
        ‖surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y‖ := by
  unfold surgeryRetainedInverse
  rw [neck_inverse_coordinate N _ (surgeryRetainedInverse_coordinate_mem g₀ N hcut y)]
  rfl

theorem surgeryCollapse_negative_image (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) :
    surgeryCollapse g₀ N '' N.region (-N.epsilon⁻¹) 0 =
      {y | surgeryCapRadius g₀ < radialArclength g₀
        ‖surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y‖} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_ofPred_eq, surgeryCollapse_arclength g₀ N hx.1]
    exact lt_of_lt_of_le (by linarith [hx.2.2]) (le_max_left _ _)
  · intro hy
    refine ⟨surgeryRetainedInverse g₀ N y, ?_, surgeryCollapse_right_inverse g₀ N hcut y⟩
    have hx := surgeryRetainedInverse_mem g₀ N hcut y
    refine ⟨hx, (N.coordinate_inverse_mem _ hx).2.1, ?_⟩
    rw [surgeryRetainedInverse_height g₀ N hcut]
    exact sub_neg.mpr hy

theorem surgeryCollapse_central_image (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) :
    surgeryCollapse g₀ N '' N.central_sphere =
      {y | radialArclength g₀
        ‖surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y‖ = surgeryCapRadius g₀} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases (neck_central_iff N).mp hx with ⟨hx, hs⟩
    rw [Set.mem_ofPred_eq, surgeryCollapse_arclength g₀ N hx, hs, sub_zero,
      max_eq_left (surgeryCapRadius_pos g₀).le]
  · intro hy
    refine ⟨surgeryRetainedInverse g₀ N y, ?_, surgeryCollapse_right_inverse g₀ N hcut y⟩
    apply (neck_central_iff N).mpr
    refine ⟨surgeryRetainedInverse_mem g₀ N hcut y, ?_⟩
    rw [surgeryRetainedInverse_height g₀ N hcut, hy, sub_self]

theorem surgeryCap_boundary (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) :
    surgeryCollapse g₀ N '' N.central_sphere =
      frontier (surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon) ''
        g₀.metric.ball 0 (surgeryCapRadius g₀)) := by
  rw [surgeryCollapse_central_image g₀ N hcut, surgeryCapChart_frontier_radial g₀ N]

theorem surgeryCap_exterior (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) :
    (closure (surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon) ''
      g₀.metric.ball 0 (surgeryCapRadius g₀)))ᶜ =
      surgeryCollapse g₀ N '' N.region (-N.epsilon⁻¹) 0 := by
  rw [surgeryCapChart_closure_radial g₀ N, surgeryCollapse_negative_image g₀ N hcut]
  ext y
  change (¬ radialArclength g₀
    ‖surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y‖ ≤ surgeryCapRadius g₀) ↔ _
  simp only [Set.mem_ofPred_eq]
  exact not_le

theorem surgeryCap_output_cover (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) :
    (surgeryCollapse g₀ N '' N.region (-N.epsilon⁻¹) 0) ∪
      closure (surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon) ''
        g₀.metric.ball 0 (surgeryCapRadius g₀)) = Set.univ := by
  rw [← surgeryCap_exterior g₀ N hcut]
  exact Set.compl_union_self _

theorem surgeryCollapse_positive_cap (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    surgeryCollapse g₀ N '' N.region 0 N.epsilon⁻¹ ⊆
      closure (surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon) ''
        g₀.metric.ball 0 (surgeryCapRadius g₀)) := by
  rw [surgeryCapChart_closure_radial g₀ N]
  rintro _ ⟨x, hx, rfl⟩
  rw [Set.mem_ofPred_eq, surgeryCollapse_arclength g₀ N hx.1]
  exact max_le (by linarith [hx.2.1]) (surgeryCapRadius_pos g₀).le

theorem surgeryCollapse_positive_tail (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) :
    ∃ b : ℝ, 0 < b ∧ b < N.epsilon⁻¹ ∧
      ∀ x ∈ N.carrier, b ≤ (N.coordinate_inverse x).2 →
        surgeryCollapse g₀ N x = surgeryBallTip g₀ (surgeryOuterRadius_pos g₀ N) :=
  ⟨surgeryCapRadius g₀, surgeryCapRadius_pos g₀, hcut,
    fun _ hx hs => surgeryCollapse_tail g₀ N hx hs⟩

end PoincareConjecture.M36
