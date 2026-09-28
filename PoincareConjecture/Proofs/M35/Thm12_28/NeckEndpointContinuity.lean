import PoincareConjecture.Proofs.M35.Thm12_28.NeckCompactness
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [ConnectedSpace M] {g : RiemannianMetric 3 M}

theorem axial_dist_le_between (N : EpsilonNeck g) (q : UnitTwoSphere)
    {s t : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    letI : MetricSpace M := Proofs.M09.selectedMetricSpace g
    dist (N.coordinate_map (q, s)) (N.coordinate_map (q, t)) ≤
      2 * N.scale * |s - t| := by
  let : MetricSpace M := Proofs.M09.selectedMetricSpace g
  have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞
      (fun r : ℝ => N.coordinate_map (q, r)) (Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    N.coordinate_map_smooth.comp (contMDiffOn_const.prodMk contMDiffOn_id)
      (fun _ hr => ⟨mem_univ _, hr⟩)
  have hspeed (r : ℝ) (hr : r ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
      g.tangentNorm (N.coordinate_map (q, r))
        (curveVelocity (fun a => N.coordinate_map (q, a)) r) ≤ 2 * N.scale := by
    rw [N.axial_curve_velocity q hr]
    exact N.axial_tangentNorm_le q hr
  have hbound (a b : ℝ) (ha : a ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
      (hb : b ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (hab : a ≤ b) :
      dist (N.coordinate_map (q, a)) (N.coordinate_map (q, b)) ≤
        2 * N.scale * (b - a) := by
    have hsub : Icc a b ⊆ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      fun _ hr => ⟨ha.1.trans_le hr.1, hr.2.trans_lt hb.2⟩
    exact Proofs.M09.selectedMetric_dist_le_of_speed_le g
      (fun r => N.coordinate_map (q, r)) a b (2 * N.scale) hab
      (mul_nonneg (by norm_num) N.scale_pos.le)
      ((hsmooth.mono hsub).of_le (by norm_num)) (fun r hr => hspeed r (hsub hr))
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hbound s t hs ht hst
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hts), dist_comm] using hbound t s ht hs hts

theorem axial_lipschitzOn (N : EpsilonNeck g) (q : UnitTwoSphere) :
    letI : MetricSpace M := Proofs.M09.selectedMetricSpace g
    LipschitzOnWith ⟨2 * N.scale, mul_nonneg (by norm_num) N.scale_pos.le⟩
      (fun r : ℝ => N.coordinate_map (q, r)) (Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) := by
  let : MetricSpace M := Proofs.M09.selectedMetricSpace g
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro s hs t ht
  change dist (N.coordinate_map (q, s)) (N.coordinate_map (q, t)) ≤
    2 * N.scale * dist s t
  rw [Real.dist_eq]
  exact N.axial_dist_le_between q hs ht

theorem exists_axial_limit (N : EpsilonNeck g) (hcomplete : MetricComplete g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Icc (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ∃ p ∈ closure N.carrier,
      Tendsto (fun r : ℝ => N.coordinate_map (q, r))
        (𝓝[Ioo (-N.epsilon⁻¹) N.epsilon⁻¹] s) (𝓝 p) := by
  let : MetricSpace M := Proofs.M09.selectedMetricSpace g
  have : CompleteSpace M := Proofs.M09.selectedMetricSpace_complete g hcomplete
  have hends : -N.epsilon⁻¹ < N.epsilon⁻¹ := by
    have := inv_pos.mpr N.epsilon_pos
    linarith
  have hsclosure : s ∈ closure (Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) := by
    rwa [closure_Ioo hends.ne]
  have : NeBot (𝓝[Ioo (-N.epsilon⁻¹) N.epsilon⁻¹] s) :=
    mem_closure_iff_nhdsWithin_neBot.mp hsclosure
  have hcauchy : Cauchy (𝓝[Ioo (-N.epsilon⁻¹) N.epsilon⁻¹] s) :=
    cauchy_nhds.mono nhdsWithin_le_nhds
  obtain ⟨p, hp⟩ := cauchy_map_iff_exists_tendsto.mp
    (hcauchy.map_of_le (N.axial_lipschitzOn q).uniformContinuousOn inf_le_right)
  refine ⟨p, isClosed_closure.mem_of_tendsto hp ?_, hp⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact subset_closure (N.coordinatePartialDiffeomorph.map_source ⟨mem_univ _, hr⟩)

end PoincareConjecture.EpsilonNeck
