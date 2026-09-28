import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient.Ascent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.AscendingSlope.Level









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle NNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem infDist_level_le_of_gradient_lower_bound
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) {c t : ℝ} (hc : 0 < c) (ht : f x < t) :
    letI := g.toMetricSpace
    (∀ y ∈ Metric.ball x ((t - f x) / c), f y < t →
      c < g.tangentNorm y (g.gradient f y)) →
    (f ⁻¹' {t}).Nonempty ∧ Metric.infDist x (f ⁻¹' {t}) ≤ (t - f x) / c := by
  let := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hcomplete
  intro hgrad
  apply Poincare.infDist_level_le_of_local_ascent hc hf.continuous ht
  intro y hy hyt s hs
  obtain ⟨z, hz, hinc⟩ := g.exists_arbitrarily_close_ascent_of_lt_gradient_norm
    (hf.mdifferentiable (by simp) y) hc.le (hgrad y hy hyt) s hs
  exact ⟨z, ENNReal.toReal_lt_of_lt_ofReal hz, hinc⟩



theorem sub_le_mul_infDist_level_of_lipschitzOn_closedBall
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g)
    {f : M → ℝ} (hf : Continuous f) {t : ℝ} (hne : (f ⁻¹' {t}).Nonempty)
    (x : M) {L : ℝ≥0} :
    letI := g.toMetricSpace
    LipschitzOnWith L f (Metric.closedBall x (Metric.infDist x (f ⁻¹' {t}))) →
    t - f x ≤ L * Metric.infDist x (f ⁻¹' {t}) := by
  let := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hcomplete
  intro hLip
  have hclosed : IsClosed (f ⁻¹' {t}) := isClosed_singleton.preimage hf
  obtain ⟨p, hp, hnearest⟩ := hclosed.exists_infDist_eq_dist hne x
  have hpt : f p = t := hp
  have hxball : x ∈ Metric.closedBall x (Metric.infDist x (f ⁻¹' {t})) :=
    Metric.mem_closedBall_self Metric.infDist_nonneg
  have hpball : p ∈ Metric.closedBall x (Metric.infDist x (f ⁻¹' {t})) := by
    rw [Metric.mem_closedBall, dist_comm, ← hnearest]
  have hbound := hLip.dist_le_mul p hpball x hxball
  rw [Real.dist_eq, hpt, dist_comm p x, ← hnearest] at hbound
  exact (le_abs_self (t - f x)).trans hbound


theorem div_le_infDist_level_of_lipschitzOn_closedBall
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g)
    {f : M → ℝ} (hf : Continuous f) {t : ℝ} (hne : (f ⁻¹' {t}).Nonempty)
    (x : M) {L : ℝ≥0} (hL : 0 < L) :
    letI := g.toMetricSpace
    LipschitzOnWith L f (Metric.closedBall x (Metric.infDist x (f ⁻¹' {t}))) →
    (t - f x) / L ≤ Metric.infDist x (f ⁻¹' {t}) := by
  let := g.toMetricSpace
  intro hLip
  apply (div_le_iff₀ (show 0 < (L : ℝ) from hL)).mpr
  simpa only [mul_comm] using
    g.sub_le_mul_infDist_level_of_lipschitzOn_closedBall hcomplete hf hne x hLip



theorem abs_sub_le_mul_toReal_edist_of_gradient_bound_closedBall
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x y : M) {L : ℝ≥0} :
    letI := g.toMetricSpace
    (∀ z ∈ Metric.closedBall x (g.edist x y).toReal,
      g.tangentNorm z (g.gradient f z) ≤ L) →
    |f y - f x| ≤ L * (g.edist x y).toReal := by
  let := g.toMetricSpace
  intro hgrad
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hcomplete x y
  have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have h0 := hI (show (0 : ℝ) ∈ Icc 0 1 by simp)
  obtain ⟨C, hC⟩ := hγ.exists_constant_tangentNorm (by linarith)
  have hv := (hγ.hasDerivAt_chart_at h0 x (by
    simpa only [hγ0] using mem_extChartAt_source x)).1
  have hC0 : g.tangentNorm x (deriv (fun s => extChartAt (𝓡 n) x (γ s)) 0) = C := by
    simpa only [chartCoefficients_self, tangentNorm] using
      (hγ.tangentNorm_initial h0 hγ0 hv).symm.trans (hC 0 h0)
  have hCd : (C : ℝ) = (g.edist x y).toReal := by
    have h := hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hv hmin
    rw [hC0] at h
    simpa only [ENNReal.toReal_ofReal C.coe_nonneg] using congrArg ENNReal.toReal h
  have hspeed (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      g.tangentNorm (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) = (g.edist x y).toReal :=
    (hC s (hI hs)).trans hCd
  have hball (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      γ s ∈ Metric.closedBall x (g.edist x y).toReal := by
    have hxs := congrArg ENNReal.toReal (hmin 0 (by simp) s hs)
    rw [hγ0, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
      zero_sub, abs_neg, abs_of_nonneg hs.1] at hxs
    rw [Metric.mem_closedBall, dist_comm]
    change (g.edist x (γ s)).toReal ≤ (g.edist x y).toReal
    rw [hxs]
    exact mul_le_of_le_one_left ENNReal.toReal_nonneg hs.2
  have hderiv (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => f (γ t))
        (mvfderiv (𝓡 n) f (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)) s := by
    have hγd := (hγ.contMDiffAt (hI hs)).mdifferentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
    exact ((hf.mdifferentiable (by simp) (γ s)).hasMFDerivAt.comp s
      hγd.hasMFDerivAt).hasFDerivAt.hasDerivAt
  have hbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖mvfderiv (𝓡 n) f (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)‖ ≤
        L * (g.edist x y).toReal := by
    have hcs : |mvfderiv (𝓡 n) f (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)| ≤
        g.tangentNorm (γ s) (g.gradient f (γ s)) *
          g.tangentNorm (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      rw [← g.inner_gradient]
      exact abs_real_inner_le_norm (g.gradient f (γ s))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
    rw [Real.norm_eq_abs]
    calc
      _ ≤ g.tangentNorm (γ s) (g.gradient f (γ s)) *
          g.tangentNorm (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) := hcs
      _ ≤ L * g.tangentNorm (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) :=
        mul_le_mul_of_nonneg_right (hgrad (γ s) (hball s hs)) (Real.sqrt_nonneg _)
      _ = L * (g.edist x y).toReal := by rw [hspeed s hs]
  have hvalue := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hderiv s hs).hasDerivWithinAt) hbound
    (by simp : (0 : ℝ) ∈ Icc 0 1) (by simp : (1 : ℝ) ∈ Icc 0 1)
  simpa only [Real.norm_eq_abs, hγ0, hγ1, sub_zero, abs_one, mul_one] using hvalue



theorem sub_le_mul_infDist_level_of_gradient_upper_bound
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {t : ℝ} (hne : (f ⁻¹' {t}).Nonempty) (x : M) {L : ℝ≥0} :
    letI := g.toMetricSpace
    (∀ y ∈ Metric.closedBall x (Metric.infDist x (f ⁻¹' {t})),
      g.tangentNorm y (g.gradient f y) ≤ L) →
    t - f x ≤ L * Metric.infDist x (f ⁻¹' {t}) := by
  let := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hcomplete
  intro hgrad
  have hclosed : IsClosed (f ⁻¹' {t}) := isClosed_singleton.preimage hf.continuous
  obtain ⟨p, hp, hnearest⟩ := hclosed.exists_infDist_eq_dist hne x
  have hpt : f p = t := hp
  have hdist : (g.edist x p).toReal = Metric.infDist x (f ⁻¹' {t}) := hnearest.symm
  have hvalue := g.abs_sub_le_mul_toReal_edist_of_gradient_bound_closedBall hcomplete hf x p
    (by simpa only [hdist] using hgrad)
  rw [hpt, hdist] at hvalue
  exact (le_abs_self (t - f x)).trans hvalue



theorem div_le_infDist_level_of_gradient_upper_bound
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {t : ℝ} (hne : (f ⁻¹' {t}).Nonempty) (x : M) {L : ℝ≥0} (hL : 0 < L) :
    letI := g.toMetricSpace
    (∀ y ∈ Metric.closedBall x (Metric.infDist x (f ⁻¹' {t})),
      g.tangentNorm y (g.gradient f y) ≤ L) →
    (t - f x) / L ≤ Metric.infDist x (f ⁻¹' {t}) := by
  let := g.toMetricSpace
  intro hgrad
  apply (div_le_iff₀ (show 0 < (L : ℝ) from hL)).mpr
  simpa only [mul_comm] using
    g.sub_le_mul_infDist_level_of_gradient_upper_bound hcomplete hf hne x hgrad

end PoincareConjecture.RiemannianMetric
