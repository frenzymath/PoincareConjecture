import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.BackwardControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Uniform

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RiemannianMetric

theorem radial_lower_bound_on_ball
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p q : M) {b r : ℝ}
    (hmargin : b + r ≤ (g.edist p q).toReal) :
    ∀ x ∈ g.ball q r, b < (g.edist p x).toReal := by
  let := g.toMetricSpace
  intro x hx
  have hx' : dist q x < r := by
    rw [← g.toMetricSpace_ball, Metric.mem_ball, dist_comm] at hx
    exact hx
  have htriangle := dist_triangle p x q
  rw [dist_comm x q] at htriangle
  change b + r ≤ dist p q at hmargin
  change b < dist p x
  linarith

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def ancientRescaleAt (F : RicciFlow n M (Iic 0))
    (Q : ℝ) (hQ : 0 < Q) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) : RicciFlow n M (Iic 0) :=
  F.parabolicRescale Q hQ t₀
    (fun s hs => (add_le_of_nonpos_right
      (div_nonpos_of_nonpos_of_nonneg hs hQ.le)).trans ht₀)
    ordConnected_Iic ⟨-1, by simp, 0, by simp, by norm_num⟩

theorem ancientRescaleAt_metric (F : RicciFlow n M (Iic 0))
    (Q : ℝ) (hQ : 0 < Q) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (s : ℝ) :
    (F.ancientRescaleAt Q hQ t₀ ht₀).metric s =
      rescaledMetric (F.metric (t₀ + s / Q)) Q hQ := rfl

theorem ancientRescaleAt_scalarCurvature (F : RicciFlow n M (Iic 0))
    (Q : ℝ) (hQ : 0 < Q) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (s : ℝ) (x : M) :
    ((F.ancientRescaleAt Q hQ t₀ ht₀).connection s).scalarCurvature x =
      Q⁻¹ * (F.connection (t₀ + s / Q)).scalarCurvature x :=
  F.parabolicRescale_scalarCurvature Q hQ t₀ _ _ _ s x

theorem ancientRescaleAt_scalarCurvature_zero (F : RicciFlow n M (Iic 0))
    (Q : ℝ) (hQ : 0 < Q) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (x : M)
    (hx : (F.connection t₀).scalarCurvature x = Q) :
    ((F.ancientRescaleAt Q hQ t₀ ht₀).connection 0).scalarCurvature x = 1 := by
  rw [ancientRescaleAt_scalarCurvature, zero_div, add_zero, hx, inv_mul_cancel₀ hQ.ne']

theorem ancientRescaleAt_edist_toReal_zero (F : RicciFlow n M (Iic 0))
    (Q : ℝ) (hQ : 0 < Q) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p x : M) :
    (((F.ancientRescaleAt Q hQ t₀ ht₀).metric 0).edist p x).toReal =
      Real.sqrt Q * ((F.metric t₀).edist p x).toReal := by
  rw [ancientRescaleAt_metric, zero_div, add_zero, rescaledMetric_edist,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg Q)]

theorem ancientRescaleAt_scalarCurvature_mul_sq_edist_zero
    (F : RicciFlow n M (Iic 0))
    (Q : ℝ) (hQ : 0 < Q) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p x : M) :
    ((F.ancientRescaleAt Q hQ t₀ ht₀).connection 0).scalarCurvature x *
      (((F.ancientRescaleAt Q hQ t₀ ht₀).metric 0).edist p x).toReal ^ 2 =
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 := by
  rw [ancientRescaleAt_scalarCurvature, ancientRescaleAt_edist_toReal_zero,
    zero_div, add_zero, mul_pow, Real.sq_sqrt hQ.le]
  field_simp

variable [T3Space M] [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]

theorem ancientRescaleAt_scalarCurvature_le_of_quadratic_decay
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (Q : ℝ) (hQ : 0 < Q) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M)
    {A L b : ℝ} (hb : 0 < b)
    (hdecay : ∀ x, L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ A)
    (hscale : Real.sqrt Q * L ≤ b) :
    ∀ s ≤ 0, ∀ x,
      b ≤ (((F.ancientRescaleAt Q hQ t₀ ht₀).metric 0).edist p x).toReal →
      ((F.ancientRescaleAt Q hQ t₀ ht₀).connection s).scalarCurvature x ≤ A / b ^ 2 := by
  let G := F.ancientRescaleAt Q hQ t₀ ht₀
  intro s hs x hx
  have hdist := F.ancientRescaleAt_edist_toReal_zero Q hQ t₀ ht₀ p x
  have hout : L ≤ ((F.metric t₀).edist p x).toReal := by
    apply (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr hQ)).mp
    exact hscale.trans (hx.trans_eq hdist)
  have hnonneg : 0 ≤ (G.connection 0).scalarCurvature x := by
    rw [ancientRescaleAt_scalarCurvature, zero_div, add_zero]
    exact mul_nonneg (inv_nonneg.mpr hQ.le)
      (((F.connection t₀).curvatureOperatorBound_scalarCurvature
        (hC.tensor_calculus n M (F.metric t₀) (F.connection t₀)) x (hoperator t₀ ht₀ x)).1)
  have hterminal : (G.connection 0).scalarCurvature x ≤ A / b ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hb)).mpr
    calc
      _ ≤ (G.connection 0).scalarCurvature x * ((G.metric 0).edist p x).toReal ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb.le hx 2) hnonneg
      _ = (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 :=
        F.ancientRescaleAt_scalarCurvature_mul_sq_edist_zero Q hQ t₀ ht₀ p x
      _ ≤ A := hdecay x hout
  have ht : t₀ + s / Q ≤ t₀ :=
    add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs hQ.le)
  have hmono := F.scalarCurvature_monotoneOn_of_bounded_ancient hC hcomplete hoperator
    hK hbound x (ht.trans ht₀) ht₀ ht
  have hmonoG : (G.connection s).scalarCurvature x ≤ (G.connection 0).scalarCurvature x := by
    change ((F.ancientRescaleAt Q hQ t₀ ht₀).connection s).scalarCurvature x ≤
      ((F.ancientRescaleAt Q hQ t₀ ht₀).connection 0).scalarCurvature x
    rw [ancientRescaleAt_scalarCurvature, ancientRescaleAt_scalarCurvature,
      zero_div, add_zero]
    exact mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hQ.le)
  exact hmonoG.trans hterminal

theorem ancientRescaleAt_curvatureTensorNorm_le_of_quadratic_decay
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (Q : ℝ) (hQ : 0 < Q) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M)
    {A L b : ℝ} (hb : 0 < b)
    (hdecay : ∀ x, L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ A)
    (hscale : Real.sqrt Q * L ≤ b) :
    ∀ s ≤ 0, ∀ x,
      b ≤ (((F.ancientRescaleAt Q hQ t₀ ht₀).metric 0).edist p x).toReal →
      ((F.ancientRescaleAt Q hQ t₀ ht₀).connection s).curvatureTensorNorm x ≤
        (n : ℝ) ^ 2 * (A / b ^ 2) := by
  let G := F.ancientRescaleAt Q hQ t₀ ht₀
  intro s hs x hx
  have ht : t₀ + s / Q ≤ 0 :=
    (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs hQ.le)).trans ht₀
  have hpos : (G.connection s).NonnegativeCurvatureOperator x :=
    F.parabolicRescale_nonnegativeCurvatureOperator Q hQ t₀ _ _ _ s x (hoperator _ ht x)
  apply ((G.connection s).curvatureTensorNorm_le_scalarCurvature
    (hC.tensor_calculus n M (G.metric s) (G.connection s)) x hpos).trans
  exact mul_le_mul_of_nonneg_left
    (F.ancientRescaleAt_scalarCurvature_le_of_quadratic_decay hC hcomplete hoperator
      hK hbound Q hQ t₀ ht₀ p hb hdecay hscale s hs x hx) (sq_nonneg _)

omit [T3Space M] [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M] in

theorem scalarCurvature_tendsto_zero_of_finite_ratio
    (F : RicciFlow n M (Iic 0)) (t₀ : ℝ) (p : M) (q : ℕ → M)
    (hd : Tendsto (fun i => ((F.metric t₀).edist p (q i)).toReal) atTop atTop)
    {A : ℝ} (hratio : Tendsto (fun i => (F.connection t₀).scalarCurvature (q i) *
      ((F.metric t₀).edist p (q i)).toReal ^ 2) atTop (𝓝 A)) :
    Tendsto (fun i => (F.connection t₀).scalarCurvature (q i)) atTop (𝓝 0) := by
  have h := hratio.div_atTop ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hd)
  apply h.congr'
  filter_upwards [hd.eventually_gt_atTop 0] with i hi
  exact mul_div_cancel_right₀ _ (pow_ne_zero 2 hi.ne')

omit [T3Space M] [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M] in

theorem ancientRescaleAt_basepoint_edist_tendsto_of_finite_ratio
    (F : RicciFlow n M (Iic 0)) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M) (q : ℕ → M)
    (hQ : ∀ i, 0 < (F.connection t₀).scalarCurvature (q i))
    {A : ℝ} (hratio : Tendsto (fun i => (F.connection t₀).scalarCurvature (q i) *
      ((F.metric t₀).edist p (q i)).toReal ^ 2) atTop (𝓝 A)) :
    Tendsto (fun i => (((F.ancientRescaleAt
      ((F.connection t₀).scalarCurvature (q i)) (hQ i) t₀ ht₀).metric 0).edist p (q i)).toReal)
      atTop (𝓝 (Real.sqrt A)) := by
  convert (Real.continuous_sqrt.continuousAt.tendsto.comp hratio) using 1
  funext i
  rw [Function.comp_apply, ancientRescaleAt_edist_toReal_zero, Real.sqrt_mul (hQ i).le,
    Real.sqrt_sq ENNReal.toReal_nonneg]

theorem eventually_ancientRescaleAt_annular_curvature_control
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M) (q : ℕ → M)
    (hQ : ∀ i, 0 < (F.connection t₀).scalarCurvature (q i))
    (hd : Tendsto (fun i => ((F.metric t₀).edist p (q i)).toReal) atTop atTop)
    {A C L b : ℝ} (hb : 0 < b)
    (hratio : Tendsto (fun i => (F.connection t₀).scalarCurvature (q i) *
      ((F.metric t₀).edist p (q i)).toReal ^ 2) atTop (𝓝 A))
    (hdecay : ∀ x, L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C) :
    ∀ᶠ i in atTop, ∀ s ≤ 0, ∀ x,
      b ≤ (((F.ancientRescaleAt ((F.connection t₀).scalarCurvature (q i))
        (hQ i) t₀ ht₀).metric 0).edist p x).toReal →
      ((F.ancientRescaleAt ((F.connection t₀).scalarCurvature (q i))
        (hQ i) t₀ ht₀).connection s).curvatureTensorNorm x ≤ (n : ℝ) ^ 2 * (C / b ^ 2) := by
  have hzero := F.scalarCurvature_tendsto_zero_of_finite_ratio t₀ p q hd hratio
  have hsmall : Tendsto (fun i => Real.sqrt ((F.connection t₀).scalarCurvature (q i)) * L)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero, zero_mul] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hzero).mul_const L
  filter_upwards [hsmall.eventually_lt_const hb] with i hi
  exact F.ancientRescaleAt_curvatureTensorNorm_le_of_quadratic_decay hC hcomplete hoperator
    hK hbound _ (hQ i) t₀ ht₀ p hb hdecay hi.le

theorem ancientRescaleAt_volume_lower_bound_of_quadratic_decay
    [MeasurableSpace M] [BorelSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ}
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (Q : ℝ) (hQ : 0 < Q) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p q : M)
    {A L b r : ℝ} (hb : 0 < b) (hr : 0 < r)
    (hdecay : ∀ x, L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ A)
    (hscale : Real.sqrt Q * L ≤ b)
    (hmargin : b + r ≤ (((F.ancientRescaleAt Q hQ t₀ ht₀).metric 0).edist p q).toReal)
    (hrcurv : (n : ℝ) ^ 2 * (A / b ^ 2) ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (κ * r ^ n) ≤
      ((F.ancientRescaleAt Q hQ t₀ ht₀).metric 0).volumeMeasure
        (((F.ancientRescaleAt Q hQ t₀ ht₀).metric 0).ball q r) := by
  let G := F.ancientRescaleAt Q hQ t₀ ht₀
  have hsq : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hball : (G.metric 0).ball q r = (F.metric t₀).ball q (r / Real.sqrt Q) := by
    rw [ancientRescaleAt_metric, zero_div, add_zero, rescaledMetric_ball_allDimensions]
  have hscalar : ∀ x ∈ (F.metric t₀).ball q (r / Real.sqrt Q),
      (F.connection t₀).scalarCurvature x ≤ Q * (A / b ^ 2) := by
    intro x hx
    have hx' : x ∈ (G.metric 0).ball q r := hball.symm ▸ hx
    have houter := (G.metric 0).radial_lower_bound_on_ball p q hmargin x hx'
    have h := F.ancientRescaleAt_scalarCurvature_le_of_quadratic_decay hC hcomplete
      hoperator hK hbound Q hQ t₀ ht₀ p hb hdecay hscale 0 le_rfl x houter.le
    rw [ancientRescaleAt_scalarCurvature, zero_div, add_zero] at h
    have hmul := mul_le_mul_of_nonneg_left h hQ.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul] using hmul
  have hscale' : (n : ℝ) ^ 2 * (Q * (A / b ^ 2)) ≤ (r / Real.sqrt Q)⁻¹ ^ 2 := by
    calc
      _ = Q * ((n : ℝ) ^ 2 * (A / b ^ 2)) := by ring
      _ ≤ Q * r⁻¹ ^ 2 := mul_le_mul_of_nonneg_left hrcurv hQ.le
      _ = _ := by rw [inv_div, div_pow, Real.sq_sqrt hQ.le, div_eq_mul_inv, inv_pow]
  have hvolume := F.ball_volume_lower_bound_of_bounded_ancient_terminal_scalar
    hC hcomplete hoperator hK hbound hnoncollapse ht₀ q (div_pos hr hsq) hscalar hscale'
  change ENNReal.ofReal (κ * r ^ n) ≤ (rescaledMetric (F.metric (t₀ + 0 / Q)) Q hQ).volumeMeasure
    ((rescaledMetric (F.metric (t₀ + 0 / Q)) Q hQ).ball q r)
  rw [rescaledMetric_volumeMeasure, rescaledMetric_ball_allDimensions, zero_div, add_zero]
  simp only [MeasureTheory.Measure.smul_apply, smul_eq_mul]
  have h := mul_le_mul' (le_refl (ENNReal.ofReal (Real.sqrt Q) ^ n)) hvolume
  have hid : ENNReal.ofReal (Real.sqrt Q) ^ n *
      ENNReal.ofReal (κ * (r / Real.sqrt Q) ^ n) = ENNReal.ofReal (κ * r ^ n) := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg Q),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg Q) n)]
    congr 1
    calc
      Real.sqrt Q ^ n * (κ * (r / Real.sqrt Q) ^ n) =
          κ * (Real.sqrt Q * (r / Real.sqrt Q)) ^ n := by rw [mul_pow]; ring
      _ = κ * r ^ n := by rw [mul_div_cancel₀ _ hsq.ne']
  rwa [hid] at h

theorem ancientRescaleAt_uniform_exponential_chart_of_quadratic_decay
    [MeasurableSpace M] [BorelSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (hn : 1 ≤ n) (Q : ℝ) (hQ : 0 < Q) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p q : M)
    {A L b r : ℝ} (hA : 0 ≤ A) (hb : 0 < b) (hr : 0 < r)
    (hdecay : ∀ x, L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ A)
    (hscale : Real.sqrt Q * L ≤ b)
    (hmargin : b + 2 * r ≤ (((F.ancientRescaleAt Q hQ t₀ ht₀).metric 0).edist p q).toReal)
    (hrcurv : (n : ℝ) ^ 2 * (A / b ^ 2) ≤ r⁻¹ ^ 2) :
    let g := (F.ancientRescaleAt Q hQ t₀ ht₀).metric 0
    let ρ := RiemannianMetric.localInjectivityRadius n ((n : ℝ) ^ 2 * (A / b ^ 2)) r (κ * r ^ n)
    0 < ρ ∧ ρ < r ∧
      ∃ L₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
        Φ.source = Metric.ball 0 ρ ∧ Φ.target = g.ball q ρ ∧ Φ 0 = q ∧
        (∀ a b, g.pullbackCoefficients (extChartAt (𝓡 n) q).symm
          (extChartAt (𝓡 n) q q) (L₀ a) (L₀ b) = inner ℝ a b) ∧
        HasFDerivAt (fun w => extChartAt (𝓡 n) q (Φ w)) L₀.toContinuousLinearMap 0 ∧
        (∀ w ∈ Metric.ball 0 r,
          g.IsGeodesicOn (fun t => Φ (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 r}) ∧
        ∀ w ∈ Metric.ball 0 ρ, g.edist q (Φ w) = ENNReal.ofReal ‖w‖ := by
  let G := F.ancientRescaleAt Q hQ t₀ ht₀
  have hcompleteG : MetricComplete (G.metric 0) := by
    rw [ancientRescaleAt_metric, zero_div, add_zero]
    exact metricComplete_rescaledMetric _ Q hQ (hcomplete t₀ ht₀)
  have hcompact : IsCompact (closure ((G.metric 0).ball q (2 * r))) := by
    let := (G.metric 0).toMetricSpace
    let : ProperSpace M := (G.metric 0).properSpace_toMetricSpace hcompleteG
    rw [← (G.metric 0).toMetricSpace_ball]
    exact (isCompact_closedBall q (2 * r)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  have hcurv : ∀ x ∈ (G.metric 0).ball q (2 * r),
      (G.connection 0).curvatureTensorNorm x ≤ (n : ℝ) ^ 2 * (A / b ^ 2) := by
    intro x hx
    exact F.ancientRescaleAt_curvatureTensorNorm_le_of_quadratic_decay hC hcomplete
      hoperator hK hbound Q hQ t₀ ht₀ p hb hdecay hscale 0 le_rfl x
      ((G.metric 0).radial_lower_bound_on_ball p q hmargin x hx).le
  have hmargin' : b + r ≤ ((G.metric 0).edist p q).toReal := by
    change b + 2 * r ≤ ((G.metric 0).edist p q).toReal at hmargin
    linarith
  have hvolume := F.ancientRescaleAt_volume_lower_bound_of_quadratic_decay hC hcomplete
    hoperator hK hbound hnoncollapse Q hQ t₀ ht₀ p q hb hr hdecay hscale hmargin' hrcurv
  exact (G.metric 0).exists_uniform_precompact_exponential_diffeomorph
    (G.connection 0) q hn (mul_nonneg (sq_nonneg _) (div_nonneg hA (sq_nonneg _)))
    hr (mul_pos hκ (pow_pos hr n)) hcompact hcurv hvolume

theorem eventually_ancientRescaleAt_uniform_exponential_charts
    [MeasurableSpace M] [BorelSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (hn : 1 ≤ n) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M) (q : ℕ → M)
    (hQ : ∀ i, 0 < (F.connection t₀).scalarCurvature (q i))
    (hd : Tendsto (fun i => ((F.metric t₀).edist p (q i)).toReal) atTop atTop)
    {A C L b r : ℝ} (hCnonneg : 0 ≤ C) (hb : 0 < b) (hr : 0 < r)
    (hratio : Tendsto (fun i => (F.connection t₀).scalarCurvature (q i) *
      ((F.metric t₀).edist p (q i)).toReal ^ 2) atTop (𝓝 A))
    (hdecay : ∀ x, L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C)
    (hmargin : b + 2 * r < Real.sqrt A)
    (hrcurv : (n : ℝ) ^ 2 * (C / b ^ 2) ≤ r⁻¹ ^ 2) :
    let ρ := RiemannianMetric.localInjectivityRadius n ((n : ℝ) ^ 2 * (C / b ^ 2)) r (κ * r ^ n)
    0 < ρ ∧ ρ < r ∧ ∀ᶠ i in atTop,
      let g := (F.ancientRescaleAt ((F.connection t₀).scalarCurvature (q i)) (hQ i) t₀ ht₀).metric 0
      ∃ L₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
        Φ.source = Metric.ball 0 ρ ∧ Φ.target = g.ball (q i) ρ ∧ Φ 0 = q i ∧
        (∀ a b, g.pullbackCoefficients (extChartAt (𝓡 n) (q i)).symm
          (extChartAt (𝓡 n) (q i) (q i)) (L₀ a) (L₀ b) = inner ℝ a b) ∧
        HasFDerivAt (fun w => extChartAt (𝓡 n) (q i) (Φ w)) L₀.toContinuousLinearMap 0 ∧
        (∀ w ∈ Metric.ball 0 r,
          g.IsGeodesicOn (fun t => Φ (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 r}) ∧
        ∀ w ∈ Metric.ball 0 ρ, g.edist (q i) (Φ w) = ENNReal.ofReal ‖w‖ := by
  refine ⟨RiemannianMetric.localInjectivityRadius_pos _ _ hr _,
    RiemannianMetric.localInjectivityRadius_lt _ _ hr _, ?_⟩
  have hzero := F.scalarCurvature_tendsto_zero_of_finite_ratio t₀ p q hd hratio
  have hsmall : Tendsto (fun i => Real.sqrt ((F.connection t₀).scalarCurvature (q i)) * L)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero, zero_mul] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hzero).mul_const L
  have hdist := F.ancientRescaleAt_basepoint_edist_tendsto_of_finite_ratio t₀ ht₀ p q hQ hratio
  filter_upwards [hsmall.eventually_lt_const hb, hdist.eventually_const_lt hmargin]
    with i hscale hcenter
  exact (F.ancientRescaleAt_uniform_exponential_chart_of_quadratic_decay hC hcomplete
    hoperator hK hbound hκ hnoncollapse hn _ (hQ i) t₀ ht₀ p (q i)
    hCnonneg hb hr hdecay hscale.le hcenter.le hrcurv).2.2

end PoincareConjecture.RicciFlow
