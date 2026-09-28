import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Polar.Dilation









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter TopologicalSpace PoincareConjecture
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric



theorem tangentNorm_deriv_zero_of_edist_affine_segment
    {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {γ : ℝ → EuclideanSpace ℝ (Fin n)} {ε c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c)
    (hmetric : ∀ s ∈ Ioo (-ε) ε, ∀ t ∈ Ioo (-ε) ε,
      g.edist (γ s) (γ t) = ENNReal.ofReal (c * |s - t|)) :
    g.tangentNorm (γ 0) (deriv γ 0) = c := by
  let δ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let η := fun t => γ (δ * t)
  have htime (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) : δ * t ∈ Ioo (-ε) ε := by
    dsimp [δ]
    constructor <;> nlinarith [ht.1, ht.2]
  have hηmetric (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 2)
      (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) :
      g.edist (η s) (η t) = ENNReal.ofReal ((δ * c) * |s - t|) := by
    rw [hmetric _ (htime s hs) _ (htime t ht)]
    congr 1
    rw [← mul_sub, abs_mul, abs_of_pos hδ]
    ring
  have hgeo : g.IsGeodesicOn η (Ioo (-1 : ℝ) (1 + 1)) := by
    norm_num
    exact (g.isGeodesicOn_and_contMDiffOn_of_edist_affine_segment
      (mul_nonneg hδ.le hc) hηmetric).1
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hsmooth := (g.isGeodesicOn_and_contMDiffOn_of_edist_affine_segment hc hmetric).2
  have hdiff : DifferentiableAt ℝ γ 0 :=
    (contMDiffAt_iff_contDiffAt.mp (hsmooth.contMDiffAt (isOpen_Ioo.mem_nhds hzero))).differentiableAt
      (by simp)
  have hderiv : HasDerivAt η (δ • deriv γ 0) 0 := by
    have hd : HasDerivAt γ (deriv γ 0) (δ * 0) := by simpa only [mul_zero] using hdiff.hasDerivAt
    convert! hd.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul δ) using 1
    simp only [mul_one]
  have hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (η s) (η t) = ENNReal.ofReal |s - t| * g.edist (η 0) (η 1) := by
    intro s hs t ht
    rw [hηmetric _ ⟨by linarith [hs.1], by linarith [hs.2]⟩
      _ ⟨by linarith [ht.1], by linarith [ht.2]⟩,
      hηmetric 0 (by norm_num) 1 (by norm_num)]
    norm_num only [zero_sub, abs_neg, abs_one, mul_one]
    rw [← ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
  have hdchart : HasDerivAt (fun t => extChartAt (𝓡 n) (η 0) (η t))
      (δ • deriv γ 0) 0 := by simpa using hderiv
  have hs := hgeo.initial_tangentNorm_eq_of_edist_segment zero_lt_one rfl hdchart hmin
  rw [hηmetric 0 (by norm_num) 1 (by norm_num)] at hs
  have hs' := congrArg ENNReal.toReal hs
  norm_num only [zero_sub, abs_neg, abs_one, mul_one] at hs'
  rw [ENNReal.toReal_ofReal (show 0 ≤ g.tangentNorm (η 0) (δ • deriv γ 0) from Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (mul_nonneg hδ.le hc)] at hs'
  have hnorm : g.tangentNorm (η 0) (δ • deriv γ 0) =
      δ * g.tangentNorm (γ 0) (deriv γ 0) := by
    change g.tangentNorm (γ (δ * 0)) (δ • deriv γ 0) = _
    simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ.le]
    erw [mul_zero]
  rw [hnorm] at hs'
  exact mul_left_cancel₀ hδ.ne' hs'

end PoincareConjecture.RiemannianMetric

namespace Poincare.AncientVolume.ScalarRatio.UnitSliceRadialChartData

variable {X : Type*} [MetricSpace X] {p : X} {hcomparison : RayComparison p} {n : ℕ}


def radialOrbit (d : UnitSliceRadialChartData hcomparison n) (x : UnitSliceAmbient n)
    (t : ℝ) : UnitSliceAmbient n :=
  d.ambientChart.symm (asymptoticConeDilation hcomparison (Real.toNNReal (1 + t)) (d.ambientChart x))

theorem radialOrbit_zero (d : UnitSliceRadialChartData hcomparison n)
    {x : UnitSliceAmbient n} (hx : x ∈ d.ambientChart.source) : d.radialOrbit x 0 = x := by
  simp only [radialOrbit, add_zero, Real.toNNReal_one, asymptoticConeDilation_one]
  exact d.ambientChart.left_inv hx



theorem exists_radialOrbit_interval (d : UnitSliceRadialChartData hcomparison n)
    {x : UnitSliceAmbient n} (hx : x ∈ d.ambientChart.source) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧
      (∀ t ∈ Ioo (-ε) ε, d.radialOrbit x t ∈ d.ambientChart.source) ∧
      d.metric.IsGeodesicOn (d.radialOrbit x) (Ioo (-ε) ε) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 (n + 1)) ∞ (d.radialOrbit x) (Ioo (-ε) ε) ∧
      (∀ t ∈ Ioo (-ε) ε, d.potential (d.radialOrbit x t) = (1 + t) ^ 2 * d.potential x) ∧
      (∀ s ∈ Ioo (-ε) ε, ∀ t ∈ Ioo (-ε) ε,
        d.metric.edist (d.radialOrbit x s) (d.radialOrbit x t) =
          ENNReal.ofReal ((asymptoticConeRadius hcomparison (d.ambientChart x) : ℝ) * |s - t|)) := by
  have hcont : Continuous (fun t : ℝ =>
      asymptoticConeDilation hcomparison (Real.toNNReal (1 + t)) (d.ambientChart x)) :=
    (continuous_asymptoticConeDilation hcomparison).comp
      ((continuous_real_toNNReal.comp (continuous_const.add continuous_id)).prodMk continuous_const)
  have hnear : ∀ᶠ t : ℝ in 𝓝 0,
      asymptoticConeDilation hcomparison (Real.toNNReal (1 + t)) (d.ambientChart x) ∈
        d.ambientChart.target := by
    apply hcont.continuousAt.preimage_mem_nhds
    simpa only [add_zero, Real.toNNReal_one, asymptoticConeDilation_one] using
      d.ambientChart.open_target.mem_nhds (d.ambientChart.map_source hx)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  let ε := min δ (1 / 2)
  have hε : 0 < ε := lt_min hδ (by norm_num)
  have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
  have htarget (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      asymptoticConeDilation hcomparison (Real.toNNReal (1 + t)) (d.ambientChart x) ∈
        d.ambientChart.target := by
    apply hδsub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    have hεδ : ε ≤ δ := min_le_left _ _
    constructor <;> linarith [ht.1, ht.2]
  have hpos (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : 0 ≤ 1 + t := by linarith [ht.1]
  have hsource (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : d.radialOrbit x t ∈ d.ambientChart.source :=
    d.ambientChart.map_target (htarget t ht)
  have hvalue (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      d.ambientChart (d.radialOrbit x t) =
        asymptoticConeDilation hcomparison (Real.toNNReal (1 + t)) (d.ambientChart x) :=
    d.ambientChart.right_inv (htarget t ht)
  have hmetric (s : ℝ) (hs : s ∈ Ioo (-ε) ε) (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      d.metric.edist (d.radialOrbit x s) (d.radialOrbit x t) =
        ENNReal.ofReal ((asymptoticConeRadius hcomparison (d.ambientChart x) : ℝ) * |s - t|) := by
    rw [← ENNReal.ofReal_toReal (d.metric.edist_ne_top _ _),
      ← d.distance _ (hsource s hs) _ (hsource t ht), hvalue s hs, hvalue t ht,
      dist_asymptoticConeDilation_same_point, Real.coe_toNNReal _ (hpos s hs),
      Real.coe_toNNReal _ (hpos t ht), add_sub_add_left_eq_sub, mul_comm]
  obtain ⟨hgeo, hsmooth⟩ := d.metric.isGeodesicOn_and_contMDiffOn_of_edist_affine_segment
    (asymptoticConeRadius hcomparison (d.ambientChart x)).coe_nonneg hmetric
  refine ⟨ε, hε, hεhalf, hsource, hgeo, hsmooth, ?_, hmetric⟩
  intro t ht
  rw [← d.radial _ (hsource t ht), hvalue t ht, asymptoticConeRadius_dilation,
    NNReal.coe_mul, Real.coe_toNNReal _ (hpos t ht), mul_pow, ← d.radial x hx]
  ring




theorem hasDerivAt_radialOrbit_zero (d : UnitSliceRadialChartData hcomparison n)
    {x : UnitSliceAmbient n} (hx : x ∈ d.ambientChart.source) :
    HasDerivAt (d.radialOrbit x) (d.connection.gradient d.potential x) 0 := by
  obtain ⟨ε, hε, _, _, _, hsmooth, hpotential, hmetric⟩ := d.exists_radialOrbit_interval hx
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hdiff : DifferentiableAt ℝ (d.radialOrbit x) 0 :=
    (contMDiffAt_iff_contDiffAt.mp (hsmooth.contMDiffAt (isOpen_Ioo.mem_nhds hzero))).differentiableAt
      (by simp)
  let v := deriv (d.radialOrbit x) 0
  have hspeed : d.metric.tangentNorm x v =
      (asymptoticConeRadius hcomparison (d.ambientChart x) : ℝ) := by
    have hh := d.metric.tangentNorm_deriv_zero_of_edist_affine_segment hε
      (asymptoticConeRadius hcomparison (d.ambientChart x)).coe_nonneg hmetric
    rw [d.radialOrbit_zero hx] at hh
    exact hh
  have hself : d.metric.inner x v v = 2 * d.potential x := by
    have hnonneg : 0 ≤ d.metric.inner x v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (d.metric.pos x v hv).le
    have hh := congrArg (fun a : ℝ => a ^ 2) hspeed
    rw [RiemannianMetric.tangentNorm, Real.sq_sqrt hnonneg] at hh
    have hr := d.radial x hx
    linarith
  have heq : (fun t => d.potential (d.radialOrbit x t)) =ᶠ[𝓝 0]
      fun t => (1 + t) ^ 2 * d.potential x := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with t ht
    exact hpotential t ht
  have hquadratic : HasDerivAt (fun t : ℝ => (1 + t) ^ 2 * d.potential x)
      (2 * d.potential x) 0 := by
    convert! ((((hasDerivAt_id (0 : ℝ)).const_add 1).pow 2).mul_const (d.potential x)) using 1
    norm_num
  have hderiv : HasDerivAt (fun t => d.potential (d.radialOrbit x t))
      (2 * d.potential x) 0 := hquadratic.congr_of_eventuallyEq heq
  have hf : HasFDerivAt d.potential (fderiv ℝ d.potential x) (d.radialOrbit x 0) := by
    rw [d.radialOrbit_zero hx]
    exact ((contMDiffAt_iff_contDiffAt.mp (d.smooth x)).differentiableAt (by simp)).hasFDerivAt
  have hcross : d.metric.inner x (d.connection.gradient d.potential x) v = 2 * d.potential x := by
    rw [d.connection.inner_gradient]
    simp only [mvfderiv, mfderiv_eq_fderiv]
    exact (hf.comp_hasDerivAt 0 hdiff.hasDerivAt).unique hderiv
  have hgrad : d.metric.inner x (d.connection.gradient d.potential x)
      (d.connection.gradient d.potential x) = 2 * d.potential x := d.eikonal x hx
  have hv : v = d.connection.gradient d.potential x := by
    change TangentSpace (𝓡 (n + 1)) x at v
    by_contra hne
    have hpos := d.metric.pos x (v - d.connection.gradient d.potential x) (sub_ne_zero.mpr hne)
    simp only [map_sub, sub_apply] at hpos
    rw [d.metric.symm x v (d.connection.gradient d.potential x), hcross, hself, hgrad] at hpos
    linarith
  rw [← hv]
  exact hdiff.hasDerivAt

end Poincare.AncientVolume.ScalarRatio.UnitSliceRadialChartData
