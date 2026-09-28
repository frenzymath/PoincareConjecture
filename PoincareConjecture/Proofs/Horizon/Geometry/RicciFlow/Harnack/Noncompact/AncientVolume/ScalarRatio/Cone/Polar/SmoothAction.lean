import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Polar.Orbits
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter TopologicalSpace PoincareConjecture
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace Poincare.AncientVolume.ScalarRatio.UnitSliceRadialChartData

variable {X : Type*} [MetricSpace X] {p : X} {hcomparison : RayComparison p} {n : ℕ}

theorem exists_uniform_radialOrbit_interval (d : UnitSliceRadialChartData hcomparison n)
    {x : UnitSliceAmbient n} (hx : x ∈ d.ambientChart.source) :
    ∃ (ε : ℝ) (U : Set (UnitSliceAmbient n)), 0 < ε ∧ ε ≤ 1 / 2 ∧
      IsOpen U ∧ x ∈ U ∧ U ⊆ d.ambientChart.source ∧
      ∀ y ∈ U, d.metric.IsGeodesicOn (d.radialOrbit y) (Ioo (-ε) ε) := by
  have hcont : ContinuousAt (fun z : ℝ × UnitSliceAmbient n =>
      asymptoticConeDilation hcomparison (Real.toNNReal (1 + z.1)) (d.ambientChart z.2)) (0, x) :=
    (continuous_asymptoticConeDilation hcomparison).continuousAt.comp
      ((continuous_real_toNNReal.continuousAt.comp (continuousAt_const.add continuousAt_fst)).prodMk
        ((d.ambientChart.continuousOn.continuousAt (d.ambientChart.open_source.mem_nhds hx)).comp
          continuousAt_snd))
  have hnear : {z : ℝ × UnitSliceAmbient n | z.2 ∈ d.ambientChart.source ∧
      asymptoticConeDilation hcomparison (Real.toNNReal (1 + z.1)) (d.ambientChart z.2) ∈
        d.ambientChart.target} ∈ 𝓝 (0, x) := by
    have htarget := hcont.preimage_mem_nhds (d.ambientChart.open_target.mem_nhds
      (show asymptoticConeDilation hcomparison (Real.toNNReal (1 + (0 : ℝ))) (d.ambientChart x) ∈
          d.ambientChart.target by
        simpa only [add_zero, Real.toNNReal_one, asymptoticConeDilation_one] using d.ambientChart.map_source hx))
    exact inter_mem (continuous_snd.continuousAt.preimage_mem_nhds
      (d.ambientChart.open_source.mem_nhds hx)) htarget
  obtain ⟨T, U, hT, h0T, hU, hxU, hsub⟩ := mem_nhds_prod_iff'.mp hnear
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds h0T)
  let ε := min δ (1 / 2)
  have hε : 0 < ε := lt_min hδ (by norm_num)
  have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
  have htime (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : t ∈ T := by
    apply hδsub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    have hεδ : ε ≤ δ := min_le_left _ _
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨ε, U, hε, hεhalf, hU, hxU, (fun y hy => (hsub (show (0, y) ∈ T ×ˢ U from ⟨h0T, hy⟩)).1), ?_⟩
  intro y hy
  have htarget (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      asymptoticConeDilation hcomparison (Real.toNNReal (1 + t)) (d.ambientChart y) ∈
        d.ambientChart.target := (hsub (show (t, y) ∈ T ×ˢ U from ⟨htime t ht, hy⟩)).2
  have hpos (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : 0 ≤ 1 + t := by linarith [ht.1]
  apply (d.metric.isGeodesicOn_and_contMDiffOn_of_edist_affine_segment
    (asymptoticConeRadius hcomparison (d.ambientChart y)).coe_nonneg ?_).1
  intro s hs t ht
  simp only [radialOrbit]
  rw [← ENNReal.ofReal_toReal (d.metric.edist_ne_top _ _),
    ← d.distance _ (d.ambientChart.map_target (htarget s hs))
      _ (d.ambientChart.map_target (htarget t ht))]
  rw [d.ambientChart.right_inv (htarget s hs), d.ambientChart.right_inv (htarget t ht),
    dist_asymptoticConeDilation_same_point, Real.coe_toNNReal _ (hpos s hs),
    Real.coe_toNNReal _ (hpos t ht), add_sub_add_left_eq_sub, mul_comm]

theorem contDiffAt_radialOrbit_joint_zero (d : UnitSliceRadialChartData hcomparison n)
    {x : UnitSliceAmbient n} (hx : x ∈ d.ambientChart.source) :
    ContDiffAt ℝ ∞ (fun z : ℝ × UnitSliceAmbient n => d.radialOrbit z.2 z.1) (0, x) := by
  obtain ⟨ε, U, hε, _, hU, hxU, hUsub, hgeo⟩ := d.exists_uniform_radialOrbit_interval hx
  let Γ : (ℝ × UnitSliceAmbient n) → ℝ → UnitSliceAmbient n :=
    fun z s => d.radialOrbit z.2 (z.1 * s)
  have hnear : ∀ᶠ z : ℝ × UnitSliceAmbient n in 𝓝 (0, x),
      |z.1| < ε / 3 ∧ z.2 ∈ U := by
    apply inter_mem
    · have hh : {t : ℝ | |t| < ε / 3} ∈ 𝓝 (0 : ℝ) := by
        simpa only [Metric.ball, Real.dist_eq, sub_zero] using
          Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < ε / 3)
      exact (continuous_fst.continuousAt : ContinuousAt (Prod.fst : ℝ × UnitSliceAmbient n → ℝ)
        (0, x)).preimage_mem_nhds hh
    · exact continuous_snd.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)
  have hΓ : ∀ᶠ z in 𝓝 (0, x), d.metric.IsGeodesicOn (Γ z) (Ioo (-1 : ℝ) 2) := by
    filter_upwards [hnear] with z hz
    intro s hs
    apply (hgeo z.2 hz.2).comp_mul z.1 s
    have habs : |s| < 2 := abs_lt.mpr ⟨by linarith [hs.1], hs.2⟩
    have hprod : |z.1 * s| < ε := by
      rw [abs_mul]
      rcases eq_or_lt_of_le (abs_nonneg z.1) with hz0 | hzpos
      · rw [← hz0, zero_mul]
        exact hε
      · nlinarith [mul_lt_mul_of_pos_left habs hzpos, hz.1]
    exact abs_lt.mp hprod
  have hzero : (fun z => Γ z 0) =ᶠ[𝓝 (0, x)] fun z => z.2 := by
    filter_upwards [hnear] with z hz
    dsimp only [Γ]
    rw [mul_zero, d.radialOrbit_zero (hUsub hz.2)]
  have hvel : (fun z => deriv (Γ z) 0) =ᶠ[𝓝 (0, x)]
      fun z => z.1 • d.connection.gradient d.potential z.2 := by
    filter_upwards [hnear] with z hz
    have hd : HasDerivAt (d.radialOrbit z.2) (d.connection.gradient d.potential z.2)
        (z.1 * 0) := by
      simpa only [mul_zero] using d.hasDerivAt_radialOrbit_zero (hUsub hz.2)
    have hh := hd.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul z.1)
    simpa +instances only [Γ, Function.comp_def, mul_one] using hh.deriv
  have hgrad : ContDiffAt ℝ ∞ (fun y : UnitSliceAmbient n => d.connection.gradient d.potential y) x :=
    d.connection.contDiffAt_gradient_euclidean (contMDiffAt_iff_contDiffAt.mp (d.smooth x))
  have hpnt : ContMDiffAt 𝓘(ℝ, ℝ × UnitSliceAmbient n) (𝓡 (n + 1)) ∞ (fun z => Γ z 0) (0, x) :=
    contMDiffAt_iff_contDiffAt.mpr (contDiffAt_snd.congr_of_eventuallyEq hzero)
  have hv : ContDiffAt ℝ ∞ (fun z => deriv (fun s =>
      extChartAt (𝓡 (n + 1)) (Γ (0, x) 0) (Γ z s)) 0) (0, x) := by
    have hs : ContDiffAt ℝ ∞ (fun z : ℝ × UnitSliceAmbient n =>
        z.1 • d.connection.gradient d.potential z.2) (0, x) :=
      contDiffAt_fst.smul (hgrad.comp (0, x) contDiffAt_snd)
    simpa using hs.congr_of_eventuallyEq hvel
  have hend := d.metric.contMDiffAt_geodesic_endpoint hΓ (convex_Ioo _ _)
    (by norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 2)
    (by norm_num : (1 : ℝ) ∈ Ioo (-1 : ℝ) 2) hpnt hv
  simpa only [Γ, mul_one] using contMDiffAt_iff_contDiffAt.mp hend

theorem fderiv_radialOrbit_joint_zero (d : UnitSliceRadialChartData hcomparison n)
    {x : UnitSliceAmbient n} (hx : x ∈ d.ambientChart.source)
    (a : ℝ) (v : UnitSliceAmbient n) :
    let V : UnitSliceAmbient n := d.connection.gradient d.potential x
    fderiv ℝ (fun z : ℝ × UnitSliceAmbient n => d.radialOrbit z.2 z.1) (0, x) (a, v) =
      a • V + v := by
  dsimp only
  let O := fun z : ℝ × UnitSliceAmbient n => d.radialOrbit z.2 z.1
  let L := fderiv ℝ O (0, x)
  have hO : HasFDerivAt O L (0, x) :=
    ((d.contDiffAt_radialOrbit_joint_zero hx).differentiableAt (by simp)).hasFDerivAt
  have hfirst : L (1, 0) = d.connection.gradient d.potential x := by
    have hcurve : HasDerivAt (fun t : ℝ => (t, x)) (1, 0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 x)
    have hh : HasDerivAt (d.radialOrbit x) (L (1, 0)) 0 := by
      convert! hO.comp_hasDerivAt 0 hcurve using 1
    exact hh.unique (d.hasDerivAt_radialOrbit_zero hx)
  have hsecond : L (0, v) = v := by
    let J : UnitSliceAmbient n →L[ℝ] ℝ × UnitSliceAmbient n :=
      (0 : UnitSliceAmbient n →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ _)
    have hJ : HasFDerivAt (fun y : UnitSliceAmbient n => ((0 : ℝ), y)) J x :=
      (hasFDerivAt_const (0 : ℝ) x).prodMk (hasFDerivAt_id x)
    have hid : HasFDerivAt (fun y : UnitSliceAmbient n => d.radialOrbit y 0)
        (ContinuousLinearMap.id ℝ _) x := by
      apply (hasFDerivAt_id x).congr_of_eventuallyEq
      filter_upwards [d.ambientChart.open_source.mem_nhds hx] with y hy
      exact d.radialOrbit_zero hy
    have hh := (hO.comp x hJ).unique hid
    exact congrArg (fun A : UnitSliceAmbient n →L[ℝ] UnitSliceAmbient n => A v) hh
  have hsplit : (a, v) = a • ((1 : ℝ), (0 : UnitSliceAmbient n)) + (0, v) := by
    ext <;> simp
  change L (a, v) = _
  rw [hsplit, map_add, map_smul, hfirst, hsecond]

end Poincare.AncientVolume.ScalarRatio.UnitSliceRadialChartData
