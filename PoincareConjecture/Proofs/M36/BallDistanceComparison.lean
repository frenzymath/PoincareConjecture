import PoincareConjecture.Proofs.M36.MetricComparison
import PoincareConjecture.Proofs.M36.RetainedDifferential
import PoincareConjecture.Proofs.M36.MetricPullback
import PoincareConjecture.Proofs.M01.NormalizationScaling










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M36

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y]

theorem edist_le_edist_of_pullback_bound (g : RiemannianMetric 3 X)
    (h : RiemannianMetric 3 Y) {f : X → Y}
    (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (hmetric : ∀ x, ∀ v : TangentSpace (𝓡 3) x,
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤
        g.inner x v v) (x y : X) :
    h.edist (f x) (f y) ≤ g.edist x y := by
  by_contra hle
  have hlt := lt_of_not_ge hle
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨gamma, hx, hy, hgamma, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hlt
  have hbound := edist_comp_le_pathELength_of_pullback_bound g h (U := Set.univ)
    (fun z _ => hf z) (fun z _ => hmetric z) zero_le_one hgamma (Set.subset_univ _)
  rw [hx, hy] at hbound
  exact (not_lt_of_ge hbound) hlen

theorem surgeryBall_radial_distance_lower (g₀ : StandardInitialMetric)
    {L : ℝ} (hL : 0 < L) [Nonempty (SurgeryBall.{u} g₀ L)]
    (h : RiemannianMetric 3 (SurgeryBall.{u} g₀ L)) {c : ℝ} (hc : 0 < c)
    (hmetric : ∀ y, ∀ v : TangentSpace (𝓡 3) y,
      c * metricPullbackForm g₀.metric (surgeryBallInclusion g₀ L) y v v ≤ h.inner y v v)
    (y : SurgeryBall.{u} g₀ L) :
    ENNReal.ofReal (Real.sqrt c * radialArclength g₀ ‖surgeryBallInclusion g₀ L y‖) ≤
      h.edist (surgeryBallTip g₀ hL) y := by
  have hbound := edist_le_edist_of_pullback_bound h (m01RescaledMetric g₀.metric c hc)
    (surgeryBallInclusion_contMDiff g₀ L) hmetric (surgeryBallTip g₀ hL) y
  rw [surgeryBallInclusion_tip, m01RescaledMetric_edist, standard_edist_zero,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg c)] at hbound
  exact hbound

theorem surgeryBallChart_inclusion_mfderiv (g₀ : StandardInitialMetric)
    (L : ℝ) [Nonempty (SurgeryBall.{u} g₀ L)] {x : StandardCapSpace}
    (hx : x ∈ Metric.ball 0 (radialEuclideanRadius g₀ L)) (v : StandardCapSpace) :
    mfderiv (𝓡 3) (𝓡 3) (surgeryBallInclusion g₀ L) (surgeryBallChart g₀ L x)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryBallChart g₀ L) x v) = v := by
  have hc := ((surgeryBallChart_contMDiffOn g₀ L x hx).contMDiffAt
    (Metric.isOpen_ball.mem_nhds hx)).mdifferentiableAt (by simp)
  have hj := (surgeryBallInclusion_contMDiff g₀ L (surgeryBallChart g₀ L x)).mdifferentiableAt
    (by simp)
  have heq : surgeryBallInclusion g₀ L ∘ surgeryBallChart g₀ L =ᶠ[nhds x] id := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    exact surgeryBallChart_right_inverse g₀ L hz
  have hd := heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp x hj hc, mfderiv_id] at hd
  exact congrArg (fun D => D v) hd

theorem surgeryBall_radial_distance_upper (g₀ : StandardInitialMetric)
    {L : ℝ} (hL : 0 < L) [Nonempty (SurgeryBall.{u} g₀ L)]
    (h : RiemannianMetric 3 (SurgeryBall.{u} g₀ L)) {c : ℝ} (hc : 0 < c)
    (hmetric : ∀ y, ∀ v : TangentSpace (𝓡 3) y,
      h.inner y v v ≤ c * metricPullbackForm g₀.metric (surgeryBallInclusion g₀ L) y v v)
    (y : SurgeryBall.{u} g₀ L) :
    h.edist (surgeryBallTip g₀ hL) y ≤
      ENNReal.ofReal (Real.sqrt c * radialArclength g₀ ‖surgeryBallInclusion g₀ L y‖) := by
  let x := surgeryBallInclusion g₀ L y
  have hx : x ∈ Metric.ball 0 (radialEuclideanRadius g₀ L) := y.down.property
  by_cases hx0 : x = 0
  · have hy : y = surgeryBallTip g₀ hL :=
      (surgeryBallInclusion_isOpenEmbedding g₀ L).injective hx0
    rw [hy, metric_edist_self]
    exact bot_le
  let e : StandardCapSpace := ‖x‖⁻¹ • x
  have he : ‖e‖ = 1 := by simp [e, norm_smul, norm_ne_zero_iff.mpr hx0]
  let gamma : ℝ → StandardCapSpace := fun t => t • e
  have hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma :=
    (contDiff_id.smul contDiff_const).contMDiff
  have hstart : gamma 0 = 0 := zero_smul ℝ e
  have hend : gamma ‖x‖ = x := by simp [gamma, e, smul_smul, norm_ne_zero_iff.mpr hx0]
  have hrange : gamma '' Set.Icc 0 ‖x‖ ⊆ Metric.ball 0 (radialEuclideanRadius g₀ L) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Metric.mem_ball, dist_zero_right]
    change ‖t • e‖ < _
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact lt_of_le_of_lt ht.2 (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
  have hpull : ∀ z ∈ Metric.ball 0 (radialEuclideanRadius g₀ L),
      ∀ v : TangentSpace (𝓡 3) z,
      h.inner (surgeryBallChart g₀ L z)
        (mfderiv (𝓡 3) (𝓡 3) (surgeryBallChart g₀ L) z v)
        (mfderiv (𝓡 3) (𝓡 3) (surgeryBallChart g₀ L) z v) ≤
      (m01RescaledMetric g₀.metric c hc).inner z v v := by
    intro z hz v
    have hb := hmetric (surgeryBallChart g₀ L z)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryBallChart g₀ L) z v)
    rw [metricPullbackForm_apply, surgeryBallChart_inclusion_mfderiv g₀ L hz,
      surgeryBallChart_right_inverse g₀ L hz] at hb
    exact hb
  have hb := edist_comp_le_pathELength_of_pullback_bound (m01RescaledMetric g₀.metric c hc) h
    (fun z hz => (surgeryBallChart_contMDiffOn g₀ L z hz).contMDiffAt
      (Metric.isOpen_ball.mem_nhds hz)) hpull (norm_nonneg x) hgamma.contMDiffOn hrange
  rw [hstart, hend, surgeryBallChart_zero g₀ hL, surgeryBallChart_left_inverse] at hb
  apply hb.trans_eq
  rw [m01RescaledMetric_pathELength,
    pathELength_eq_integral_speed g₀.metric hgamma (norm_nonneg x)]
  simp_rw [show gamma = fun t : ℝ => t • e from rfl, metricPathSpeed_unit_ray g₀ e he]
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
  rfl

end PoincareConjecture.M36
