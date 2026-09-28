import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Transverse.RayComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Polar.ChangeOfVariables
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.CenterDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]

theorem pullbackVolumeDensity_le_one_on_regular_ray
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (hm : 0 < m)
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M}
    {U : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    (hU : IsOpen U) (h0 : (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ U)
    (he : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e U)
    (hgeo : ∀ v ∈ U, g.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (hmetric : ∀ u v : EuclideanSpace ℝ (Fin (m + 1)),
      g.inner (e 0) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 u)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 v) = inner ℝ u v)
    (θ : EuclideanSpace ℝ (Fin (m + 1))) (hθ : ‖θ‖ = 1)
    {b : ℝ} (hb : 0 < b) (hsub : ∀ s ∈ Icc 0 b, s • θ ∈ U)
    (hi : ∀ s ∈ Icc 0 b,
      Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (s • θ)))
    (hRic : ∀ s ∈ Ioo 0 b, ∀ v : TangentSpace (𝓡 (m + 1)) (e (s • θ)),
      0 ≤ D.ricci (e (s • θ)) v v)
    {s : ℝ} (hs : s ∈ Ioo 0 b) :
    g.pullbackVolumeDensity e (s • θ) ≤ 1 := by
  have hi0 : Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0) := by
    intro u v huv
    have h := hmetric (u - v) (u - v)
    simp only [map_sub, huv, sub_self, map_zero] at h
    exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)
      (E := EuclideanSpace ℝ (Fin (m + 1)))).mp h.symm)
  have hρ := (g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (hU.mem_nhds h0)) hi0).1
  have hline : ContinuousAt (fun t : ℝ => t • θ) 0 := by fun_prop
  have hlim : Tendsto (fun t : ℝ => g.pullbackVolumeDensity e (t • θ))
      (𝓝[>] 0) (𝓝 1) := by
    have hρ' : ContinuousAt (g.pullbackVolumeDensity e) ((0 : ℝ) • θ) := by
      simpa only [zero_smul] using hρ.continuousAt
    have H := (hρ'.comp (f := fun t : ℝ => t • θ) hline).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [Function.comp_def, zero_smul,
      g.pullbackVolumeDensity_zero_eq_one e hmetric] using! H
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hs.1)] with t ht hts
  have ht' : t ∈ Ioo 0 b := ⟨ht, hts.trans hs.2⟩
  have h := g.polarDensity_cross_le_on_regular_ray D hm hU h0 he hgeo hmetric
    θ hθ hb (κ := 0) le_rfl hsub hi
    (fun r hr v => by simpa using hRic r hr v) ht' hs hts.le
  simp only [modelS_zero_curvature] at h
  have htpos : 0 < t := ht
  have hprod : 0 < s ^ m * t ^ m := mul_pos (pow_pos hs.1 m) (pow_pos htpos m)
  nlinarith

theorem pullbackVolumeDensity_le_one_on_normal_ball
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (hm : 0 < m)
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M} {R : ℝ} (hR : 0 < R)
    (he : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e (Metric.ball 0 R))
    (hgeo : ∀ v ∈ Metric.ball 0 R, g.IsGeodesicOn (fun s : ℝ => e (s • v))
      {s | s • v ∈ Metric.ball 0 R})
    (hmetric : ∀ u v : EuclideanSpace ℝ (Fin (m + 1)),
      g.inner (e 0) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 u)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 v) = inner ℝ u v)
    (hi : ∀ v ∈ Metric.ball 0 R,
      Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e v))
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 (m + 1)) x, 0 ≤ D.ricci x v v)
    {x : EuclideanSpace ℝ (Fin (m + 1))} (hx : x ∈ Metric.ball 0 R) :
    g.pullbackVolumeDensity e x ≤ 1 := by
  by_cases hx0 : x = 0
  · subst x
    exact (g.pullbackVolumeDensity_zero_eq_one e hmetric).le
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hxR : ‖x‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  let θ := ‖x‖⁻¹ • x
  have hθ : ‖θ‖ = 1 := norm_smul_inv_norm hx0
  have hback : ‖x‖ • θ = x := by
    dsimp [θ]
    rw [smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
  obtain ⟨b, hxb, hbR⟩ := exists_between hxR
  have hb : 0 < b := hxpos.trans hxb
  have hsub (s : ℝ) (hs : s ∈ Icc 0 b) : s • θ ∈ Metric.ball 0 R := by
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hs.1,
      hθ, mul_one]
    exact hs.2.trans_lt hbR
  have H := g.pullbackVolumeDensity_le_one_on_regular_ray D hm Metric.isOpen_ball
    (Metric.mem_ball_self hR) he hgeo hmetric θ hθ hb hsub
    (fun s hs => hi _ (hsub s hs)) (fun s _ v => hRic _ v) ⟨hxpos, hxb⟩
  simpa only [hback] using H

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem pullbackVolumeDensity_eq_one_of_ball_volume_eq
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (hm : 0 < m)
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M} {R : ℝ} (hR : 0 < R)
    (he : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e (Metric.ball 0 R))
    (hgeo : ∀ v ∈ Metric.ball 0 R, g.IsGeodesicOn (fun s : ℝ => e (s • v))
      {s | s • v ∈ Metric.ball 0 R})
    (hmetric : ∀ u v : EuclideanSpace ℝ (Fin (m + 1)),
      g.inner (e 0) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 u)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 v) = inner ℝ u v)
    (hi : ∀ v ∈ Metric.ball 0 R,
      Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e v))
    (hinj : InjOn e (Metric.ball 0 R))
    (himage : e '' Metric.ball 0 R = g.ball (e 0) R)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 (m + 1)) x, 0 ≤ D.ricci x v v)
    (hvol : g.volumeMeasure (g.ball (e 0) R) =
      ENNReal.ofReal (euclideanUnitBallVolume (m + 1) * R ^ (m + 1))) :
    ∀ x ∈ Metric.ball 0 R, g.pullbackVolumeDensity e x = 1 := by
  have hchange := g.volumeMeasure_image_eq_lintegral_of_mdifferentiableAt_injOn
    Metric.isOpen_ball.measurableSet
    (fun x hx => (he.contMDiffAt (Metric.isOpen_ball.mem_nhds hx)).mdifferentiableAt
      (by simp)) hinj
  rw [himage, hvol] at hchange
  have hbound : ∀ x ∈ Metric.ball 0 R, ENNReal.ofReal (g.pullbackVolumeDensity e x) ≤ 1 := by
    intro x hx
    exact ENNReal.ofReal_le_one.mpr
      (g.pullbackVolumeDensity_le_one_on_normal_ball D hm hR he hgeo hmetric hi hRic hx)
  have hae : (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x)) =ᵐ[
      volume.restrict (Metric.ball 0 R)] (fun _ => 1) := by
    apply ae_eq_of_ae_le_of_lintegral_le
      ((ae_restrict_mem Metric.isOpen_ball.measurableSet).mono hbound)
    · rw [← hchange]
      exact ENNReal.ofReal_ne_top
    · exact measurable_const.aemeasurable
    · simp only [lintegral_const, Measure.restrict_apply_univ, one_mul, ← hchange]
      exact (euclidean_ball_volume_eq (m + 1) hR).le
  have hc : ContinuousOn (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))
      (Metric.ball 0 R) := by
    intro x hx
    exact (ENNReal.continuous_ofReal.continuousAt.comp
      (g.contDiffAt_pullbackVolumeDensity
        (he.contMDiffAt (Metric.isOpen_ball.mem_nhds hx)) (hi x hx)).1.continuousAt
      ).continuousWithinAt
  have hpoint := Measure.eqOn_open_of_ae_eq hae Metric.isOpen_ball hc continuousOn_const
  intro x hx
  exact ENNReal.ofReal_eq_one.mp (hpoint hx)

end PoincareConjecture.RiemannianMetric
