import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsCoordinateTime
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicEvolution
import PoincareConjecture.Proofs.M35.RadialGauge.MovingRadiusEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open RadialGauge

noncomputable def rawIntrinsicGaugeMap {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (t₀ : ℝ) (w : ℝ → ℝ → ℝ)
    (t : ℝ) (x : StandardCapSpace) : StandardCapSpace :=
  Real.exp (w t ‖intrinsicSpatialCoordinate (G.flow.metric (t₀ + t)) x‖) •
    intrinsicSpatialCoordinate (G.flow.metric (t₀ + t)) x

theorem rawIntrinsicGaugeMap_zero {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (t₀ : ℝ) (w : ℝ → ℝ → ℝ) (t : ℝ) :
    rawIntrinsicGaugeMap G t₀ w t 0 = 0 := by
  simp only [rawIntrinsicGaugeMap, intrinsicSpatialCoordinate_zero, smul_zero]

theorem rawIntrinsicGaugeMap_eq_radius {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (t₀ : ℝ) (w : ℝ → ℝ → ℝ) (t : ℝ)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    rawIntrinsicGaugeMap G t₀ w t x =
      (mapRadius (w t) (radialArclength (G.flow.metric (t₀ + t)) ‖x‖) / ‖x‖) • x := by
  rw [rawIntrinsicGaugeMap, intrinsicSpatialCoordinate_norm,
    intrinsicSpatialCoordinate_eq_quotient (G.flow.metric (t₀ + t)) hx, smul_smul]
  congr 1
  unfold mapRadius
  ring

theorem rawIntrinsicGaugeMap_hasDerivAt_of_radius_equation
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {w : ℝ → ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hc : ContDiffOn ℝ 1 (Function.uncurry w) (J ×ˢ univ))
    {t₀ t : ℝ} (ht : t ∈ J) (htG : t₀ + t ∈ Ioo 0 G.lifetime)
    (hs : ContDiff ℝ ∞ (w t))
    (hPDE : ∀ r > 0, HasDerivAt (fun a => mapRadius (w a) r)
      (harmonicRadialOperator 3 (rawWarpingRadius P G hrotation (t₀ + t))
        (rawWarpingRadius P G hrotation t₀) (rawRadialVelocity P G hrotation (t₀ + t))
        (mapRadius (w t)) r) t)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    HasDerivAt (fun a => rawIntrinsicGaugeMap G t₀ w a x)
      ((harmonicRadialOperator 3 (rawWarpingRadius P G hrotation (t₀ + t))
        (rawWarpingRadius P G hrotation t₀) (fun _ => 0) (mapRadius (w t))
          (radialArclength (G.flow.metric (t₀ + t)) ‖x‖) / ‖x‖) • x) t := by
  have htcc : t₀ + t ∈ Ico 0 G.lifetime := ⟨htG.1.le, htG.2⟩
  let q (a : ℝ) := radialArclength (G.flow.metric (t₀ + a)) ‖x‖
  have hqpos : 0 < q t := by
    simpa only [q, radialArclength_zero] using
      (radialArclength_strictMono (G.flow.metric (t₀ + t))) (norm_pos_iff.mpr hx)
  have hq : HasDerivAt q (rawRadialVelocity P G hrotation (t₀ + t) (q t)) t := by
    rw [rawRadialVelocity_eq P G hrotation htcc]
    have h := (raw_radialArclength_hasDerivAt_velocity G htG
      (hrotation (t₀ + t) htcc) (G.complete P htcc) (norm_nonneg x)).comp t
        ((hasDerivAt_const t t₀).add (hasDerivAt_id t))
    simpa only [q, Function.comp_def, zero_add, mul_one] using h
  have h := corrected_radius_comp_solves_harmonic hJ hc ht hs hq (hPDE (q t) hqpos)
  have hzero :
      HasDerivAt (fun a => mapRadius (w a) (q a))
        (harmonicRadialOperator 3 (rawWarpingRadius P G hrotation (t₀ + t))
          (rawWarpingRadius P G hrotation t₀) (fun _ => 0) (mapRadius (w t)) (q t)) t := by
    simpa only [harmonicRadialOperator, zero_mul, sub_zero] using h
  have heq : (fun a => rawIntrinsicGaugeMap G t₀ w a x) =
      fun a => (mapRadius (w a) (q a) / ‖x‖) • x :=
    funext (fun a => rawIntrinsicGaugeMap_eq_radius G t₀ w a hx)
  rw [heq]
  exact (hzero.div_const ‖x‖).smul_const x

end PoincareConjecture.M35.Uniqueness
