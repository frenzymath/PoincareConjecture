import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsGaugeCoefficients
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsForcingEnd
import PoincareConjecture.Proofs.M35.RadialGauge.RadialTimeEquation










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open SmoothRadial RadialGauge

variable (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
  (G : PartialStandardCapFlow g₀)
  (hrotation : ∀ t ∈ Ico 0 G.lifetime,
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
      (G.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)

local notation "V" => EuclideanSpace ℝ (Fin 5)
local notation "f" => rawWarpingRadius P G hrotation
local notation "v" => rawRadialVelocity P G hrotation

theorem rawIntrinsicGaugeDrift_eq_radial {t : ℝ} (ht : t ∈ Ico 0 G.lifetime)
    {x : V} (hx : x ≠ 0) :
    rawIntrinsicGaugeDrift P G hrotation t x =
      (radialGaugeDrift (f t) (v t) ‖x‖ / ‖x‖) • x := by
  let h (r : ℝ) := Real.log (axisDivision (f t) r)
  let xi := axisDivision (v t)
  have hhe : h = intrinsicLogWarping (G.flow.metric t)
      (hrotation t ht) (G.complete P ht) := by
    dsimp only [h]
    rw [rawWarpingRadius_eq P G hrotation ht]
    rfl
  have hhs : ContDiff ℝ ∞ h := by
    rw [hhe]
    exact intrinsicLogWarping_contDiff _ _ _
  have hhp : Function.Even h := by
    rw [hhe]
    exact intrinsicLogWarping_even _ _ _
  have hvs : ContDiff ℝ ∞ (v t) := by
    rw [rawRadialVelocity_eq P G hrotation ht]
    exact intrinsicRadialVelocity_contDiff _ _ _
  have hmap : mapRadius h = f t := by
    rw [hhe, rawWarpingRadius_eq P G hrotation ht]
    exact funext (fun r => (intrinsicWarpingRadius_eq_exp _ _ _ r).symm)
  have hvelocity : (fun r => r * xi r) = v t := by
    funext r
    have hz : v t 0 = 0 := by
      rw [rawRadialVelocity_eq P G hrotation ht, intrinsicRadialVelocity_zero]
    simpa only [xi, hz, sub_zero] using mul_axisDivision hvs r
  have hd := smoothGaugeDrift_eq_radial (xi := xi) hhs hhp (norm_pos_iff.mpr hx)
  rw [hmap, hvelocity] at hd
  simp only [smoothGaugeDrift, Real.norm_eq_abs, abs_norm, smul_eq_mul] at hd
  have hcoefficient : 2 * axisDivision (deriv h) ‖x‖ - xi ‖x‖ =
      radialGaugeDrift (f t) (v t) ‖x‖ / ‖x‖ :=
    (eq_div_iff (norm_ne_zero_iff.mpr hx)).mpr hd
  change (2 * axisDivision (deriv h) ‖x‖ - xi ‖x‖) • x = _
  rw [hcoefficient]



theorem raw_intrinsic_radius_time_equation
    {u : ℝ → V → ℝ} {T t₀ t r : ℝ} (hTlt : T < G.lifetime)
    (ht₀ : t₀ ∈ Icc 0 T) (ht : t₀ + t ∈ Icc 0 T)
    (hu : ContDiff ℝ ∞ (u t))
    (hinvariant : ∀ (Q : V ≃ₗᵢ[ℝ] V) x, u t (Q x) = u t x)
    {e : V} (he : ‖e‖ = 1) (hr : 0 < r)
    (hPDE : HasDerivAt (fun s => u s (r • e))
      (euclideanLaplacian (u t) (r • e) + gaugeSource
        (rawIntrinsicGaugeDrift P G hrotation (t₀ + t))
        (rawIntrinsicGaugeForcing P G hrotation t₀ (t₀ + t)) (u t) (r • e)) t) :
    HasDerivAt (fun s => mapRadius (fun z => u s (z • e)) r)
      (harmonicRadialOperator 3 (f (t₀ + t)) (f t₀) (v (t₀ + t))
        (mapRadius (fun z => u t (z • e))) r) t := by
  have htG : t₀ + t ∈ Ico 0 G.lifetime := ⟨ht.1, ht.2.trans_lt hTlt⟩
  have hnorm : ‖r • e‖ = r := by
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  have hx : r • e ≠ 0 := norm_pos_iff.mp (hnorm.symm ▸ hr)
  have hfr : f (t₀ + t) r ≠ 0 := by
    rw [rawWarpingRadius_eq P G hrotation htG]
    exact (intrinsicWarpingRadius_pos _ _ _ hr).ne'
  have hb := rawIntrinsicGaugeDrift_eq_radial P G hrotation htG hx
  rw [hnorm] at hb
  have hsource := (raw_intrinsic_gauge_forcing_radial_eq P G hrotation hTlt ht ht₀
    hx (u t (r • e))).1
  rw [hnorm, radialGaugeForcing_eq] at hsource
  exact invariant_R5_radius_time_equation hu hinvariant he hr
    (f (t₀ + t)) (f t₀) (v (t₀ + t)) hfr hb hsource hPDE

end PoincareConjecture.M35.Uniqueness
