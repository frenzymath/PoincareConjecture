import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsMapTime
import PoincareConjecture.Proofs.M35.RadialGauge.NativeRadiusTension
import PoincareConjecture.Proofs.M35.RadialGauge.NativeGaugeVelocity
import PoincareConjecture.Proofs.M35.RadialGauge.TensionTip

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open RadialGauge

theorem rawIntrinsicGaugeMap_solves_native_harmonic
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {w : ℝ → ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hc : ContDiffOn ℝ 1 (Function.uncurry w) (J ×ˢ univ))
    {t₀ t : ℝ} (ht₀ : t₀ ∈ Ico 0 G.lifetime) (ht : t ∈ J)
    (htG : t₀ + t ∈ Ioo 0 G.lifetime)
    (hs : ContDiff ℝ ∞ (w t)) (he : Function.Even (w t))
    (hPDE : ∀ r > 0, HasDerivAt (fun a => mapRadius (w a) r)
      (harmonicRadialOperator 3 (rawWarpingRadius P G hrotation (t₀ + t))
        (rawWarpingRadius P G hrotation t₀) (rawRadialVelocity P G hrotation (t₀ + t))
        (mapRadius (w t)) r) t)
    (DI : LeviCivitaData (intrinsicSpatialMetric (G.flow.metric (t₀ + t))
      (hrotation (t₀ + t) ⟨htG.1.le, htG.2⟩) (G.complete P ⟨htG.1.le, htG.2⟩)))
    (B : LeviCivitaData (intrinsicSpatialMetric (G.flow.metric t₀)
      (hrotation t₀ ht₀) (G.complete P ht₀))) (x : StandardCapSpace) :
    HasDerivAt (fun a => rawIntrinsicGaugeMap G t₀ w a x)
      (mapTension (G.flow.connection (t₀ + t)) B (rawIntrinsicGaugeMap G t₀ w t) x) t := by
  let g := G.flow.metric (t₀ + t)
  let b := G.flow.metric t₀
  have htcc : t₀ + t ∈ Ico 0 G.lifetime := ⟨htG.1.le, htG.2⟩
  let hg := hrotation (t₀ + t) htcc
  let hb := hrotation t₀ ht₀
  let hgc := G.complete P htcc
  let hbc := G.complete P ht₀
  let h (r : ℝ) := Real.exp (w t r)
  have hh : ContDiff ℝ ∞ h := hs.exp
  have heh : Function.Even h := fun r => congrArg Real.exp (he r)
  have hF : ContDiff ℝ ∞ (radialScaleMap h) := radialScaleMap_contDiff hh heh
  have hmap : rawIntrinsicGaugeMap G t₀ w t = radialScaleMap h ∘ intrinsicSpatialCoordinate g := rfl
  have hnatural (y : StandardCapSpace) :
      mapTension (G.flow.connection (t₀ + t)) B (rawIntrinsicGaugeMap G t₀ w t) y =
        mapTension DI B (radialScaleMap h) (intrinsicSpatialCoordinate g y) := by
    rw [hmap]
    exact mapTension_original_intrinsic g _ hg hgc (G.flow.connection (t₀ + t)) B DI hF y
  by_cases hx : x = 0
  · subst x
    rw [hnatural, intrinsicSpatialCoordinate_zero,
      mapTension_radialScale_zero DI B (intrinsicSpatialMetric_rotation g hg hgc)
        (intrinsicSpatialMetric_rotation b hb hbc) hh heh (fun r => Real.exp_pos _)]
    simpa only [rawIntrinsicGaugeMap_zero] using hasDerivAt_const t (0 : StandardCapSpace)
  have hq : 0 < radialArclength g ‖x‖ := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono g) (norm_pos_iff.mpr hx)
  have hy : intrinsicSpatialCoordinate g x ≠ 0 := by
    apply norm_pos_iff.mp
    rw [intrinsicSpatialCoordinate_norm]
    exact hq
  have hnative := mapTension_radialScale_eq_harmonic g b hg hb hgc hbc DI B hh heh hy
    (Real.exp_pos _)
  have hvelocity := rawIntrinsicGaugeMap_hasDerivAt_of_radius_equation
    P G hrotation hJ hc ht htG hs hPDE hx
  have heq : mapTension (G.flow.connection (t₀ + t)) B (rawIntrinsicGaugeMap G t₀ w t) x =
      (harmonicRadialOperator 3 (rawWarpingRadius P G hrotation (t₀ + t))
        (rawWarpingRadius P G hrotation t₀) (fun _ => 0) (mapRadius (w t))
          (radialArclength g ‖x‖) / ‖x‖) • x := by
    rw [hnatural, hnative, intrinsicSpatialCoordinate_norm,
      intrinsicSpatialCoordinate_eq_quotient g hx, smul_smul,
      rawWarpingRadius_eq P G hrotation htcc, rawWarpingRadius_eq P G hrotation ht₀]
    congr 1
    change (_ / radialArclength g ‖x‖) * (radialArclength g ‖x‖ / ‖x‖) = _
    rw [div_mul_div_cancel₀ hq.ne']
    rfl
  rw [heq]
  exact hvelocity

end PoincareConjecture.M35.Uniqueness
