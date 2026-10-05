import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.MetricUniqueness.HarmonicTension
import PoincareLib.Geometry.RicciFlow.Local.Gauge.Pullback.PullbackConnection

/-!
# Actual gauge pullback metrics on Euclidean space

Morgan-Tian Proposition 12.26, pp. 320-322. The native pullback metric
constructor only needs smoothness of its actual bilinear section.
Euclidean metric coefficients provide that smoothness on the complete
noncompact domain, without the compact-space assumption of M03's
metric-family producer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Bundle

namespace PoincareMT.M35.Uniqueness

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem contMDiff_gaugePullback_section (g : RiemannianMetric n V)
    (Φ : Diffeomorph (𝓡 n) (𝓡 n) V V ∞) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ)) ∞
      (fun x : V => Bundle.TotalSpace.mk' (V →L[ℝ] V →L[ℝ] ℝ) x (pinner g Φ x)) := by
  have hΦ : ContDiff ℝ ∞ (Φ : V → V) := contMDiff_iff_contDiff.mp Φ.contMDiff
  have hdΦ := hΦ.fderiv_right (m := ∞) (by simp)
  have hg : ContDiff ℝ ∞ g.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  let C : V → V →L[ℝ] V →L[ℝ] ℝ := fun x =>
    (g.euclideanCoefficients (Φ x)).bilinearComp (fderiv ℝ (Φ : V → V) x)
      (fderiv ℝ (Φ : V → V) x)
  have hC : ContDiff ℝ ∞ C := by
    apply contDiff_clm_apply_iff.mpr
    intro v
    apply contDiff_clm_apply_iff.mpr
    intro w
    exact ((hg.comp hΦ).clm_apply (hdΦ.clm_apply contDiff_const)).clm_apply
      (hdΦ.clm_apply contDiff_const)
  intro x
  rw [Bundle.contMDiffAt_section]
  convert! hC.contDiffAt.contMDiffAt using 1
  ext y v w
  suffices he : pinner g Φ y v w = g.inner (Φ y)
      (fderiv ℝ (Φ : V → V) y v) (fderiv ℝ (Φ : V → V) y w) by
    simpa [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace,
      C, RiemannianMetric.euclideanCoefficients] using he
  have he := pinner_apply g Φ y v w
  simp only [mfderiv_eq_fderiv] at he
  exact he

/-- The native actual pullback, with smoothness proved on all space. -/
def gaugePullbackMetric (g : RiemannianMetric n V)
    (Φ : Diffeomorph (𝓡 n) (𝓡 n) V V ∞) : RiemannianMetric n V :=
  pullbackMetric g Φ (contMDiff_gaugePullback_section g Φ)

theorem gaugePullbackMetric_inner (g : RiemannianMetric n V)
    (Φ : Diffeomorph (𝓡 n) (𝓡 n) V V ∞) (x u v : V) :
    (gaugePullbackMetric g Φ).inner x u v =
      g.inner (Φ x) (fderiv ℝ (Φ : V → V) x u) (fderiv ℝ (Φ : V → V) x v) := by
  rw [gaugePullbackMetric, pullbackMetric_inner, mfderiv_eq_fderiv]
  rfl

end PoincareMT.M35.Uniqueness
