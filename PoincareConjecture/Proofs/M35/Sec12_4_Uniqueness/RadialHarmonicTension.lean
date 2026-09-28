import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.IntrinsicTensionTrace
import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.RadialMapAxis










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1

variable (g b : RiemannianMetric 3 StandardCapSpace)
  (hg : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hb : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      b.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = b.inner x u v)
  (hc : MetricComplete g) (hc₀ : MetricComplete b)
  (D : LeviCivitaData (intrinsicSpatialMetric g hg hc))
  (B : LeviCivitaData (intrinsicSpatialMetric b hb hc₀))
  {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (he : Function.Even h)
  {r : ℝ} (hr : 0 < r) (hhpos : 0 < h r)

local notation "f" => intrinsicWarpingRadius g hg hc
local notation "f₀" => intrinsicWarpingRadius b hb hc₀

include hh he hr hhpos

private theorem mapHessian_radial_angular (i : Fin 3) (hi : i ≠ 2) :
    mapCovariantHessian D B (radialScaleMap h) (r • e 2) (e i) (e i) =
      ((f r * deriv f r * (h r + r * deriv h r) -
        f₀ (r * h r) * deriv f₀ (r * h r)) / r ^ 2) • e 2 := by
  have hρ : 0 < r * h r := mul_pos hr hhpos
  rw [mapCovariantHessian_apply, radialScaleMap_hessian_angular hh hr he i hi,
    radialScaleMap_axis hr, radialScaleMap_fderiv_angular hh hr i hi,
    intrinsicSpatialMetric_connection_angular g hg hc D hr i hi,
    B.euclideanConnection_smul_left, B.euclideanConnection_smul_right]
  simp only [Pi.smul_apply]
  rw [intrinsicSpatialMetric_connection_angular b hb hc₀ B hρ i hi,
    map_smul, radialScaleMap_fderiv_axis hh hr]
  simp only [smul_smul, ← add_smul, ← sub_smul]
  congr 1
  field_simp [hr.ne', hhpos.ne']
  ring

private theorem mapHessian_radial_axis :
    mapCovariantHessian D B (radialScaleMap h) (r • e 2) (e 2) (e 2) =
      (2 * deriv h r + r * deriv (deriv h) r) • e 2 := by
  have hρ : 0 < r * h r := mul_pos hr hhpos
  rw [mapCovariantHessian_apply, radialScaleMap_hessian_axis hh hr he,
    radialScaleMap_axis hr, radialScaleMap_fderiv_axis hh hr,
    intrinsicSpatialMetric_connection_axis g hg hc D hr,
    B.euclideanConnection_smul_left, B.euclideanConnection_smul_right]
  simp only [Pi.smul_apply]
  rw [intrinsicSpatialMetric_connection_axis b hb hc₀ B hρ]
  simp only [smul_zero, add_zero, map_zero, sub_zero]



theorem mapTension_radialScale_axis :
    mapTension D B (radialScaleMap h) (r • e 2) =
      (2 * deriv h r + r * deriv (deriv h) r +
        2 * deriv f r / f r * (h r + r * deriv h r) -
        2 * f₀ (r * h r) * deriv f₀ (r * h r) / f r ^ 2) • e 2 := by
  rw [mapTension_intrinsic_axis g hg hc D B,
    mapHessian_radial_angular g b hg hb hc hc₀ D B hh he hr hhpos 0 (by decide),
    mapHessian_radial_angular g b hg hb hc hc₀ D B hh he hr hhpos 1 (by decide),
    mapHessian_radial_axis g b hg hb hc hc₀ D B hh he hr hhpos]
  simp only [smul_smul, ← add_smul]
  congr 1
  have hQ : intrinsicWarpingQuotient g hg hc r = f r / r := by
    apply (eq_div_iff hr.ne').mpr
    simpa only [mul_comm] using mul_intrinsicWarpingQuotient g hg hc r
  rw [hQ]
  field_simp [hr.ne', (intrinsicWarpingRadius_pos g hg hc hr).ne']
  ring

end PoincareConjecture.M35.Uniqueness
