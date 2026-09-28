import PoincareConjecture.Proofs.M35.RadialGauge.TensionEquivariance
import PoincareConjecture.Proofs.M35.RadialGauge.CorrectedEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.RadialGauge

open Uniqueness

private noncomputable abbrev e : StandardCapSpace := EuclideanSpace.single 2 1

private theorem radius_product_deriv {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (r : ℝ) :
    deriv (fun s => s * h s) r = h r + r * deriv h r := by
  simpa only [one_mul, id_eq, Pi.mul_def] using
    ((hasDerivAt_id r).mul ((hh.differentiable (by simp) r).hasDerivAt)).deriv

private theorem radius_product_second_deriv {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (r : ℝ) :
    deriv (deriv (fun s => s * h s)) r = 2 * deriv h r + r * deriv (deriv h) r := by
  have hD : deriv (fun s => s * h s) = fun s => h s + s * deriv h s :=
    funext (radius_product_deriv hh)
  rw [hD]
  have hd := (hh.differentiable (by simp) r).hasDerivAt
  have hdd := ((contDiff_infty_iff_deriv.mp hh).2.differentiable (by simp) r).hasDerivAt
  have hd2 := (hd.add ((hasDerivAt_id r).mul hdd)).deriv
  simpa only [Pi.add_def, Pi.mul_def, id_eq, one_mul, two_mul, add_assoc] using hd2

theorem mapTension_radialScale_eq_harmonic
    (g b : RiemannianMetric 3 StandardCapSpace)
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
    {x : StandardCapSpace} (hx : x ≠ 0) (hpos : 0 < h ‖x‖) :
    mapTension D B (radialScaleMap h) x =
      (harmonicRadialOperator 3 (intrinsicWarpingRadius g hg hc)
        (intrinsicWarpingRadius b hb hc₀) (fun _ => 0) (fun r => r * h r) ‖x‖ / ‖x‖) • x := by
  let r := ‖x‖
  have hr : 0 < r := norm_pos_iff.mpr hx
  have he1 : ‖e‖ = 1 := by simp [e]
  have hre : ‖r • e‖ = r := by
    rw [norm_smul, he1, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  have hre0 : r • e ≠ 0 := by
    apply norm_pos_iff.mp
    rw [hre]
    exact hr
  obtain ⟨A, hA⟩ := exists_axis_rotation x
  have hA' : standardRotation A (r • e) = x := hA
  have hrotate := mapTension_radialScale_rotation D B
    (intrinsicSpatialMetric_rotation g hg hc) (intrinsicSpatialMetric_rotation b hb hc₀)
    A hh he hre0 (by simpa only [hre] using hpos)
  rw [hA'] at hrotate
  rw [hrotate, mapTension_radialScale_axis g b hg hb hc hc₀ D B hh he hr hpos]
  let tau := harmonicRadialOperator 3 (intrinsicWarpingRadius g hg hc)
    (intrinsicWarpingRadius b hb hc₀) (fun _ => 0) (fun s => s * h s) r
  have htau : tau = 2 * deriv h r + r * deriv (deriv h) r +
      2 * deriv (intrinsicWarpingRadius g hg hc) r / intrinsicWarpingRadius g hg hc r *
        (h r + r * deriv h r) -
      2 * intrinsicWarpingRadius b hb hc₀ (r * h r) *
        deriv (intrinsicWarpingRadius b hb hc₀) (r * h r) /
          intrinsicWarpingRadius g hg hc r ^ 2 := by
    dsimp only [tau, harmonicRadialOperator]
    rw [radius_product_deriv hh, radius_product_second_deriv hh]
    norm_num only [show (3 : ℝ) - 1 = 2 by norm_num, zero_mul, sub_zero]
    ring
  change standardRotation A (_ • e) = (tau / r) • x
  rw [← htau, ← hA']
  change Matrix.toEuclideanLin A.1 (tau • e) = (tau / r) • Matrix.toEuclideanLin A.1 (r • e)
  rw [map_smul, map_smul, smul_smul, div_mul_cancel₀ tau hr.ne']

end PoincareConjecture.M35.RadialGauge
