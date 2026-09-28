import PoincareConjecture.Proofs.M35.Uniqueness.RadialConnection
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Euclidean
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem radialConnection_contDiffAt
    (g : RiemannianMetric 3 StandardCapSpace) {r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ ∞ (radialConnectionAlpha g) r ∧
      ContDiffAt ℝ ∞ (radialConnectionBeta g) r ∧
      ContDiffAt ℝ ∞ (radialConnectionGamma g) r := by
  have ha := (axisAngularCoefficient_contDiff g).contDiffAt (x := r)
  have hb := (axisRadialCoefficient_contDiff g).contDiffAt (x := r)
  have hcor : ContDiffAt ℝ ∞ (axisCorrectionCoefficient g) r :=
    (hb.sub ha).div (contDiffAt_id.pow 2) (pow_ne_zero 2 hr.ne')
  have hda : ContDiffAt ℝ ∞ (deriv (axisAngularCoefficient g)) r :=
    ha.derivWithin (by simp)
  have hA : ContDiffAt ℝ ∞ (radialConnectionAlpha g) r :=
    hda.div ((contDiffAt_const.mul ha).mul contDiffAt_id)
      (mul_ne_zero (mul_ne_zero (by norm_num)
        (axisAngularCoefficient_pos g r).ne') hr.ne')
  have hB : ContDiffAt ℝ ∞ (radialConnectionBeta g) r :=
    (hcor.sub (hda.div (contDiffAt_const.mul contDiffAt_id)
      (by positivity : (2 : ℝ) * r ≠ 0))).div hb
      (axisRadialCoefficient_pos g r).ne'
  have hdcor : ContDiffAt ℝ ∞ (deriv (axisCorrectionCoefficient g)) r :=
    hcor.derivWithin (by simp)
  have hC : ContDiffAt ℝ ∞ (radialConnectionGamma g) r :=
    ((hdcor.div (contDiffAt_const.mul contDiffAt_id)
      (by positivity : (2 : ℝ) * r ≠ 0)).sub
        ((contDiffAt_const.mul hcor).mul hA)).div hb
          (axisRadialCoefficient_pos g r).ne'
  exact ⟨hA, hB, hC⟩

private theorem norm_hasFDerivAt {x : StandardCapSpace} (hx : x ≠ 0) :
    HasFDerivAt (fun y : StandardCapSpace => ‖y‖)
      (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq_eq_abs, abs_norm] at h
  convert! h using 1
  ext w
  simp [smul_eq_mul]
  ring

theorem rotational_connection_first_derivative
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {x : StandardCapSpace} (hx : x ≠ 0) (u v w : StandardCapSpace) :
    fderiv ℝ (D.euclideanConnection u v) x w =
      (deriv (radialConnectionAlpha g) ‖x‖ / ‖x‖ * inner ℝ x w) •
          (inner ℝ x u • v + inner ℝ x v • u) +
        radialConnectionAlpha g ‖x‖ •
          (inner ℝ w u • v + inner ℝ w v • u) +
        (deriv (radialConnectionBeta g) ‖x‖ / ‖x‖ * inner ℝ x w * inner ℝ u v +
          deriv (radialConnectionGamma g) ‖x‖ / ‖x‖ *
            inner ℝ x w * inner ℝ x u * inner ℝ x v +
          radialConnectionGamma g ‖x‖ *
            (inner ℝ w u * inner ℝ x v + inner ℝ x u * inner ℝ w v)) • x +
        (radialConnectionBeta g ‖x‖ * inner ℝ u v +
          radialConnectionGamma g ‖x‖ * inner ℝ x u * inner ℝ x v) • w := by
  obtain ⟨hA, hB, hC⟩ := radialConnection_contDiffAt g (norm_pos_iff.mpr hx)
  have hn := norm_hasFDerivAt hx
  have hda := ((hA.differentiableAt (by simp)).hasDerivAt).comp_hasFDerivAt x hn
  have hdb := ((hB.differentiableAt (by simp)).hasDerivAt).comp_hasFDerivAt x hn
  have hdc := ((hC.differentiableAt (by simp)).hasDerivAt).comp_hasFDerivAt x hn
  have hu := (innerSL ℝ u).hasFDerivAt (x := x)
  have hv := (innerSL ℝ v).hasFDerivAt (x := x)
  have hd := (hda.smul ((hu.smul_const v).add (hv.smul_const u))).add
    (((hdb.mul_const (inner ℝ u v)).add ((hdc.mul hu).mul hv)).smul (hasFDerivAt_id x))
  have heq : D.euclideanConnection u v =ᶠ[𝓝 x]
      (fun y => radialConnectionAlpha g ‖y‖ •
          (inner ℝ u y • v + inner ℝ v y • u) +
        (radialConnectionBeta g ‖y‖ * inner ℝ u v +
          radialConnectionGamma g ‖y‖ * inner ℝ u y * inner ℝ v y) • y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    have h := rotational_connection_const D hrotation hy u v
    simpa only [LeviCivitaData.euclideanConnection, real_inner_comm y u,
      real_inner_comm y v] using h
  erw [heq.fderiv_eq, hd.fderiv]
  ext i
  simp only [add_apply, smul_apply, Pi.add_apply, Pi.mul_apply, id_eq,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, innerSL_apply_apply,
    Function.comp_apply, PiLp.add_apply, PiLp.smul_apply, real_inner_comm u x,
    real_inner_comm v x, real_inner_comm u w, real_inner_comm v w]
  ring

end PoincareConjecture.M35.Uniqueness
