import PoincareConjecture.Proofs.M35.Thm12_28.CylinderConnection

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35

theorem roundCylinderChristoffel_eq {u : ℝ} (hu : u < 1) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) (a b d : Fin 3) :
    roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d =
      (-2 / (‖p.1‖ ^ 2 + 4)) *
        (inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis d).1 *
            inner ℝ p.1 (roundCylinderCoordinateBasis b).1 +
          inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1 *
            inner ℝ p.1 (roundCylinderCoordinateBasis d).1 -
          inner ℝ (roundCylinderCoordinateBasis b).1 (roundCylinderCoordinateBasis d).1 *
            inner ℝ p.1 (roundCylinderCoordinateBasis a).1) := by
  unfold roundCylinderChristoffel
  rw [roundCylinderGram_inv_eq hu]
  simp_rw [fderiv_roundCylinderGram_apply]
  have ht : 1 - u ≠ 0 := by linarith
  have hp : ‖p.1‖ ^ 2 + 4 ≠ 0 := ne_of_gt (by positivity)
  fin_cases a <;> fin_cases b <;> fin_cases d <;>
    simp [Matrix.diagonal, roundCylinderCoordinateBasis,
      EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] <;>
    field_simp <;> ring

theorem fderiv_roundCylinderChristoffel_center {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (s : ℝ) (v : RoundCylinderCoordinates) (a b d : Fin 3) :
    fderiv ℝ (fun p : RoundCylinderCoordinates =>
      roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d)
      (0, s) v = (-1 / 2 : ℝ) *
        (inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis d).1 *
            inner ℝ v.1 (roundCylinderCoordinateBasis b).1 +
          inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1 *
            inner ℝ v.1 (roundCylinderCoordinateBasis d).1 -
          inner ℝ (roundCylinderCoordinateBasis b).1 (roundCylinderCoordinateBasis d).1 *
            inner ℝ v.1 (roundCylinderCoordinateBasis a).1) := by
  let ev (i : Fin 3) : RoundCylinderCoordinates →L[ℝ] ℝ :=
    (innerSL ℝ (roundCylinderCoordinateBasis i).1).comp
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
  let L : RoundCylinderCoordinates →L[ℝ] ℝ :=
    (inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis d).1) • ev b +
    (inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1) • ev d -
    (inner ℝ (roundCylinderCoordinateBasis b).1 (roundCylinderCoordinateBasis d).1) • ev a
  have hfun : (fun p : RoundCylinderCoordinates =>
      roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) =
      fun p => (-2 / (‖p.1‖ ^ 2 + 4)) * L p := by
    funext p
    rw [roundCylinderChristoffel_eq hu]
    simp [L, ev, real_inner_comm]
  have hf : DifferentiableAt ℝ
      (fun p : RoundCylinderCoordinates => -2 / (‖p.1‖ ^ 2 + 4)) (0, s) := by
    have hn : ContDiff ℝ ∞ (fun p : RoundCylinderCoordinates => ‖p.1‖ ^ 2) :=
      (contDiff_norm_sq ℝ).comp contDiff_fst
    have hff : ContDiff ℝ ∞
        (fun p : RoundCylinderCoordinates => -2 / (‖p.1‖ ^ 2 + 4)) :=
      contDiff_const.div (hn.add contDiff_const) (fun p => ne_of_gt (by positivity))
    exact hff.differentiable (by simp) (0, s)
  have hd := hf.hasFDerivAt.mul L.hasFDerivAt
  rw [hfun]
  convert! congrArg (fun A : RoundCylinderCoordinates →L[ℝ] ℝ => A v) hd.fderiv using 1
  norm_num [L, ev, real_inner_comm]

theorem contDiff_roundCylinderChristoffel {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (a b d : Fin 3) :
    ContDiff ℝ ∞ (fun p : RoundCylinderCoordinates =>
      roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) := by
  simp_rw [roundCylinderChristoffel_eq hu]
  have hn : ContDiff ℝ ∞ (fun p : RoundCylinderCoordinates => ‖p.1‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp contDiff_fst
  apply ContDiff.mul
  · exact contDiff_const.div (hn.add contDiff_const) (fun p => ne_of_gt (by positivity))
  · have he (i : Fin 3) : ContDiff ℝ ∞ (fun p : RoundCylinderCoordinates =>
        inner ℝ p.1 (roundCylinderCoordinateBasis i).1) :=
      contDiff_fst.inner ℝ contDiff_const
    exact ((contDiff_const.mul (he b)).add (contDiff_const.mul (he d))).sub
      (contDiff_const.mul (he a))

end PoincareConjecture.M35
