import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityCircleReplacement
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularitySemicircle
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerBoundaryArc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic











set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Complex
open scoped Topology intervalIntegral

namespace PoincareConjecture.M65Boundary

open M65StrictTrace

private theorem angular_complex (t : ℝ) :
    orthonormalBasisOneI.repr.symm (m65LoopAngular t : LoopPlane) =
      Complex.exp ((t : ℂ) * I) := by
  rw [Complex.exp_ofReal_mul_I]
  rfl

private theorem angular_periodic : Function.Periodic m65LoopAngular (2 * Real.pi) := by
  intro t
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [m65LoopAngular, Proofs.M58.angularPoint,
    Real.cos_add_two_pi, Real.sin_add_two_pi]

private theorem puncturedArc_shift (p : LoopCircle) :
    ∃ a : ℝ, ∀ t : ℝ, puncturedArc p t = m65LoopAngular (t + a) := by
  let v := -orthonormalBasisOneI.repr.symm (p : LoopPlane)
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_neg, LinearIsometryEquiv.norm_map, p.property]
  have he : Complex.exp ((Complex.arg v : ℂ) * I) = v := by
    simpa only [hv, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I v
  refine ⟨Complex.arg v, fun t => ?_⟩
  apply Subtype.ext
  apply orthonormalBasisOneI.repr.symm.injective
  change orthonormalBasisOneI.repr.symm (orthonormalBasisOneI.repr
    (boundaryCoordinate v t)) = _
  rw [LinearIsometryEquiv.symm_apply_apply, angular_complex,
    Complex.ofReal_add, add_mul, Complex.exp_add, he]
  simp only [boundaryCoordinate, mul_comm I (t : ℂ), mul_comm v]





theorem circle_integral_eq_short_arc (p : LoopCircle) {r : ℝ}
    (hrπ : r < Real.pi) (f : LoopCircle → ℝ)
    (hzero : ∀ z ∉ puncturedArc p '' Icc (-r) r, f z = 0) :
    (∫ t in Icc (-Real.pi) Real.pi, f (m65LoopAngular t)) =
      ∫ s in Icc (-r) r, f (puncturedArc p s) := by
  obtain ⟨a, ha⟩ := puncturedArc_shift p
  have hperiod : Function.Periodic (fun t => f (m65LoopAngular t)) (2 * Real.pi) :=
    fun t => congrArg f (angular_periodic t)
  have hshift : (∫ t in -Real.pi..Real.pi, f (m65LoopAngular t)) =
      ∫ t in -Real.pi..Real.pi, f (puncturedArc p t) := by
    simp_rw [ha]
    rw [intervalIntegral.integral_comp_add_right (fun t => f (m65LoopAngular t)) a]
    convert! hperiod.intervalIntegral_add_eq (-Real.pi) (-Real.pi + a) using 1 <;>
      congr 1 <;> ring
  have hsub : Icc (-r) r ⊆ Ioo (-Real.pi) Real.pi :=
    fun _ ht => ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hrπ⟩
  have hrestrict : (∫ t in Ioo (-Real.pi) Real.pi, f (puncturedArc p t)) =
      ∫ t in Icc (-r) r, f (puncturedArc p t) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo hsub
    intro t ht
    apply hzero
    rintro ⟨s, hs, he⟩
    have h := congrArg (m65WeakCircleArg p) he
    rw [arg_puncturedArc p (hsub hs), arg_puncturedArc p ht.1] at h
    exact ht.2 (h ▸ hs)
  calc
    _ = ∫ t in -Real.pi..Real.pi, f (m65LoopAngular t) := by
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
        integral_Icc_eq_integral_Ioc]
    _ = ∫ t in -Real.pi..Real.pi, f (puncturedArc p t) := hshift
    _ = ∫ t in Ioo (-Real.pi) Real.pi, f (puncturedArc p t) := by
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
        integral_Ioc_eq_integral_Ioo]
    _ = _ := hrestrict




theorem boundaryCirclePoint_eq_puncturedArc {p : ℂ} (hp : ‖p‖ = 1) (s : ℝ) :
    boundaryCirclePoint hp s =
      puncturedArc ⟨-orthonormalBasisOneI.repr p, by
        rw [norm_neg, LinearIsometryEquiv.norm_map, hp]⟩ s := by
  apply Subtype.ext
  simp only [boundaryCirclePoint, diskBoundaryCoordinate, puncturedArc, map_neg,
    LinearIsometryEquiv.symm_apply_apply, neg_neg]
  congr 2
  simp [EuclideanSpace.basisFun_apply]






theorem boundary_replacement_green_integral {M : Type*} {N : ℕ}
    (e : M → EuclideanSpace ℝ (Fin N)) (γ : LoopCircle → M)
    (p : LoopCircle) {r : ℝ} (hrπ : r < Real.pi)
    (beta B : LoopCircle → LoopCircle)
    (hmatch : ∀ z ∉ puncturedArc p '' Icc (-r) r, B z = beta z)
    (test : LoopPlane → ℝ) (i : Fin 2) (j : Fin N) :
    (∫ t in Icc (-Real.pi) Real.pi,
      (e (γ (B (m65LoopAngular t))) j - e (γ (beta (m65LoopAngular t))) j) *
        test (m65LoopAngular t) * (m65LoopAngular t : LoopPlane) i) =
      ∫ s in Icc (-r) r,
        (e (γ (B (puncturedArc p s))) j - e (γ (beta (puncturedArc p s))) j) *
          test (puncturedArc p s) * (puncturedArc p s : LoopPlane) i := by
  apply circle_integral_eq_short_arc p hrπ
    (fun z => (e (γ (B z)) j - e (γ (beta z)) j) * test z * (z : LoopPlane) i)
  intro z hz
  rw [hmatch z hz, sub_self, zero_mul, zero_mul]

end PoincareConjecture.M65Boundary
