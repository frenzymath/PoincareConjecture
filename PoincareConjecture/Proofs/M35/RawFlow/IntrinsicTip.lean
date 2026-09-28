import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicWarping
import PoincareConjecture.Proofs.M35.Mathlib.SmoothEvenRadial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv











set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open SmoothRadial

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g)


noncomputable def intrinsicWarpingQuotient (s : ℝ) : ℝ :=
  axisDivision (intrinsicWarpingRadius g hrotation hcomplete) s

theorem intrinsicWarpingQuotient_contDiff :
    ContDiff ℝ ∞ (intrinsicWarpingQuotient g hrotation hcomplete) :=
  axisDivision_contDiff (intrinsicWarpingRadius_contDiff g hrotation hcomplete)

theorem intrinsicWarpingQuotient_even :
    Function.Even (intrinsicWarpingQuotient g hrotation hcomplete) :=
  axisDivision_even_of_odd (intrinsicWarpingRadius_contDiff g hrotation hcomplete)
    (intrinsicWarpingRadius_odd g hrotation hcomplete)

theorem intrinsicWarpingQuotient_zero :
    intrinsicWarpingQuotient g hrotation hcomplete 0 = 1 := by
  rw [intrinsicWarpingQuotient, axisDivision_zero,
    (intrinsicWarpingRadius_hasDerivAt_zero g hrotation hcomplete).deriv]

theorem mul_intrinsicWarpingQuotient (s : ℝ) :
    s * intrinsicWarpingQuotient g hrotation hcomplete s =
      intrinsicWarpingRadius g hrotation hcomplete s := by
  rw [intrinsicWarpingQuotient,
    mul_axisDivision (intrinsicWarpingRadius_contDiff g hrotation hcomplete),
    intrinsicWarpingRadius_zero, sub_zero]


theorem intrinsicWarpingQuotient_pos (s : ℝ) :
    0 < intrinsicWarpingQuotient g hrotation hcomplete s := by
  have hp (r : ℝ) (hr : 0 < r) :
      0 < intrinsicWarpingQuotient g hrotation hcomplete r := by
    have h := intrinsicWarpingRadius_pos g hrotation hcomplete hr
    rw [← mul_intrinsicWarpingQuotient g hrotation hcomplete] at h
    exact (mul_pos_iff_of_pos_left hr).mp h
  rcases lt_trichotomy s 0 with hs | hs | hs
  · have h := hp (-s) (neg_pos.mpr hs)
    rwa [intrinsicWarpingQuotient_even g hrotation hcomplete s] at h
  · rw [hs, intrinsicWarpingQuotient_zero]
    norm_num
  · exact hp s hs


noncomputable def intrinsicLogWarping (s : ℝ) : ℝ :=
  Real.log (intrinsicWarpingQuotient g hrotation hcomplete s)

theorem intrinsicLogWarping_contDiff :
    ContDiff ℝ ∞ (intrinsicLogWarping g hrotation hcomplete) :=
  (intrinsicWarpingQuotient_contDiff g hrotation hcomplete).log
    (fun s => (intrinsicWarpingQuotient_pos g hrotation hcomplete s).ne')

theorem intrinsicLogWarping_even :
    Function.Even (intrinsicLogWarping g hrotation hcomplete) := by
  intro s
  exact congrArg Real.log (intrinsicWarpingQuotient_even g hrotation hcomplete s)

theorem intrinsicLogWarping_zero : intrinsicLogWarping g hrotation hcomplete 0 = 0 := by
  simp only [intrinsicLogWarping, intrinsicWarpingQuotient_zero, Real.log_one]


theorem intrinsicWarpingRadius_eq_exp (s : ℝ) :
    intrinsicWarpingRadius g hrotation hcomplete s =
      s * Real.exp (intrinsicLogWarping g hrotation hcomplete s) := by
  rw [intrinsicLogWarping,
    Real.exp_log (intrinsicWarpingQuotient_pos g hrotation hcomplete s)]
  exact (mul_intrinsicWarpingQuotient g hrotation hcomplete s).symm



theorem intrinsicLogWarping_contDiff_norm {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ContDiff ℝ ∞ (fun x : E => intrinsicLogWarping g hrotation hcomplete ‖x‖) :=
  contDiff_even_norm (intrinsicLogWarping_contDiff g hrotation hcomplete)
    (intrinsicLogWarping_even g hrotation hcomplete)


theorem intrinsicLogWarping_gradient_coefficient_contDiff_norm {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ContDiff ℝ ∞ (fun x : E =>
      axisDivision (deriv (intrinsicLogWarping g hrotation hcomplete)) ‖x‖) :=
  contDiff_even_norm
    (axisDivision_contDiff
      (contDiff_infty_iff_deriv.mp (intrinsicLogWarping_contDiff g hrotation hcomplete)).2)
    (axisDivision_deriv_even (intrinsicLogWarping_contDiff g hrotation hcomplete)
      (intrinsicLogWarping_even g hrotation hcomplete))

end PoincareConjecture.M35.Uniqueness
