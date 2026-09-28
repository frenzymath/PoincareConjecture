import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.CoefficientCalculus

set_option autoImplicit false

open Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M34

noncomputable def initialWeightedSlope (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  deriv (initialWarping g₀) r / initialRadialSpeed g₀ r

theorem initialWeightedSlope_contDiff (g₀ : StandardInitialMetric) :
    ContDiff ℝ ∞ (initialWeightedSlope g₀) := by
  exact (initialWarping_contDiff g₀).deriv'.div (initialRadialSpeed_contDiff g₀)
    (fun r => (initialRadialSpeed_pos g₀ r).ne')

theorem initialWeightedSlope_hasDerivAt (g₀ : StandardInitialMetric) (r : ℝ) :
    HasDerivAt (initialWeightedSlope g₀)
      (deriv (deriv (initialWarping g₀)) r / initialRadialSpeed g₀ r -
        deriv (initialWarping g₀) r * deriv (initialRadialSpeed g₀) r /
          initialRadialSpeed g₀ r ^ 2) r := by
  have ha := (initialRadialSpeed_pos g₀ r).ne'
  have hp := ((((initialWarping_contDiff g₀).deriv' (n := ∞)).differentiable
    (by simp)) r).hasDerivAt
  have hd := (((initialRadialSpeed_contDiff g₀).differentiable (by simp)) r).hasDerivAt
  convert! hp.div hd ha using 1
  field_simp

theorem initialChristoffelB_hasDerivAt (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (initialChristoffelB g₀)
      (-2 / r ^ 3 -
        (deriv (initialWarping g₀) r ^ 2 +
          initialWarping g₀ r * deriv (deriv (initialWarping g₀)) r) /
            (initialRadialSpeed g₀ r ^ 2 * r ^ 3) +
        2 * initialWarping g₀ r * deriv (initialWarping g₀) r *
          deriv (initialRadialSpeed g₀) r / (initialRadialSpeed g₀ r ^ 3 * r ^ 3) +
        3 * initialWarping g₀ r * deriv (initialWarping g₀) r /
          (initialRadialSpeed g₀ r ^ 2 * r ^ 4)) r := by
  have ha := (initialRadialSpeed_pos g₀ r).ne'
  have he : initialChristoffelB g₀ =ᶠ[𝓝 r]
      (fun s => 1 / s ^ 2 - initialWarping g₀ s * deriv (initialWarping g₀) s /
        (initialRadialSpeed g₀ s ^ 2 * s ^ 3)) := by
    filter_upwards [eventually_ne_nhds hr] with s hs
    exact initialChristoffelB_eq g₀ hs
  have hf := (((initialWarping_contDiff g₀).differentiable (by simp)) r).hasDerivAt
  have hp := ((((initialWarping_contDiff g₀).deriv' (n := ∞)).differentiable
    (by simp)) r).hasDerivAt
  have hd := (((initialRadialSpeed_contDiff g₀).differentiable (by simp)) r).hasDerivAt
  have h := ((hasDerivAt_const r (1 : ℝ)).div ((hasDerivAt_id r).pow 2)
    (pow_ne_zero 2 hr)).sub ((hf.mul hp).div ((hd.pow 2).mul ((hasDerivAt_id r).pow 3))
      (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 3 hr)))
  convert! h.congr_of_eventuallyEq he using 1
  simp only [Pi.mul_apply, Pi.pow_apply, id_eq, Nat.reduceSub, pow_one]
  field_simp
  ring

theorem initialCurvature_coefficient_F (g₀ : StandardInitialMetric) {r : ℝ}
    (hr : 0 < r) :
    initialChristoffelB g₀ r - initialChristoffelA g₀ r +
        initialChristoffelA g₀ r * initialChristoffelB g₀ r * r ^ 2 =
      (1 - initialWeightedSlope g₀ r ^ 2) / r ^ 2 := by
  have ha := (initialRadialSpeed_pos g₀ r).ne'
  have hf := (initialWarping_pos g₀ hr).ne'
  rw [initialChristoffelA_eq g₀ hr.ne' hf, initialChristoffelB_eq g₀ hr.ne']
  unfold initialWeightedSlope
  field_simp
  ring

theorem initialCurvature_coefficient_radial (g₀ : StandardInitialMetric) {r : ℝ}
    (hr : 0 < r) :
    (initialChristoffelB g₀ r - initialChristoffelA g₀ r +
        initialChristoffelA g₀ r * initialChristoffelB g₀ r * r ^ 2) +
      (deriv (initialChristoffelB g₀) r / r - initialChristoffelC g₀ r +
        initialChristoffelB g₀ r ^ 2 +
          initialChristoffelB g₀ r * initialChristoffelC g₀ r * r ^ 2) * r ^ 2 =
      -initialWarping g₀ r * deriv (initialWeightedSlope g₀) r /
        (initialRadialSpeed g₀ r * r ^ 2) := by
  have ha := (initialRadialSpeed_pos g₀ r).ne'
  have hf := (initialWarping_pos g₀ hr).ne'
  rw [initialChristoffelC_eq g₀ hr.ne' hf,
    initialChristoffelA_eq g₀ hr.ne' hf, initialChristoffelB_eq g₀ hr.ne',
    (initialChristoffelB_hasDerivAt g₀ hr.ne').deriv,
    (initialWeightedSlope_hasDerivAt g₀ r).deriv]
  field_simp
  ring

end PoincareConjecture.M34
