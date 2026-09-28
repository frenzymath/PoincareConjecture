import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.Connection
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.RadialLength

set_option autoImplicit false

open Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M34

theorem initialRadialCoefficient_eq (g₀ : StandardInitialMetric) (r : ℝ) :
    initialRadialCoefficient g₀ r = initialRadialSpeed g₀ r ^ 2 :=
  (Real.sq_sqrt (initialCoefficients_pos g₀ r).1.le).symm

theorem initialAngularCoefficient_eq (g₀ : StandardInitialMetric) {r : ℝ} (hr : r ≠ 0) :
    initialAngularCoefficient g₀ r = initialWarping g₀ r ^ 2 / r ^ 2 := by
  unfold initialWarping
  rw [mul_pow, Real.sq_sqrt (initialCoefficients_pos g₀ r).2.le]
  field_simp

theorem initialRadialCoefficient_hasDerivAt (g₀ : StandardInitialMetric) (r : ℝ) :
    HasDerivAt (initialRadialCoefficient g₀)
      (2 * initialRadialSpeed g₀ r * deriv (initialRadialSpeed g₀) r) r := by
  have h := (((initialRadialSpeed_contDiff g₀).differentiable (by simp)) r).hasDerivAt.pow 2
  have he : initialRadialCoefficient g₀ = fun s => initialRadialSpeed g₀ s ^ 2 :=
    funext (initialRadialCoefficient_eq g₀)
  rw [he]
  convert! h using 1
  norm_num

theorem initialAngularCoefficient_hasDerivAt (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (initialAngularCoefficient g₀)
      (2 * initialWarping g₀ r * (r * deriv (initialWarping g₀) r -
        initialWarping g₀ r) / r ^ 3) r := by
  have he : initialAngularCoefficient g₀ =ᶠ[𝓝 r]
      (fun s => initialWarping g₀ s ^ 2 / s ^ 2) := by
    filter_upwards [eventually_ne_nhds hr] with s hs
    exact initialAngularCoefficient_eq g₀ hs
  have hf := (((initialWarping_contDiff g₀).differentiable (by simp)) r).hasDerivAt
  have h := (hf.pow 2).div ((hasDerivAt_id r).pow 2) (pow_ne_zero 2 hr)
  convert! h.congr_of_eventuallyEq he using 1
  simp only [Pi.pow_apply, id_eq, Nat.reduceSub, pow_one]
  field_simp
  ring

theorem initialRankOneCoefficient_hasDerivAt (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (initialRankOneCoefficient g₀)
      ((2 * initialRadialSpeed g₀ r * deriv (initialRadialSpeed g₀) r * r ^ 3 -
        2 * initialRadialSpeed g₀ r ^ 2 * r ^ 2 -
        2 * r * initialWarping g₀ r * deriv (initialWarping g₀) r +
        4 * initialWarping g₀ r ^ 2) / r ^ 5) r := by
  have h := ((initialRadialCoefficient_hasDerivAt g₀ r).sub
    (initialAngularCoefficient_hasDerivAt g₀ hr)).div ((hasDerivAt_id r).pow 2)
      (pow_ne_zero 2 hr)
  convert! h using 1
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq, Nat.reduceSub, pow_one]
  rw [initialRadialCoefficient_eq, initialAngularCoefficient_eq g₀ hr]
  field_simp
  ring

theorem initialChristoffelA_eq (g₀ : StandardInitialMetric) {r : ℝ}
    (hr : r ≠ 0) (hf : initialWarping g₀ r ≠ 0) :
    initialChristoffelA g₀ r =
      deriv (initialWarping g₀) r / (r * initialWarping g₀ r) - 1 / r ^ 2 := by
  rw [initialChristoffelA, (initialAngularCoefficient_hasDerivAt g₀ hr).deriv,
    initialAngularCoefficient_eq g₀ hr]
  field_simp

theorem initialChristoffelB_eq (g₀ : StandardInitialMetric) {r : ℝ} (hr : r ≠ 0) :
    initialChristoffelB g₀ r = 1 / r ^ 2 -
      initialWarping g₀ r * deriv (initialWarping g₀) r /
        (initialRadialSpeed g₀ r ^ 2 * r ^ 3) := by
  have ha := (initialRadialSpeed_pos g₀ r).ne'
  rw [initialChristoffelB, (initialAngularCoefficient_hasDerivAt g₀ hr).deriv,
    initialRankOneCoefficient, initialRadialCoefficient_eq, initialAngularCoefficient_eq g₀ hr]
  field_simp
  ring

theorem initialChristoffelC_eq (g₀ : StandardInitialMetric) {r : ℝ}
    (hr : r ≠ 0) (hf : initialWarping g₀ r ≠ 0) :
    initialChristoffelC g₀ r =
      (deriv (initialRadialSpeed g₀) r / (initialRadialSpeed g₀ r * r) -
        2 * initialChristoffelA g₀ r - initialChristoffelB g₀ r) / r ^ 2 := by
  have ha := (initialRadialSpeed_pos g₀ r).ne'
  rw [initialChristoffelC, (initialRankOneCoefficient_hasDerivAt g₀ hr).deriv,
    initialChristoffelA_eq g₀ hr hf, initialChristoffelB_eq g₀ hr,
    initialRankOneCoefficient, initialRadialCoefficient_eq, initialAngularCoefficient_eq g₀ hr]
  field_simp
  ring

end PoincareConjecture.M34
