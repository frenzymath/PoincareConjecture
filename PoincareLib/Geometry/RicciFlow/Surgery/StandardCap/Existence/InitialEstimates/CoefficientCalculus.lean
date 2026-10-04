import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialEstimates.Connection
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialEstimates.RadialLength

/-!
# Weighted radial metric coefficients in terms of the warping function

Morgan-Tian Lemma 12.3, pp. 294-295. The radial speed a and warping
function f recover the supplied metric coefficients as a^2 and f^2/r^2.
Differentiating these genuine smooth functions gives rational formulas
for the supplied connection, away from the origin. See the independent
weighted-radial-positivity derivation and its source review.
-/

set_option autoImplicit false

open Filter
open scoped Topology ContDiff

namespace PoincareMT.M34

/-- The squared radial speed is the radial metric coefficient
(Lemma 12.3 calculation, pp. 294-295). -/
theorem initialRadialCoefficient_eq (g₀ : StandardInitialMetric) (r : ℝ) :
    initialRadialCoefficient g₀ r = initialRadialSpeed g₀ r ^ 2 :=
  (Real.sq_sqrt (initialCoefficients_pos g₀ r).1.le).symm

/-- The warping radius recovers the angular metric coefficient at
nonzero radii (Lemma 12.3 calculation, pp. 294-295). -/
theorem initialAngularCoefficient_eq (g₀ : StandardInitialMetric) {r : ℝ} (hr : r ≠ 0) :
    initialAngularCoefficient g₀ r = initialWarping g₀ r ^ 2 / r ^ 2 := by
  unfold initialWarping
  rw [mul_pow, Real.sq_sqrt (initialCoefficients_pos g₀ r).2.le]
  field_simp

/-- Derivative of the radial metric coefficient in terms of its speed
(Lemma 12.3 calculation, pp. 294-295). -/
theorem initialRadialCoefficient_hasDerivAt (g₀ : StandardInitialMetric) (r : ℝ) :
    HasDerivAt (initialRadialCoefficient g₀)
      (2 * initialRadialSpeed g₀ r * deriv (initialRadialSpeed g₀) r) r := by
  have h := (((initialRadialSpeed_contDiff g₀).differentiable (by simp)) r).hasDerivAt.pow 2
  have he : initialRadialCoefficient g₀ = fun s => initialRadialSpeed g₀ s ^ 2 :=
    funext (initialRadialCoefficient_eq g₀)
  rw [he]
  convert! h using 1
  norm_num

/-- Derivative of the angular metric coefficient at nonzero radius
(Lemma 12.3 curvature computation, pp. 294-295). -/
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

/-- Derivative of the rank-one metric coefficient with radial speed
retained (Lemma 12.3 curvature computation, pp. 294-295). -/
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

/-- The first connection coefficient in weighted warping variables
(Lemma 12.3 curvature computation, pp. 294-295). -/
theorem initialChristoffelA_eq (g₀ : StandardInitialMetric) {r : ℝ}
    (hr : r ≠ 0) (hf : initialWarping g₀ r ≠ 0) :
    initialChristoffelA g₀ r =
      deriv (initialWarping g₀) r / (r * initialWarping g₀ r) - 1 / r ^ 2 := by
  rw [initialChristoffelA, (initialAngularCoefficient_hasDerivAt g₀ hr).deriv,
    initialAngularCoefficient_eq g₀ hr]
  field_simp

/-- The second connection coefficient in weighted warping variables
(Lemma 12.3 curvature computation, pp. 294-295). -/
theorem initialChristoffelB_eq (g₀ : StandardInitialMetric) {r : ℝ} (hr : r ≠ 0) :
    initialChristoffelB g₀ r = 1 / r ^ 2 -
      initialWarping g₀ r * deriv (initialWarping g₀) r /
        (initialRadialSpeed g₀ r ^ 2 * r ^ 3) := by
  have ha := (initialRadialSpeed_pos g₀ r).ne'
  rw [initialChristoffelB, (initialAngularCoefficient_hasDerivAt g₀ hr).deriv,
    initialRankOneCoefficient, initialRadialCoefficient_eq, initialAngularCoefficient_eq g₀ hr]
  field_simp
  ring

/-- Radial speed determines the third connection coefficient
(Lemma 12.3 curvature computation, pp. 294-295). -/
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

end PoincareMT.M34
