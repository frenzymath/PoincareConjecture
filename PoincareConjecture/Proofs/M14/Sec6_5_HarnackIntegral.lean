import PoincareConjecture.Proofs.M14.Sec6_5_HarnackIntegrability
import PoincareConjecture.Proofs.M14.Sec6_1_SquareRootAction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}



noncomputable def squareHarnackPrimitive (R : M14SquareRootPath G p) (s : ℝ) : ℝ :=
  s ^ 3 * horizontalScalarCurvature G.leafwise (R.curve s) +
    s * G.spacetime.horizontalMetric.inner (R.curve s)
      (R.horizontal_velocity s) (R.horizontal_velocity s) / 4



theorem squareHarnackPrimitive_contDiffOn
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (R : M14SquareRootPath G p) :
    ContDiffOn ℝ ∞ (squareHarnackPrimitive R) (M14SqrtParameterInterval τ₁ τ₂) :=
  ((contDiffOn_id.pow 3).mul (squareRoot_scalar_contDiffOn hM12 R)).add
    ((contDiffOn_id.mul (squareRoot_energy_contDiffOn R)).div_const 4)



theorem squareHarnackPrimitive_derivWithin
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (R : M14SquareRootPath G p)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    derivWithin (squareHarnackPrimitive R) (M14SqrtParameterInterval τ₁ τ₂) s =
      3 * s ^ 2 * horizontalScalarCurvature G.leafwise (R.curve s) +
        s ^ 3 * derivWithin (fun r => horizontalScalarCurvature G.leafwise (R.curve r))
          (M14SqrtParameterInterval τ₁ τ₂) s +
        (G.spacetime.horizontalMetric.inner (R.curve s)
          (R.horizontal_velocity s) (R.horizontal_velocity s) +
          s * derivWithin (fun r => G.spacetime.horizontalMetric.inner (R.curve r)
            (R.horizontal_velocity r) (R.horizontal_velocity r))
            (M14SqrtParameterInterval τ₁ τ₂) s) / 4 := by
  have hC := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)
  have hSd := (squareRoot_scalar_contDiffOn hM12 R).differentiableOn (by simp) s hs
  have hEd := (squareRoot_energy_contDiffOn R).differentiableOn (by simp) s hs
  have hS := hSd.hasDerivWithinAt
  have hE := hEd.hasDerivWithinAt
  have h := (((hasDerivWithinAt_pow 3 s).mul hS).add
    (((hasDerivWithinAt_id s _).mul hE).div_const 4)).derivWithin (hC s hs)
  change derivWithin (fun r => r ^ 3 * horizontalScalarCurvature G.leafwise (R.curve r) +
    r * G.spacetime.horizontalMetric.inner (R.curve r)
      (R.horizontal_velocity r) (R.horizontal_velocity r) / 4) _ s = _
  simpa only [Pi.add_def, Pi.mul_def, Nat.cast_ofNat, Nat.reduceSub, one_mul, id_eq] using h



theorem squareRoot_harnackIntegral_eq
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (R : M14SquareRootPath G p)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      R.horizontal_velocity)
    (hEuler : ∀ s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂),
      ∀ W, M14SquareRootEulerResidual G R E s W = 0) :
    M14GeneralizedKIntegral G p
        (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
          (p.curve t)) =
      M14BackwardLAction G p / 2 - squareHarnackPrimitive R (Real.sqrt τ₂) +
        squareHarnackPrimitive R (Real.sqrt τ₁) := by
  let C := M14SqrtParameterInterval τ₁ τ₂
  have hle : Real.sqrt τ₁ ≤ Real.sqrt τ₂ := Real.sqrt_le_sqrt p.tau_lt.le
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)
  have hP := squareHarnackPrimitive_contDiffOn hM12 R
  have hPi : IntervalIntegrable (derivWithin (squareHarnackPrimitive R) C)
      MeasureTheory.volume (Real.sqrt τ₁) (Real.sqrt τ₂) :=
    ((hP.derivWithin hC (m := ∞) (by simp)).continuousOn).intervalIntegrable_of_Icc hle
  have hFTC : (∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
      derivWithin (squareHarnackPrimitive R) C s) =
        squareHarnackPrimitive R (Real.sqrt τ₂) -
          squareHarnackPrimitive R (Real.sqrt τ₁) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hP.continuousOn _ hPi
    intro s hs
    have hd := (hP.differentiableOn (by simp) s (Ioo_subset_Icc_self hs)).hasDerivWithinAt
    exact hd.hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  let H := M14GeneralizedHarnackDensity G p
    (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise) (p.curve t))
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := Real.sqrt τ₁) (b := Real.sqrt τ₂)
    (f := fun s : ℝ => s ^ 2) (f' := fun s => 2 * s)
    (g := fun t => t * Real.sqrt t * H t) (continuous_pow 2).continuousOn
    (fun s _ => by simpa using hasDerivAt_pow 2 s)
    (fun s hs => by
      rw [min_eq_left hle, max_eq_right hle] at hs
      exact mul_nonneg (by norm_num) ((Real.sqrt_nonneg τ₁).trans hs.1.le))
  rw [Real.sq_sqrt p.tau_nonneg, Real.sq_sqrt (p.tau_nonneg.trans p.tau_lt.le)] at hchange
  change (∫ t in τ₁..τ₂, t * Real.sqrt t * H t) = _
  rw [← hchange]
  calc
    (∫ s in Real.sqrt τ₁..Real.sqrt τ₂, (s ^ 2 * Real.sqrt (s ^ 2) * H (s ^ 2)) * (2 * s)) =
        ∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
          (squareRootLIntegrand R s / 2 - derivWithin (squareHarnackPrimitive R) C s) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hle
      intro s hs
      have hs0 : 0 < s := (Real.sqrt_nonneg τ₁).trans_lt hs.1
      dsimp only
      rw [Real.sqrt_sq hs0.le, squareHarnackPrimitive_derivWithin hM12 R (Ioo_subset_Icc_self hs),
        squareRoot_weightedHarnack_eq hM12 R E hs (hEuler s hs)]
      unfold squareRootLIntegrand
      ring
    _ = M14BackwardLAction G p / 2 - squareHarnackPrimitive R (Real.sqrt τ₂) +
        squareHarnackPrimitive R (Real.sqrt τ₁) := by
      rw [intervalIntegral.integral_sub ((squareRootLIntegrand_intervalIntegrable R).div_const 2)
        hPi, intervalIntegral.integral_div, integral_squareRootLIntegrand_eq_action R, hFTC]
      ring



theorem squareRoot_harnackIntegral_zero_start
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {p : M14BackwardPath G T 0 τ₂ x y}
    (R : M14SquareRootPath G p)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval 0 τ₂)
      R.horizontal_velocity)
    (hEuler : ∀ s ∈ Ioo 0 (Real.sqrt τ₂),
      ∀ W, M14SquareRootEulerResidual G R E s W = 0) :
    M14GeneralizedKIntegral G p
        (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
          (p.curve t)) =
      M14BackwardLAction G p / 2 - squareHarnackPrimitive R (Real.sqrt τ₂) := by
  have h := squareRoot_harnackIntegral_eq hM12 R E (by simpa only [Real.sqrt_zero] using hEuler)
  simpa only [Real.sqrt_zero, squareHarnackPrimitive, zero_pow (by norm_num : 3 ≠ 0),
    zero_mul, zero_div, add_zero] using h

end PoincareConjecture.M14
