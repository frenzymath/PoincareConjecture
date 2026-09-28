import PoincareConjecture.Proofs.M14.Sec6_5_HarnackIntegral

set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}

noncomputable def adaptedScalarPrimitive (R : M14SquareRootPath G p) (s : ℝ) : ℝ :=
  2 * s * (s - Real.sqrt a) ^ 2 * horizontalScalarCurvature G.leafwise (R.curve s)

theorem adaptedScalarPrimitive_contDiffOn
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (R : M14SquareRootPath G p) :
    ContDiffOn ℝ ∞ (adaptedScalarPrimitive R) (M14SqrtParameterInterval a b) :=
  (((contDiffOn_const.mul contDiffOn_id).mul
    ((contDiffOn_id.sub contDiffOn_const).pow 2)).mul (squareRoot_scalar_contDiffOn hM12 R))

theorem adaptedScalarPrimitive_derivWithin
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (R : M14SquareRootPath G p)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval a b) :
    derivWithin (adaptedScalarPrimitive R) (M14SqrtParameterInterval a b) s =
      (2 * (s - Real.sqrt a) ^ 2 + 4 * s * (s - Real.sqrt a)) *
        horizontalScalarCurvature G.leafwise (R.curve s) +
      2 * s * (s - Real.sqrt a) ^ 2 *
        (2 * s * M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise) (R.curve s) +
          M14HorizontalScalarDifferential G (R.curve s) (R.horizontal_velocity s).val) := by
  have hC := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)
  have hpoly : HasDerivAt (fun r : ℝ => 2 * r * (r - Real.sqrt a) ^ 2)
      (2 * (s - Real.sqrt a) ^ 2 + 4 * s * (s - Real.sqrt a)) s := by
    exact (((hasDerivAt_id s).const_mul 2).mul
      (((hasDerivAt_id s).sub_const (Real.sqrt a)).pow 2)).congr_deriv
        (by simp only [id_eq, Pi.pow_apply]; ring)
  exact (hpoly.hasDerivWithinAt.mul (squareRoot_scalar_hasDerivWithinAt hM12 R hs)).derivWithin
    (hC s hs)

theorem integral_adaptedScalarPrimitive_derivWithin
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (R : M14SquareRootPath G p) :
    (∫ s in Real.sqrt a..Real.sqrt b,
      derivWithin (adaptedScalarPrimitive R) (M14SqrtParameterInterval a b) s) =
        2 * Real.sqrt b * (Real.sqrt b - Real.sqrt a) ^ 2 *
          horizontalScalarCurvature G.leafwise (R.curve (Real.sqrt b)) := by
  have hle := Real.sqrt_le_sqrt p.tau_lt.le
  have hC := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)
  have hP := adaptedScalarPrimitive_contDiffOn hM12 R
  have hPi : IntervalIntegrable
      (derivWithin (adaptedScalarPrimitive R) (M14SqrtParameterInterval a b))
      MeasureTheory.volume (Real.sqrt a) (Real.sqrt b) :=
    ((hP.derivWithin hC (m := ∞) (by simp)).continuousOn).intervalIntegrable_of_Icc hle
  have hFTC : (∫ s in Real.sqrt a..Real.sqrt b,
      derivWithin (adaptedScalarPrimitive R) (M14SqrtParameterInterval a b) s) =
        adaptedScalarPrimitive R (Real.sqrt b) - adaptedScalarPrimitive R (Real.sqrt a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hP.continuousOn _ hPi
    intro s hs
    have hd := (hP.differentiableOn (by simp) s (Ioo_subset_Icc_self hs)).hasDerivWithinAt
    exact hd.hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  simpa only [adaptedScalarPrimitive, sub_self, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_mul, sub_zero] using hFTC

end PoincareConjecture.M14
