import PoincareConjecture.Proofs.M14.Sec6_5_AdaptedIndexHarnack
import PoincareConjecture.Proofs.M14.Sec6_5_ShiftedHarnack
import PoincareConjecture.Proofs.M14.Sec6_5_ScalarEvolutionTransport
import PoincareConjecture.Proofs.M14.Sec6_4_IndexJacobi
import PoincareConjecture.Proofs.M04

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  (R : M14SquareRootPath G p)

theorem integral_adaptedPullbackIndex (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (P : Fin n → ∀ s, G.Horizontal (R.curve s))
    (hP : ∀ i, IsHorizontalUnitAdaptedFieldOn R (Real.sqrt a) (Real.sqrt b) (P i))
    (EP : ∀ i, M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) (P i))
    (horth : ∀ s ∈ M14SqrtParameterInterval a b, ∀ i j,
      G.spacetime.horizontalMetric.inner (R.curve s) (P i s) (P j s) =
        if i = j then 1 else 0)
    (hK : IntervalIntegrable (fun t => t * Real.sqrt t * M14GeneralizedHarnackDensity G p
      (fun r => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
        (p.curve r)) t) MeasureTheory.volume a b) :
    (∑ i, ∫ s in Real.sqrt a..Real.sqrt b,
      pullbackIndexPairDensity R (horizontalAdaptedExtension (EP i))
        (horizontalAdaptedExtension (EP i)) s) =
      (n : ℝ) / (Real.sqrt b - Real.sqrt a) -
        2 * Real.sqrt b * horizontalScalarCurvature G.leafwise (R.curve (Real.sqrt b)) -
        (∫ t in a..b, Real.sqrt t * (Real.sqrt t - Real.sqrt a) ^ 2 *
          M14GeneralizedHarnackDensity G p
            (fun r => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
              (p.curve r)) t) / (Real.sqrt b - Real.sqrt a) ^ 2 := by
  let H := M14GeneralizedHarnackDensity G p
    (fun r => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise) (p.curve r))
  let J : Fin n → ℝ → ℝ := fun i => pullbackIndexPairDensity R
    (horizontalAdaptedExtension (EP i)) (horizontalAdaptedExtension (EP i))
  let B := derivWithin (adaptedScalarPrimitive R) (M14SqrtParameterInterval a b)
  let Q : ℝ → ℝ := fun s => 2 * s ^ 2 * (s - Real.sqrt a) ^ 2 * H (s ^ 2)
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have hd : Real.sqrt b - Real.sqrt a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  have hJ (i : Fin n) : IntervalIntegrable (J i) MeasureTheory.volume
      (Real.sqrt a) (Real.sqrt b) :=
    (pullbackIndexPairDensity_contDiffOn R
      (jacobiFieldDataOfExtension hCoordinates (horizontalAdaptedExtension (EP i)))
      (horizontalAdaptedExtension (EP i)) hM04 hM12).continuousOn.intervalIntegrable_of_Icc hab.le
  have hC := uniqueDiffOn_Icc hab
  have hB : IntervalIntegrable B MeasureTheory.volume (Real.sqrt a) (Real.sqrt b) :=
    (((adaptedScalarPrimitive_contDiffOn hM12 R).derivWithin hC (m := ∞)
      (by simp)).continuousOn).intervalIntegrable_of_Icc hab.le
  have hQ : IntervalIntegrable Q MeasureTheory.volume (Real.sqrt a) (Real.sqrt b) :=
    shiftedHarnack_square_intervalIntegrable p.tau_nonneg p.tau_lt H hK
  have hpoint (s : ℝ) (hs : s ∈ Ioo (Real.sqrt a) (Real.sqrt b)) :
      (∑ i, J i s) = ((n : ℝ) - B s - Q s) / (Real.sqrt b - Real.sqrt a) ^ 2 :=
    adaptedPullbackIndex_harnack R ricciFlowCurvatureTheory hM12 P hP EP hs
      (horth s (Ioo_subset_Icc_self hs)) (backwardScalarEvolution hM04 hM12 (R.curve s))
  have hBi : (∫ s in Real.sqrt a..Real.sqrt b, B s) =
      2 * Real.sqrt b * (Real.sqrt b - Real.sqrt a) ^ 2 *
        horizontalScalarCurvature G.leafwise (R.curve (Real.sqrt b)) :=
    integral_adaptedScalarPrimitive_derivWithin hM12 R
  have hQi : (∫ s in Real.sqrt a..Real.sqrt b, Q s) =
      ∫ t in a..b, Real.sqrt t * (Real.sqrt t - Real.sqrt a) ^ 2 * H t :=
    (shiftedHarnack_integral_square p.tau_nonneg p.tau_lt H).symm
  calc
    _ = ∫ s in Real.sqrt a..Real.sqrt b, ∑ i, J i s :=
      (intervalIntegral.integral_finsetSum (fun i _ => hJ i)).symm
    _ = ∫ s in Real.sqrt a..Real.sqrt b,
        ((n : ℝ) - B s - Q s) / (Real.sqrt b - Real.sqrt a) ^ 2 :=
      intervalIntegral.integral_congr_Ioo_of_le hab.le hpoint
    _ = _ := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_sub (intervalIntegrable_const.sub hB) hQ,
        intervalIntegral.integral_sub intervalIntegrable_const hB,
        intervalIntegral.integral_const, hBi, hQi]
      simp only [smul_eq_mul]
      field_simp [hd]
      rfl

end PoincareConjecture.M14
