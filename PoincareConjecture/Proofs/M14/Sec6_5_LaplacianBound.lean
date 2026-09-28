import PoincareConjecture.Proofs.M14.Sec6_5_AdaptedIndexIntegral
import PoincareConjecture.Proofs.M14.Sec6_5_RegularHessian
import PoincareConjecture.Proofs.M14.Sec6_5_HorizontalHessianTrace

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem exponential_weightedHarnack_intervalIntegrable
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {s : ℝ} (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) :
    IntervalIntegrable (fun t => t * Real.sqrt t *
      M14GeneralizedHarnackDensity G (E.path Z s hs hpos)
        (fun r => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
          ((E.path Z s hs hpos).curve r)) t) MeasureTheory.volume 0 (s ^ 2) := by
  apply squareRoot_weightedHarnack_intervalIntegrable hM12 (E.square_path Z s hs hpos)
    (E.square_extension Z s hs hpos)
  intro r hr
  apply E.square_euler Z s hs hpos r
  simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using Ioo_subset_Icc_self hr

theorem reducedLengthLaplacian_joint_bound
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) (hz : (Z, s) ∈ M14JointDomain G E)
    (hpoint : (E.square_path Z s hs hpos).curve s = E.gamma Z s)
    (hq : G.spacetime.timeFunction ((E.square_path Z s hs hpos).curve s) = T - s ^ 2) :
    M14ReducedLengthLaplacian (τ₁ := 0) G x
        ⟨(E.square_path Z s hs hpos).curve s, hq⟩ ≤
      (n : ℝ) / (2 * s ^ 2) -
        horizontalScalarCurvature G.leafwise ((E.square_path Z s hs hpos).curve s) -
        M14GeneralizedKIntegral G (E.path Z s hs hpos)
          (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
            ((E.path Z s hs hpos).curve t)) / (2 * s ^ 2 * Real.sqrt (s ^ 2)) := by
  classical
  let R := E.square_path Z s hs hpos
  let H := M14GeneralizedHarnackDensity G (E.path Z s hs hpos)
    (fun r => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
      ((E.path Z s hs hpos).curve r))
  let q : (G.slices (T - s ^ 2)).Point := ⟨R.curve s, hq⟩
  have hsC : s ∈ M14SqrtParameterInterval 0 (s ^ 2) := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hpos.le] using
      (show s ∈ Icc 0 s from ⟨hpos.le, le_rfl⟩)
  obtain ⟨P, hP, horth, hb⟩ := exists_horizontalUnitAdaptedFrame R hM04 hM12
  let EP := fun i => Classical.choose (hP i).equation
  obtain ⟨b, hb⟩ := hb s hsC
  let Y := fun i => horizontalAdaptedField (Real.sqrt 0) (Real.sqrt (s ^ 2)) (P i)
  have hY0 (i : Fin n) : Y i 0 = 0 := by
    simp only [Y, horizontalAdaptedField, Real.sqrt_zero, sub_self, zero_div, zero_smul]
  have hYs (i : Fin n) : Y i s = b i := by
    simp only [Y, horizontalAdaptedField, Real.sqrt_zero, Real.sqrt_sq hpos.le, sub_zero,
      div_self hpos.ne', one_smul, hb i]
  have hqimage : q.val ∈ range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2) := by
    change R.curve s ∈ _
    rw [show R.curve s = E.gamma Z s from hpoint]
    exact ⟨⟨(Z, s), hz⟩, rfl⟩
  have htrace := reducedLengthLaplacian_eq_horizontal_hessian_trace x q
    (reducedLengthAt_slice_contMDiffAt hM04 hM12 E q hqimage) b (by
      intro i j
      simpa only [hb i, hb j] using horth s hsC i j)
  have hbound (i : Fin n) := reducedLengthHessian_joint_le_index hCoordinates hM04 hM12
    E hs hpos hz hpoint hq (horizontalAdaptedExtension (EP i)) (hY0 i)
  have hKshift : (∫ t in 0..s ^ 2, Real.sqrt t * (Real.sqrt t - Real.sqrt 0) ^ 2 * H t) =
      M14GeneralizedKIntegral G (E.path Z s hs hpos)
        (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
          ((E.path Z s hs hpos).curve t)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (sq_nonneg s)
    intro t ht
    simp only [Real.sqrt_zero, sub_zero, Real.sq_sqrt ht.1.le]
    exact mul_right_comm _ _ _ |>.trans (by dsimp only [H]; ring)
  let J := fun i => pullbackIndexPairDensity R (horizontalAdaptedExtension (EP i))
    (horizontalAdaptedExtension (EP i))
  have hsum := integral_adaptedPullbackIndex R hM04 hM12 P hP EP horth
    (exponential_weightedHarnack_intervalIntegrable hM12 E hs hpos)
  change (∑ i, ∫ r in Real.sqrt 0..Real.sqrt (s ^ 2), J i r) =
    (n : ℝ) / (Real.sqrt (s ^ 2) - Real.sqrt 0) -
      2 * Real.sqrt (s ^ 2) * horizontalScalarCurvature G.leafwise
        (R.curve (Real.sqrt (s ^ 2))) -
      (∫ t in 0..s ^ 2, Real.sqrt t * (Real.sqrt t - Real.sqrt 0) ^ 2 * H t) /
        (Real.sqrt (s ^ 2) - Real.sqrt 0) ^ 2 at hsum
  rw [hKshift, Real.sqrt_zero, Real.sqrt_sq hpos.le, sub_zero] at hsum
  rw [htrace]
  calc
    _ = ∑ i, M14ReducedLengthHessianPairing G q (M14ReducedLengthAt G T 0 x)
        (Y i s) (Y i s) := by simp only [hYs]
    _ ≤ ∑ i, (∫ r in 0..s, pullbackIndexPairDensity R
        (horizontalAdaptedExtension (EP i)) (horizontalAdaptedExtension (EP i)) r) /
          (2 * s) := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (∑ i, ∫ r in 0..s, pullbackIndexPairDensity R
        (horizontalAdaptedExtension (EP i)) (horizontalAdaptedExtension (EP i)) r) /
          (2 * s) := (Finset.sum_div _ _ _).symm
    _ = _ := by
      rw [hsum, Real.sqrt_sq hpos.le]
      field_simp [hpos.ne']
      ring

end PoincareConjecture.M14
