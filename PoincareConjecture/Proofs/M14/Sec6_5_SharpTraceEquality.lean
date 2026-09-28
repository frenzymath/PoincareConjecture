import PoincareConjecture.Proofs.M14.Sec6_5_LaplacianBound

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem adaptedIndexIntegral_eq_hessian_of_laplacian_eq
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) (hz : (Z, s) ∈ M14JointDomain G E)
    (hpoint : (E.square_path Z s hs hpos).curve s = E.gamma Z s)
    (hq : G.spacetime.timeFunction ((E.square_path Z s hs hpos).curve s) = T - s ^ 2)
    (hequality : M14ReducedLengthLaplacian (τ₁ := 0) G x
        ⟨(E.square_path Z s hs hpos).curve s, hq⟩ =
      (n : ℝ) / (2 * s ^ 2) -
        horizontalScalarCurvature G.leafwise ((E.square_path Z s hs hpos).curve s) -
        M14GeneralizedKIntegral G (E.path Z s hs hpos)
          (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
            ((E.path Z s hs hpos).curve t)) / (2 * s ^ 2 * Real.sqrt (s ^ 2)))
    (P : Fin n → ∀ r, G.Horizontal ((E.square_path Z s hs hpos).curve r))
    (hP : ∀ i, IsHorizontalUnitAdaptedFieldOn (E.square_path Z s hs hpos)
      (Real.sqrt 0) (Real.sqrt (s ^ 2)) (P i))
    (EP : ∀ i, M14PullbackExtension G (E.square_path Z s hs hpos).curve
      (M14SqrtParameterInterval 0 (s ^ 2)) (P i))
    (horth : ∀ r ∈ M14SqrtParameterInterval 0 (s ^ 2), ∀ i j,
      G.spacetime.horizontalMetric.inner ((E.square_path Z s hs hpos).curve r)
        (P i r) (P j r) = if i = j then 1 else 0) (i : Fin n) :
    (∫ r in 0..s, pullbackIndexPairDensity (E.square_path Z s hs hpos)
      (horizontalAdaptedExtension (EP i)) (horizontalAdaptedExtension (EP i)) r) =
      (2 * s) * M14ReducedLengthHessianPairing G
        ⟨(E.square_path Z s hs hpos).curve s, hq⟩ (M14ReducedLengthAt G T 0 x)
          (P i s) (P i s) := by
  classical
  let R := E.square_path Z s hs hpos
  let q : (G.slices (T - s ^ 2)).Point := ⟨R.curve s, hq⟩
  let H := M14GeneralizedHarnackDensity G (E.path Z s hs hpos)
    (fun r => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
      ((E.path Z s hs hpos).curve r))
  let J := fun k => pullbackIndexPairDensity R (horizontalAdaptedExtension (EP k))
    (horizontalAdaptedExtension (EP k))
  let L := fun k => M14ReducedLengthHessianPairing G q (M14ReducedLengthAt G T 0 x)
    (P k s) (P k s)
  have hsC : s ∈ M14SqrtParameterInterval 0 (s ^ 2) := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hpos.le] using
      (show s ∈ Icc 0 s from ⟨hpos.le, le_rfl⟩)
  obtain ⟨b, hb⟩ := horizontalBasis_of_orthonormal (R.curve s) (fun k => P k s)
    (horth s hsC)
  have hqimage : q.val ∈ range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2) := by
    change R.curve s ∈ _
    rw [show R.curve s = E.gamma Z s from hpoint]
    exact ⟨⟨(Z, s), hz⟩, rfl⟩
  have htrace := reducedLengthLaplacian_eq_horizontal_hessian_trace x q
    (reducedLengthAt_slice_contMDiffAt hM04 hM12 E q hqimage) b (by
      intro k j
      simpa only [hb k, hb j] using horth s hsC k j)
  have htrace' : (∑ k, L k) = M14ReducedLengthLaplacian (τ₁ := 0) G x q := by
    simpa only [L, hb] using htrace.symm
  have hbound (k : Fin n) : L k ≤ (∫ r in 0..s, J k r) / (2 * s) := by
    have hY0 : horizontalAdaptedField (Real.sqrt 0) (Real.sqrt (s ^ 2)) (P k) 0 = 0 := by
      simp only [horizontalAdaptedField, Real.sqrt_zero, sub_self, zero_div, zero_smul]
    have h := reducedLengthHessian_joint_le_index hCoordinates hM04 hM12
      E hs hpos hz hpoint hq (horizontalAdaptedExtension (EP k)) hY0
    have hYs : horizontalAdaptedField (Real.sqrt 0) (Real.sqrt (s ^ 2)) (P k) s = P k s := by
      simp only [horizontalAdaptedField, Real.sqrt_zero, Real.sqrt_sq hpos.le, sub_zero,
        div_self hpos.ne', one_smul]
    simpa only [hYs] using h
  have hKshift : (∫ t in 0..s ^ 2, Real.sqrt t * (Real.sqrt t - Real.sqrt 0) ^ 2 * H t) =
      M14GeneralizedKIntegral G (E.path Z s hs hpos)
        (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
          ((E.path Z s hs hpos).curve t)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (sq_nonneg s)
    intro t ht
    simp only [Real.sqrt_zero, sub_zero, Real.sq_sqrt ht.1.le]
    exact mul_right_comm _ _ _ |>.trans (by dsimp only [H]; ring)
  have hsum := integral_adaptedPullbackIndex R hM04 hM12 P hP EP horth
    (exponential_weightedHarnack_intervalIntegrable hM12 E hs hpos)
  change (∑ k, ∫ r in Real.sqrt 0..Real.sqrt (s ^ 2), J k r) =
    (n : ℝ) / (Real.sqrt (s ^ 2) - Real.sqrt 0) -
      2 * Real.sqrt (s ^ 2) * horizontalScalarCurvature G.leafwise
        (R.curve (Real.sqrt (s ^ 2))) -
      (∫ t in 0..s ^ 2, Real.sqrt t * (Real.sqrt t - Real.sqrt 0) ^ 2 * H t) /
        (Real.sqrt (s ^ 2) - Real.sqrt 0) ^ 2 at hsum
  rw [hKshift, Real.sqrt_zero, Real.sqrt_sq hpos.le, sub_zero] at hsum
  have htotal : (∑ k, ∫ r in 0..s, J k r) / (2 * s) =
      M14ReducedLengthLaplacian (τ₁ := 0) G x q := by
    rw [hsum, hequality, Real.sqrt_sq hpos.le]
    field_simp [hpos.ne']
    ring
  let D := fun k => (∫ r in 0..s, J k r) / (2 * s) - L k
  have hnonneg (k : Fin n) : 0 ≤ D k := sub_nonneg.mpr (hbound k)
  have hsumD : (∑ k, D k) = 0 := by
    simp only [D, Finset.sum_sub_distrib, ← Finset.sum_div]
    rw [htotal, htrace', sub_self]
  have hzD := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnonneg k)).mp hsumD i
    (Finset.mem_univ i)
  have hfrac : (∫ r in 0..s, J i r) / (2 * s) = L i := sub_eq_zero.mp hzD
  exact ((div_eq_iff (mul_pos zero_lt_two hpos).ne').mp hfrac).trans (mul_comm _ _)

end PoincareConjecture.M14
