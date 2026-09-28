import PoincareConjecture.Proofs.M14.Sec6_5_PositiveStartHessian
import PoincareConjecture.Proofs.M14.Sec6_5_AdaptedIndexIntegral
import PoincareConjecture.Proofs.M14.Sec6_5_HorizontalHessianTrace









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}





theorem positiveStart_laplacian_bound
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hp : M14IsMinimizing p) (R : M14SquareRootPath G p)
    (U : Set G.Point) (hU : IsOpen U) (hy : y ∈ U)
    (hf : ContMDiffOn (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (M14ReducedLengthAt G T a x) U)
    (hq : G.spacetime.timeFunction (R.curve (Real.sqrt b)) = T - b) :
    M14ReducedLengthLaplacian (τ₁ := a) G x ⟨R.curve (Real.sqrt b), hq⟩ ≤
      (n : ℝ) / (2 * Real.sqrt b * (Real.sqrt b - Real.sqrt a)) -
        horizontalScalarCurvature G.leafwise (R.curve (Real.sqrt b)) -
        (∫ t in a..b, Real.sqrt t * (Real.sqrt t - Real.sqrt a) ^ 2 *
          M14GeneralizedHarnackDensity G p
            (fun r => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
              (p.curve r)) t) /
          (2 * Real.sqrt b * (Real.sqrt b - Real.sqrt a) ^ 2) := by
  classical
  let q : (G.slices (T - b)).Point := ⟨R.curve (Real.sqrt b), hq⟩
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have hb : 0 < b := p.tau_nonneg.trans_lt p.tau_lt
  have hs : Real.sqrt b ∈ M14SqrtParameterInterval a b := ⟨hab.le, le_rfl⟩
  have hpoint : R.curve (Real.sqrt b) = y := by
    rw [R.agrees _ hs, Real.sq_sqrt hb.le, p.curve_end]
  have hRU : R.curve (Real.sqrt b) ∈ U := by rwa [hpoint]
  have hsmooth : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun r : (G.slices (T - b)).Point => M14ReducedLengthAt G T a x r.val) q := by
    have hi : ContMDiff (𝓡 n) (spacetimeModel n) ∞
        (fun r : (G.slices (T - b)).Point => r.val) := (G.slices (T - b)).inclusion_smooth
    exact ((hf _ hRU).contMDiffAt (hU.mem_nhds hRU)).comp q hi.contMDiffAt
  obtain ⟨P, hP, horth, hbas⟩ := exists_horizontalUnitAdaptedFrame R hM04 hM12
  let EP := fun i => Classical.choose (hP i).equation
  obtain ⟨B, hB⟩ := hbas (Real.sqrt b) hs
  let Y := fun i => horizontalAdaptedField (Real.sqrt a) (Real.sqrt b) (P i)
  have hYleft (i : Fin n) : Y i (Real.sqrt a) = 0 :=
    (horizontalAdaptedField_endpoints hab).1
  have hYright (i : Fin n) : Y i (Real.sqrt b) = B i :=
    (horizontalAdaptedField_endpoints hab).2.trans (hB i).symm
  have htrace := reducedLengthLaplacian_eq_horizontal_hessian_trace x q hsmooth B (by
    intro i j
    simpa only [hB i, hB j] using horth (Real.sqrt b) hs i j)
  have hbound (i : Fin n) := positiveStart_hessian_le_pullback_index hCoordinates hM04 hM12
    hp U hU hy hf hq (horizontalAdaptedExtension (EP i)) (hYleft i)
  obtain ⟨E⟩ := exists_squareRoot_velocity_extension R
  have hK := squareRoot_weightedHarnack_intervalIntegrable hM12 R E (by
    intro r hr W
    exact squareRootEulerResidual_eq_zero_of_minimizing hCoordinates hM12 hp E
      (Ioo_subset_Icc_self hr) W)
  have hsum := integral_adaptedPullbackIndex R hM04 hM12 P hP EP horth hK
  rw [htrace]
  calc
    _ = ∑ i, M14ReducedLengthHessianPairing G q (M14ReducedLengthAt G T a x)
        (Y i (Real.sqrt b)) (Y i (Real.sqrt b)) := by simp only [hYright]
    _ ≤ ∑ i, (∫ r in Real.sqrt a..Real.sqrt b, pullbackIndexPairDensity R
        (horizontalAdaptedExtension (EP i)) (horizontalAdaptedExtension (EP i)) r) /
          (2 * Real.sqrt b) := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (∑ i, ∫ r in Real.sqrt a..Real.sqrt b, pullbackIndexPairDensity R
        (horizontalAdaptedExtension (EP i)) (horizontalAdaptedExtension (EP i)) r) /
          (2 * Real.sqrt b) := (Finset.sum_div _ _ _).symm
    _ = _ := by
      rw [hsum]
      field_simp [(Real.sqrt_pos.mpr hb).ne', sub_ne_zero.mpr hab.ne']

end PoincareConjecture.M14
