import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.OrdinaryJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.Realization







noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem abs_normalized_pullback_scalar_jet_component_le
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (r : ℕ) (hr : r ≤ 2) (i j : Fin 3) (a : Fin r → Fin 3) :
    |iteratedFDeriv ℝ r (fun p =>
      roundCylinderTensorCoefficient N.normalized_pullback
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j -
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j)
        (0, s) (fun k => roundCylinderCoordinateBasis (a k))| ≤
      (if r = 0 then 2 else if r = 1 then 3 else 6) * N.epsilon := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let E := fun p => roundCylinderTensorCoefficient N.normalized_pullback c p i j -
    roundCylinderGram 0 c p i j
  have hN : ContDiffAt ℝ ∞ (fun p =>
      roundCylinderTensorCoefficient N.normalized_pullback c p i j) (0, s) := by
    apply (N.normalized_pullback_close.1 q i j).contDiffAt
    rw [roundCylinder_sphereChart_target]
    exact (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hs⟩
  have hE : ContDiffAt ℝ ∞ E (0, s) :=
    hN.sub (contDiff_roundCylinderGram 0 q i j).contDiffAt
  change |iteratedFDeriv ℝ r E (0, s) _| ≤ _
  interval_cases r
  · simp only [iteratedFDeriv_zero_apply, ite_true]
    exact N.abs_normalized_pullback_metric_component_le_two q hs ![i, j]
  · simp only [iteratedFDeriv_one_apply, show ¬(1 : ℕ) = 0 by decide, ite_false, ite_true]
    dsimp only [E]
    rw [fderiv_fun_sub (hN.differentiableAt (by simp))
      ((contDiff_roundCylinderGram 0 q i j).differentiable (by simp) (0, s)),
      fderiv_roundCylinderGram_center, sub_zero]
    exact N.abs_normalized_pullback_first_derivative_center_le_three q hs (a 0) i j
  · simp only [iteratedFDeriv_two_apply, show ¬(2 : ℕ) = 0 by decide,
      show ¬(2 : ℕ) = 1 by decide, ite_false]
    have h := N.abs_normalized_pullback_second_derivative_center_le_six q hs
      ![a 0, a 1, i, j]
    change |fderiv ℝ (fun p => fderiv ℝ E p (roundCylinderCoordinateBasis (a 1)))
      (0, s) (roundCylinderCoordinateBasis (a 0))| ≤ 6 * N.epsilon at h
    have hEd := (hE.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    rw [fderiv_clm_apply hEd (differentiableAt_const _)] at h
    simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply] using h

theorem abs_normalizedEuclidean_scalar_jet_component_le
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (r : ℕ) (hr : r ≤ 2) (i j : Fin 3) (a : Fin r → Fin 3) :
    |iteratedFDeriv ℝ r (fun x =>
      N.normalizedEuclideanCoefficients q s x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
        roundCylinderEuclideanCoefficients x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) 0
        (fun k => roundCylinderEuclideanBasis (a k))| ≤
      (if r = 0 then 2 else if r = 1 then 3 else 6) * N.epsilon := by
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  let E := fun p => roundCylinderTensorCoefficient N.normalized_pullback
    (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j -
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j
  have heq : (fun x => E ((0, s) + T x)) =ᶠ[𝓝 0]
      (fun x => N.normalizedEuclideanCoefficients q s x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
        roundCylinderEuclideanCoefficients x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) := by
    filter_upwards [N.normalizedEuclideanCoefficients_basis_eventuallyEq q hs i j]
      with x hx
    dsimp only [E, T]
    rw [hx, roundCylinderEuclideanCoefficients_basis q s]
  rw [← (heq.iteratedFDeriv ℝ r).self_of_nhds]
  have h := congrArg (fun L => L (fun k => roundCylinderEuclideanBasis (a k)))
    (Poincare.Analysis.Calculus.iteratedFDeriv_comp_continuousLinearEquiv
      T (fun p => E ((0, s) + p)) r 0)
  simp only [map_zero, iteratedFDeriv_comp_add_left, add_zero,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe,
    T, lineModelEquiv_symm_roundCylinderEuclideanBasis, Function.comp_def] at h
  rw [h]
  exact N.abs_normalized_pullback_scalar_jet_component_le q hs r hr i j a

theorem abs_realization_scalar_jet_component_le
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
    (heq : h.euclideanCoefficients =ᶠ[𝓝 0] N.normalizedEuclideanCoefficients q s)
    (r : ℕ) (hr : r ≤ 2) (i j : Fin 3) (a : Fin r → Fin 3) :
    |iteratedFDeriv ℝ r (fun x => h.inner x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
        roundCylinderEuclideanMetric.inner x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) 0
        (fun k => roundCylinderEuclideanBasis (a k))| ≤
      (if r = 0 then 2 else if r = 1 then 3 else 6) * N.epsilon := by
  have hjet : (fun x => h.inner x (roundCylinderEuclideanBasis i)
      (roundCylinderEuclideanBasis j) -
        roundCylinderEuclideanMetric.inner x (roundCylinderEuclideanBasis i)
          (roundCylinderEuclideanBasis j)) =ᶠ[𝓝 0]
      (fun x => N.normalizedEuclideanCoefficients q s x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
        roundCylinderEuclideanCoefficients x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) := by
    filter_upwards [heq] with x hx
    change h.euclideanCoefficients x _ _ - _ = _
    rw [hx, roundCylinderEuclideanMetric_inner]
  rw [(hjet.iteratedFDeriv ℝ r).self_of_nhds]
  exact N.abs_normalizedEuclidean_scalar_jet_component_le q hs r hr i j a

end PoincareConjecture.EpsilonNeck
