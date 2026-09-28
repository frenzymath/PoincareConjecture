import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.ScalarNorms
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.EuclideanModel
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.DomainChange











noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture


def roundCylinderEuclideanBasis : Module.Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.reindex ((finRotate 3).symm)

@[simp] theorem lineModelEquiv_symm_roundCylinderEuclideanBasis (i : Fin 3) :
    (RiemannianMetric.lineModelEquiv 2).symm (roundCylinderEuclideanBasis i) =
      roundCylinderCoordinateBasis i := by
  fin_cases i <;> apply Prod.ext
  all_goals first
  | (ext j; fin_cases j <;> simp [roundCylinderEuclideanBasis,
      RiemannianMetric.lineModelEquiv, roundCylinderCoordinateBasis,
      Poincare.EuclideanSpace.euclideanConsCLE,
      Poincare.EuclideanSpace.euclideanTail, EuclideanSpace.basisFun_apply])
  | simp [roundCylinderEuclideanBasis, RiemannianMetric.lineModelEquiv,
      roundCylinderCoordinateBasis, Poincare.EuclideanSpace.euclideanConsCLE,
      EuclideanSpace.basisFun_apply]


def roundCylinderEuclideanCoefficients (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  (roundCylinderModelCoefficients ((RiemannianMetric.lineModelEquiv 2).symm x)).bilinearComp
    (RiemannianMetric.lineModelEquiv 2).symm.toContinuousLinearMap
    (RiemannianMetric.lineModelEquiv 2).symm.toContinuousLinearMap

theorem roundCylinderEuclideanCoefficients_basis (q : UnitTwoSphere) (s : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) (i j : Fin 3) :
    roundCylinderEuclideanCoefficients x
        (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) =
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x) i j := by
  simp only [roundCylinderEuclideanCoefficients, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.coe_coe, lineModelEquiv_symm_roundCylinderEuclideanBasis,
    roundCylinderModelCoefficients_apply, roundCylinderGram_eq_stereographic_formula,
    sub_zero, mul_one, Prod.fst_add, zero_add]

namespace EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}


def normalizedEuclideanCoefficients (N : EpsilonNeck g) (q : UnitTwoSphere)
    (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  (N.normalizedCenteredCoefficients q
    ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x)).bilinearComp
      (RiemannianMetric.lineModelEquiv 2).symm.toContinuousLinearMap
      (RiemannianMetric.lineModelEquiv 2).symm.toContinuousLinearMap

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem normalizedEuclideanCoefficients_basis_eventuallyEq
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (i j : Fin 3) :
    (fun x => roundCylinderTensorCoefficient N.normalized_pullback
      (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x) i j) =ᶠ[𝓝 0]
    (fun x => N.normalizedEuclideanCoefficients q s x
      (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) := by
  have hcenter : Tendsto
      (fun x => (0, s) + (RiemannianMetric.lineModelEquiv 2).symm x)
      (𝓝 0) (𝓝 (0, s)) := by
    simpa only [Pi.add_def, map_zero, add_zero] using
      (((continuous_const (y := (0, s))).add
        (RiemannianMetric.lineModelEquiv 2).symm.continuous).tendsto
        (0 : EuclideanSpace ℝ (Fin 3)))
  have h := (N.normalizedCenteredCoefficients_basis_eventuallyEq q
    (y := (0, s)) hs i j).comp_tendsto hcenter
  simpa only [Function.comp_def, map_zero, add_zero, normalizedEuclideanCoefficients,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_coe,
    lineModelEquiv_symm_roundCylinderEuclideanBasis] using h



theorem exists_normalizedEuclideanCoefficients_scalar_twoJet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ},
      s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → ∀ r : ℕ, r ≤ 2 → ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ r (fun x =>
        N.normalizedEuclideanCoefficients q s x
            (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
          roundCylinderEuclideanCoefficients x
            (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) 0‖ ≤
        C * N.epsilon := by
  obtain ⟨C, hC, hbound⟩ := exists_normalized_pullback_scalar_twoJet_bound.{u}
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  let A := max 1 ‖T.toContinuousLinearMap‖
  have hA : 1 ≤ A := le_max_left _ _
  refine ⟨C * A ^ 2, mul_pos hC (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hA)), ?_⟩
  intro M _ _ _ _ _ _ _ g N q s hs r hr i j
  have hε := N.epsilon_pos
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
  have h := Poincare.Analysis.Calculus.norm_iteratedFDeriv_comp_continuousLinearEquiv_le
    T (fun p => E ((0, s) + p)) r 0
  simp only [map_zero, iteratedFDeriv_comp_add_left, add_zero] at h
  have hpow : ‖T.toContinuousLinearMap‖ ^ r ≤ A ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) r).trans
      (pow_le_pow_right₀ hA hr)
  exact h.trans ((mul_le_mul (hbound N q hs r hr i j) hpow
    (pow_nonneg (norm_nonneg _) _) (by positivity)).trans_eq (by ring))

end EpsilonNeck
end PoincareConjecture
