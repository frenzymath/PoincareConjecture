import PoincareConjecture.Proofs.M25.AppA_1_Necks.ScalarJetNorms
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.DomainChange
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.EuclideanModel
import Mathlib.Logic.Equiv.Fin.Rotate











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



noncomputable def m25_roundCylinderEuclideanBasis :
    Module.Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.reindex (finRotate 3).symm



theorem m25_lineModelEquiv_symm_roundCylinderEuclideanBasis (i : Fin 3) :
    (RiemannianMetric.lineModelEquiv 2).symm (m25_roundCylinderEuclideanBasis i) =
      roundCylinderCoordinateBasis i := by
  change (Poincare.EuclideanSpace.euclideanTail (m25_roundCylinderEuclideanBasis i),
    m25_roundCylinderEuclideanBasis i 0) = _
  apply Prod.ext
  · ext j
    fin_cases i <;> fin_cases j <;>
      simp [m25_roundCylinderEuclideanBasis, Module.Basis.reindex_apply, finRotate_apply,
        Poincare.EuclideanSpace.euclideanTail_apply,
        EuclideanSpace.basisFun_apply, roundCylinderCoordinateBasis]
  · fin_cases i <;>
      simp [m25_roundCylinderEuclideanBasis, Module.Basis.reindex_apply, finRotate_apply,
        EuclideanSpace.basisFun_apply, roundCylinderCoordinateBasis]



theorem EpsilonNeck.exists_normalized_pullback_euclidean_scalar_twoJet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ},
      s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → ∀ r : ℕ, r ≤ 2 → ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ r (fun x : EuclideanSpace ℝ (Fin 3) =>
        roundCylinderTensorCoefficient N.normalized_pullback
          (chartAt (EuclideanSpace ℝ (Fin 2)) q)
          ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x) i j -
        roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
          ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x) i j) 0‖ ≤
        C * N.epsilon := by
  obtain ⟨C, hC, hbound⟩ := m25_exists_normalized_pullback_scalar_twoJet_bound.{u}
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  let K : ℝ := max 1 ‖T.toContinuousLinearMap‖
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨C * K ^ 2, mul_pos hC (pow_pos hKpos 2), ?_⟩
  intro M _ _ _ _ _ _ _ g N q s hs r hr i j
  let E := fun p => roundCylinderTensorCoefficient N.normalized_pullback
    (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j -
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j
  have hp : ‖T.toContinuousLinearMap‖ ^ r ≤ K ^ 2 := by
    calc
      _ ≤ K ^ r := by
        gcongr
        exact le_max_right _ _
      _ ≤ K ^ 2 := pow_le_pow_right₀ hK hr
  have htransfer := Poincare.Analysis.Calculus.norm_iteratedFDeriv_comp_continuousLinearEquiv_le
    T (fun p => E ((0, s) + p)) r (0 : EuclideanSpace ℝ (Fin 3))
  change ‖iteratedFDeriv ℝ r (fun x => E ((0, s) + T x)) 0‖ ≤ _
  calc
    _ ≤ ‖iteratedFDeriv ℝ r E (0, s)‖ * ‖T.toContinuousLinearMap‖ ^ r := by
      simpa only [Function.comp_def, map_zero, iteratedFDeriv_comp_add_left, add_zero]
        using htransfer
    _ ≤ (C * N.epsilon) * K ^ 2 :=
      mul_le_mul (hbound N q hs r hr i j) hp
        (pow_nonneg (norm_nonneg _) r) (mul_nonneg hC.le N.epsilon_pos.le)
    _ = C * K ^ 2 * N.epsilon := by ring

end PoincareConjecture
