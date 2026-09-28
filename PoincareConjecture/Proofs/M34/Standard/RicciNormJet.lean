import PoincareConjecture.Proofs.M34.Standard.ScalarJetOperator
import PoincareConjecture.Proofs.M34.Standard.TensorCoordinateNorm
import PoincareConjecture.Proofs.M34.Mathlib.InvertibleBilinearGram
import PoincareConjecture.Proofs.M04.RicciRegularity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture



theorem LeviCivitaData.tensorNorm_ricciEvaluation_sq
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M) :
    (g.tensorNorm D.ricciEvaluation x) ^ 2 = D.ricciNormSq x := by
  classical
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let f := fun a : Fin 2 → Fin d => (D.ricci x (b (a 0)) (b (a 1))) ^ 2
  change (Real.sqrt (∑ a, f a)) ^ 2 = _
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  let e : (Fin d × Fin d) ≃ (Fin 2 → Fin d) := (finTwoArrowEquiv (Fin d)).symm
  rw [← e.sum_comp f, Fintype.sum_prod_type]
  rfl

namespace M34

open SpacetimeBounds SpacetimeBounds.Bootstrap



noncomputable def ricciNormSquaredTwoJet {n : ℕ} (J : MetricTwoJet n) : ℝ :=
  (tensorNormFromComponents
    (Matrix.of (fun i j => J.1 (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)))
    (fun I : Fin 2 → Fin n => jetRicci J (EuclideanSpace.basisFun (Fin n) ℝ (I 0))
      (EuclideanSpace.basisFun (Fin n) ℝ (I 1)))) ^ 2



theorem continuousAt_ricciNormSquaredTwoJet {n : ℕ} {J : MetricTwoJet n}
    (hJ : J.1.IsInvertible) : ContinuousAt ricciNormSquaredTwoJet J := by
  have h := tendsto_tensorNormFromComponents
    (fun i j => ((continuous_fst.clm_apply
      (continuous_const (y := EuclideanSpace.basisFun (Fin n) ℝ i))).clm_apply
        (continuous_const (y := EuclideanSpace.basisFun (Fin n) ℝ j))).tendsto J)
    (fun I : Fin 2 → Fin n => (contDiffAt_jetRicci hJ
      (EuclideanSpace.basisFun (Fin n) ℝ (I 0))
      (EuclideanSpace.basisFun (Fin n) ℝ (I 1))).continuousAt.tendsto)
    (hJ.det_bilinear_basis_ne_zero (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
  exact h.pow 2



theorem ricciNormSquaredTwoJet_metricTwoJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) :
    ricciNormSquaredTwoJet (metricTwoJet g.euclideanCoefficients x) = D.ricciNormSq x := by
  unfold ricciNormSquaredTwoJet
  simp only [jetRicci_metricTwoJet D]
  have h := g.tensorNormFromComponents_eq_tensorNorm D.ricciEvaluation x
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    ((M04.isSmoothCovariantTensor_ricciEvaluation D).1 x)
  change (tensorNormFromComponents
    (Matrix.of (fun i j => g.inner x (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)))
    (fun I : Fin 2 → Fin n => D.ricciEvaluation x
      (fun i => EuclideanSpace.basisFun (Fin n) ℝ (I i)))) ^ 2 = _
  have hsq := congrArg (fun r : ℝ => r ^ 2) h
  rw [D.tensorNorm_ricciEvaluation_sq] at hsq
  convert! hsq using 1

end M34
end PoincareConjecture
