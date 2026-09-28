import PoincareConjecture.Proofs.M34.Mathlib.InvertibleBilinearGram
import PoincareConjecture.Proofs.M34.Standard.CurvatureJetRealization
import PoincareConjecture.Proofs.M34.Standard.TensorCoordinateNorm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap

noncomputable def curvatureJetNorm (n m : ℕ)
    (J : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) (2 + m)) : ℝ :=
  tensorNormFromComponents
    (Matrix.of (fun i j => (twoJetProjection n (baseProjection 2 m J)).1
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)))
    (curvatureJetComponents n m J)

set_option synthInstance.maxHeartbeats 100000 in

theorem continuousOn_curvatureJetNorm (n m : ℕ) :
    ContinuousOn (curvatureJetNorm n m) (curvatureJetDomain n m) := by
  intro J hJ
  apply ContinuousAt.continuousWithinAt
  have hB : Continuous (fun K : Jet (EuclideanSpace ℝ (Fin n))
      (MetricCoefficient n) (2 + m) => (twoJetProjection n (baseProjection 2 m K)).1) :=
    continuous_fst.comp ((twoJetProjection n).continuous.comp (baseProjection 2 m).continuous)
  have hC := ((contDiffOn_curvatureJetComponents n m).contDiffAt
    ((isOpen_curvatureJetDomain n m).mem_nhds hJ)).continuousAt
  exact tendsto_tensorNormFromComponents
    (fun i j => ((hB.clm_apply continuous_const).clm_apply continuous_const).tendsto J)
    (fun I => (continuous_apply I).continuousAt.tendsto.comp hC.tendsto)
    (ContinuousLinearMap.IsInvertible.det_bilinear_basis_ne_zero hJ
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)

set_option synthInstance.maxHeartbeats 100000 in

theorem curvatureJetNorm_spatialJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    curvatureJetNorm n m
      (spatialJet (2 + m) (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        g.euclideanCoefficients p.2) (0, x)) = D.curvatureDerivativeNorm m x := by
  simp only [curvatureJetNorm, baseProjection_spatialJet, twoJetProjection_spatialJet]
  rw [funext (curvatureJetComponents_spatialJet D m x)]
  exact g.tensorNormFromComponents_eq_tensorNorm
    (D.iteratedCovariantTensorDerivative D.riemannEvaluation m) x
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    ((D.iteratedCovariantTensorDerivative_isSmooth D.riemannEvaluation_isSmooth_model m).1 x)

theorem curvatureJetNorm_bound (n m : ℕ) {a : ℝ} (ha : 0 < a) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) (2 + m),
      ‖J‖ ≤ H →
      (∀ v, a * ‖v‖ ^ 2 ≤
        (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin n))
          (MetricCoefficient n) (J 0)) v v) → curvatureJetNorm n m J ≤ C := by
  obtain ⟨K, hK, hKU, hbox⟩ := exists_compact_elliptic_jet_box n m ha H
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_curvatureJetNorm n m).mono hKU)
  refine ⟨max C 0, le_max_right _ _, fun J hJ hell => ?_⟩
  exact (le_abs_self _).trans ((hC J (hbox J hJ hell)).trans (le_max_left _ _))

theorem curvatureDerivativeNorm_bound_of_coefficient_jets
    (n m : ℕ) {a : ℝ} (ha : 0 < a) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (D : LeviCivitaData g) (x : EuclideanSpace ℝ (Fin n)),
      (∀ j ≤ 2 + m, ‖iteratedFDeriv ℝ j g.euclideanCoefficients x‖ ≤ H) →
      (∀ v, a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v) →
      D.curvatureDerivativeNorm m x ≤ C := by
  obtain ⟨C, hC, hbound⟩ := curvatureJetNorm_bound n m ha H
  refine ⟨C, hC, fun g D x hjets hell => ?_⟩
  rw [← curvatureJetNorm_spatialJet D m x]
  apply hbound
  · have hH := (norm_nonneg (iteratedFDeriv ℝ 0 g.euclideanCoefficients x)).trans
      (hjets 0 (by omega))
    apply (pi_norm_le_iff_of_nonneg hH).mpr
    intro j
    exact hjets j (by omega)
  · exact hell

end PoincareConjecture.M34
