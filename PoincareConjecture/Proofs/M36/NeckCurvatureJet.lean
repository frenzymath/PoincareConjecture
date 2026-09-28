import PoincareConjecture.Proofs.M36.CenteredNeckMetric
import PoincareConjecture.Proofs.M36.CylinderTwoJet
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Pullback









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M36

open PoincareConjecture.SpacetimeBounds

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem centeredNeckMetric_jetCurvature
    {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    (theta : UnitTwoSphere) (s : ℝ) {p : E₃} (hp : p ∈ centeredNeckDomain N s)
    (u w v z : E₃) :
    jetCurvature
        (metricTwoJet (centeredCylinderMetric (fun q a b => normalizedNeckForm N q a b)
          theta s) p) u w v z =
      (normalizedNeckConnection N).curvatureTensor (centeredNeckLift N theta s p)
        (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) p u)
        (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) p w)
        (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) p v)
        (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) p z) := by
  obtain ⟨gE, DE, V, hV, hpV, hVU, hcoeff⟩ :=
    exists_centeredNeckMetric_realization N theta s hp
  have hB : gE.euclideanCoefficients =ᶠ[𝓝 p]
      centeredCylinderMetric (fun q a b => normalizedNeckForm N q a b) theta s := by
    filter_upwards [hV.mem_nhds hpV] with q hq
    exact (hcoeff q hq).trans (normalizedNeckMetric_pullbackCoefficients N theta s (hVU hq))
  have hjet : metricTwoJet gE.euclideanCoefficients p =
      metricTwoJet (centeredCylinderMetric (fun q a b => normalizedNeckForm N q a b)
        theta s) p := by
    simp only [metricTwoJet, hB.self_of_nhds, hB.fderiv_eq,
      (hB.fderiv (𝕜 := ℝ)).fderiv_eq]
  rw [← hjet, jetCurvature_metricTwoJet DE]
  apply DE.curvatureTensor_eq_pullback_euclidean (normalizedNeckConnection N)
    (centeredNeckLift_contMDiffAt N theta s hp)
  · filter_upwards [(centeredNeckDomain_isOpen N s).mem_nhds hp] with q hq
    exact centeredNeckLift_mfderiv_isInvertible N theta s hq
  · filter_upwards [hV.mem_nhds hpV] with q hq
    intro a b
    exact congrArg (fun B => B a b) (hcoeff q hq)

theorem exists_normalizedNeck_curvature_component_bounds :
    ∃ delta : ℝ, 0 < delta ∧ ∃ K : ℝ, 0 < K ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
        {g : RiemannianMetric 3 M} (N : EpsilonNeck g),
        N.epsilon ≤ delta → 2 ≤ ⌊N.epsilon⁻¹⌋₊ →
        ∀ (theta : UnitTwoSphere) (s : ℝ), s ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        ∀ i j k l : Fin 3,
          |(normalizedNeckConnection N).curvatureTensor (centeredNeckLift N theta s 0)
              (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) 0
                (EuclideanSpace.basisFun (Fin 3) ℝ i))
              (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) 0
                (EuclideanSpace.basisFun (Fin 3) ℝ j))
              (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) 0
                (EuclideanSpace.basisFun (Fin 3) ℝ k))
              (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) 0
                (EuclideanSpace.basisFun (Fin 3) ℝ l)) -
            jetCurvature cylinderModelJet (EuclideanSpace.basisFun (Fin 3) ℝ i)
              (EuclideanSpace.basisFun (Fin 3) ℝ j)
              (EuclideanSpace.basisFun (Fin 3) ℝ k)
              (EuclideanSpace.basisFun (Fin 3) ℝ l)| ≤ K * N.epsilon := by
  obtain ⟨delta, hdelta, K, hK, hb⟩ := exists_roundCylinderClose_jetCurvature_bounds
  refine ⟨delta, hdelta, K, hK, ?_⟩
  intro M _ _ _ g N hsmall horder theta s hs i j k l
  have hclose : RoundCylinderClose N.epsilon 0 (fun q a b => normalizedNeckForm N q a b) :=
    N.metric_comparison.close
  have h := (hb N.epsilon N.epsilon_pos hsmall _ hclose horder (theta, s) hs).1 i j k l
  rw [centeredNeckMetric_jetCurvature N theta s (zero_mem_centeredNeckDomain N hs)] at h
  exact h

end PoincareConjecture.M36
