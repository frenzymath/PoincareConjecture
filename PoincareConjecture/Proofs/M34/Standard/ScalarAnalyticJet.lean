import PoincareConjecture.Proofs.M34.Standard.ScalarAnalyticConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap

noncomputable def scalarAnalyticJet (n : ℕ)
    (J : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 4) : ℝ × ℝ × ℝ :=
  (scalarTwoJet (twoJetProjection n (baseProjection 2 2 J)),
    scalarDifferentialNormJet n (baseProjection 3 1 J), scalarEvolutionJet n J)

theorem continuousOn_scalarAnalyticJet (n : ℕ) :
    ContinuousOn (scalarAnalyticJet n) (curvatureJetDomain n 2) := by
  intro J hJ
  apply ContinuousAt.continuousWithinAt
  have hS : ContinuousAt
      (fun A : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 4 =>
        scalarTwoJet (twoJetProjection n (baseProjection 2 2 A))) J :=
    (contDiffAt_scalarTwoJet (J := twoJetProjection n (baseProjection 2 2 J)) hJ).continuousAt
      |>.comp_of_eq (((twoJetProjection n).comp (baseProjection 2 2)).continuous.continuousAt) rfl
  have hJ3 : baseProjection 3 1 J ∈ curvatureJetDomain n 1 := by
    exact hJ
  have hD := ((continuousOn_scalarDifferentialNormJet n).continuousAt
    ((isOpen_curvatureJetDomain n 1).mem_nhds hJ3)).comp
      (baseProjection 3 1).continuous.continuousAt
  have hE := (continuousOn_scalarEvolutionJet n).continuousAt
    ((isOpen_curvatureJetDomain n 2).mem_nhds hJ)
  exact hS.prodMk (hD.prodMk hE)

theorem scalarAnalyticJet_spatialJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) :
    scalarAnalyticJet n (spatialJet 4
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients z.2) (0, x)) =
      (D.scalarCurvature x, g.tangentNorm x (D.gradient D.scalarCurvature x),
        D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x) := by
  have h2 := baseProjection_spatialJet 2 2
    (fun z : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients z.2) (0, x)
  have h3 := baseProjection_spatialJet 3 1
    (fun z : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients z.2) (0, x)
  simp only [scalarAnalyticJet, h2, h3, twoJetProjection_spatialJet,
    scalarTwoJet_metricTwoJet D, scalarDifferentialNormJet_spatialJet D,
    scalarEvolutionJet_spatialJet D]

end PoincareConjecture.M34
