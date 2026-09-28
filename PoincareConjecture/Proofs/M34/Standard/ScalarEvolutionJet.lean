import PoincareConjecture.Proofs.M34.Standard.ScalarLaplacianJet
import PoincareConjecture.Proofs.M34.Standard.RicciNormJet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap

noncomputable def scalarEvolutionJet (n : ℕ)
    (J : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 4) : ℝ :=
  scalarLaplacianJet n J + 2 * ricciNormSquaredTwoJet
    (twoJetProjection n (baseProjection 2 2 J))

theorem continuousOn_scalarEvolutionJet (n : ℕ) :
    ContinuousOn (scalarEvolutionJet n) (curvatureJetDomain n 2) := by
  intro J hJ
  apply ContinuousAt.continuousWithinAt
  have hL := (continuousOn_scalarLaplacianJet n).continuousAt
    ((isOpen_curvatureJetDomain n 2).mem_nhds hJ)
  have hK : ContinuousAt (fun A => twoJetProjection n (baseProjection 2 2 A)) J :=
    ((twoJetProjection n).comp (baseProjection 2 2)).continuous.continuousAt
  have hR : ContinuousAt
      (fun A : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 4 =>
        ricciNormSquaredTwoJet (twoJetProjection n (baseProjection 2 2 A))) J :=
    (continuousAt_ricciNormSquaredTwoJet
      (J := twoJetProjection n (baseProjection 2 2 J)) hJ).comp_of_eq hK rfl
  exact hL.add (hR.const_mul 2)

theorem scalarEvolutionJet_spatialJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) :
    scalarEvolutionJet n (spatialJet 4
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients z.2) (0, x)) =
      D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x := by
  have hK := congrArg (twoJetProjection n) (baseProjection_spatialJet 2 2
    (fun z : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients z.2) (0, x))
  rw [twoJetProjection_spatialJet] at hK
  simp only [scalarEvolutionJet, scalarLaplacianJet_spatialJet D, hK,
    ricciNormSquaredTwoJet_metricTwoJet D]

end PoincareConjecture.M34
