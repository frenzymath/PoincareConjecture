import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.ScalarLaplacianJet
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.RicciNormJet

/-!
# The scalar evolution numerator from four metric jets

The actual Laplacian of scalar curvature plus twice the actual Ricci
squared norm is a continuous function of the metric four-jet. This is
a static identity; the Ricci flow equation supplies its time derivative.
Source: Morgan-Tian Theorem 12.28, pp. 323-324;
included-cylinder-geometric-readouts.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The two-jet projection of the four-jet has dependent coefficient spaces.
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap

/-- The genuine scalar evolution numerator as a metric four-jet
operator (Theorem 12.28, pp. 323-324). -/
noncomputable def scalarEvolutionJet (n : ℕ)
    (J : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 4) : ℝ :=
  scalarLaplacianJet n J + 2 * ricciNormSquaredTwoJet
    (twoJetProjection n (baseProjection 2 2 J))

/-- The scalar evolution numerator is continuous on invertible
metric four-jets (Theorem 12.28, pp. 323-324). -/
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

/-- On an actual metric the four-jet readout is its actual scalar
Laplacian plus twice the actual Ricci squared norm (Theorem 12.28). -/
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

end PoincareMT.M34
