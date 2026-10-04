import PoincareLib.Geometry.RicciFlow.Local.Continuation.EndpointMetric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Connection.Difference
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Connection.NativeTime
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Connection.Variation
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureHom
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvaturePairExchange
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureRicciSecondDerivative
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureTrace
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureTrilinear
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Energy.CurvatureRateAlgebra
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Coefficients.CompactCoordinateChange
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Coefficients.CompactFiniteCoefficient
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Comparison.RateFiniteAlgebra
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Comparison.ScalarEnergyComparison
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Coordinates.FamilyBundleCoordinates
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Coordinates.LocalCoordinateEnergy
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Metric.MetricCompactBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Metric.MetricDifferenceEnergyRate
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Metric.MetricDifferenceEvolution
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Metric.MetricInverse
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.CanonicalFlowCurvature

/-!
# Uniform metric difference energy on a fixed canonical domain

The lower M03 metric rate has a constant preceding all flows and cutoffs
on a fixed domain. A singleton canonical chart gives the local integral
estimate needed for every translated flow on the reference domain.
This is Morgan-Tian Section 12.5, pp. 309-319; see
canonical-local-evolution.md for the domain/constant quantifier order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The actual curvature representatives use three nested Hom fibers.
set_option maxSynthPendingDepth 8

open Set Bundle MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareMT.M34

open DifferenceEnergy

set_option maxHeartbeats 800000 in
-- Normalize the finite singleton chart and the two actual bundle coordinates.
/-- One metric-energy constant works for all actual flow pairs and compact
cutoffs on a fixed canonical domain (Section 12.5, pp. 309-319). -/
theorem exists_canonicalDomain_metric_energy_bound
    {n dH dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    letI : MeasurableSpace (V n) := borel _
    letI : BorelSpace (V n) := ⟨rfl⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : U) (φ : V n → ℝ),
      Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J')
        (R R' : ℝ → U → FS n),
        (∀ t x u v w, R t x u v w = (F.connection t).curvature x u v w) →
        (∀ t x u v w, R' t x u v w = (F'.connection t).curvature x u v w) →
        let r := (extChartAt (𝓡 n) p).symm
        let H : ℝ × V n → FH n := fun z =>
          (F.metric z.1).inner (r z.2) - (F'.metric z.1).inner (r z.2)
        let S := fun z : ℝ × V n => R z.1 (r z.2) - R' z.1 (r z.2)
        ∀ t ∈ interior (J ∩ J'),
          (∑ alpha : Fin dH, ∫ x, 2 * φ x ^ 2 * qH (H (t, x)) alpha *
            fderiv ℝ (fun z => qH (H z) alpha) (t, x) (1, 0)) ≤
            (∑ alpha : Fin dH, ∫ x, (φ x * qH (H (t, x)) alpha) ^ 2) +
              C * (∑ beta : Fin dS, ∫ x, (φ x * qS (S (t, x)) beta) ^ 2) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let : MeasurableSpace (V n) := borel _
  let : BorelSpace (V n) := ⟨rfl⟩
  obtain ⟨C, hC, hbound⟩ := Proofs.M03.exists_metric_difference_energy_rate_bound
    (M := U) qH qS
  refine ⟨C, hC, ?_⟩
  intro p φ hφ hφc hφU J J' F F' R R' hR hR' r H S t ht
  have hc : ∀ a ∈ ({p} : Finset U), Continuous φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ (chartAt (V n) a).target := by
    intro a _
    rw [canonicalOpen_chart_target hU]
    exact ⟨hφ, hφc, hφU⟩
  have hh := hbound {p} (fun _ => φ) hc J J' F F' R R' hR hR' t ht
  simpa only [r, H, S, Finset.sum_singleton,
    constantChart_bilinear_coordinates (𝓡 n) (canonicalOpen_chart_eq hU),
    constantChart_vectorTrilinear_coordinates (𝓡 n) (canonicalOpen_chart_eq hU),
    extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq] using hh

end PoincareMT.M34
