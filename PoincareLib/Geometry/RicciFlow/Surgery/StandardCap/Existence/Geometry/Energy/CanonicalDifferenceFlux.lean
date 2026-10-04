import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Energy.CanonicalDifferenceJetFluxParameters
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Energy.UniformDifferenceJetFlux

/-!
# The actual canonical curvature-difference flux

The formal jet flux and raised divergence remainder equal the explicit
polynomials in the two retained connections and curvatures. This realizes
all their background parameters; applying the evolution PDE remains a
separate step. Morgan-Tian Section 12.5, pp. 309-319.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Tensor differences and their finite jets use nested Hom fibers.
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

open DifferenceEnergy SpacetimeBounds SpacetimeBounds.Bootstrap

variable {n : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]

/-- The complete curvature-difference flux with the actual canonical metric,
connection and differentiated-curvature parameters
(Section 12.5, pp. 309-319). -/
noncomputable def canonicalDomain_curvatureDifferenceFlux :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (_D : LeviCivitaData g)
      (g' : RiemannianMetric n U) (_D' : LeviCivitaData g') (_p : U) (_x : V n),
      FH n → FA n → FS n → Flux n := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D g' D' p x H A S
  exact curvatureDifferenceFlux
    (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm x).inverse
    (g'.pullbackCoefficients (extChartAt (𝓡 n) p).symm x).inverse
    (canonicalDomain_differenceEnergyBackground U hU g D p x).1.2
    (canonicalDomain_curvatureArray U hU g' D' p x)
    (canonicalDomain_covariantCurvatureArray U hU g' D' p x) H A S

/-- The complete geometric remainder, including the raised principal term
and the extra connection action on the primed flux
(Section 12.5, pp. 309-319). -/
noncomputable def canonicalDomain_curvatureDifferenceRemainder {dS : ℕ}
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (_D : LeviCivitaData g)
      (g' : RiemannianMetric n U) (_D' : LeviCivitaData g') (_p : U) (_x : V n),
      (Fin dS × Fin n → ℝ) → FH n → FA n → FS n → Fin dS → ℝ := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D g' D' p x d H A S
  exact curvatureDifferenceRemainder qS
    (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm x).inverse
    (g'.pullbackCoefficients (extChartAt (𝓡 n) p).symm x).inverse
    (canonicalDomain_differenceEnergyBackground U hU g D p x).1.2
    (canonicalDomain_curvatureArray U hU g' D' p x)
    (canonicalDomain_covariantCurvatureArray U hU g' D' p x)
    (canonicalDomain_raisedCurvatureFlux U hU g' D' p x) d H A S

/-- Actual coefficient jets reproduce the full canonical curvature-difference
flux (Section 12.5, pp. 309-319). -/
theorem canonicalDomain_curvatureDifferenceFlux_from_jets :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g)
      (g' : RiemannianMetric n U) (D' : LeviCivitaData g') (p : U) (x : V n), x ∈ U →
      ∀ (H : FH n) (A : FA n) (S : FS n),
        curvatureDifferenceFluxFromJets
          (spatialJet 3 (fun z : ℝ × V n =>
            g.pullbackCoefficients (extChartAt (𝓡 n) p).symm z.2) (0, x))
          (spatialJet 3 (fun z : ℝ × V n =>
            g'.pullbackCoefficients (extChartAt (𝓡 n) p).symm z.2) (0, x)) H A S =
          canonicalDomain_curvatureDifferenceFlux U hU g D g' D' p x H A S := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D g' D' p x hx H A S
  dsimp only [curvatureDifferenceFluxFromJets, canonicalDomain_curvatureDifferenceFlux]
  rw [canonicalDomain_inverseMetricThreeJet U hU,
    canonicalDomain_inverseMetricThreeJet U hU,
    canonicalDomain_connectionThreeJet U hU g D p x hx,
    canonicalDomain_curvatureThreeJet U hU g' D' p x hx,
    canonicalDomain_covariantCurvatureThreeJet U hU g' D' p x hx]

/-- Actual coefficient jets reproduce every term of the geometric remainder
(Section 12.5, pp. 309-319). -/
theorem canonicalDomain_curvatureDifferenceRemainder_from_jets {dS : ℕ}
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g)
      (g' : RiemannianMetric n U) (D' : LeviCivitaData g') (p : U) (x : V n), x ∈ U →
      ∀ (d : Fin dS × Fin n → ℝ) (H : FH n) (A : FA n) (S : FS n),
        curvatureDifferenceRemainderFromJets qS
          (spatialJet 3 (fun z : ℝ × V n =>
            g.pullbackCoefficients (extChartAt (𝓡 n) p).symm z.2) (0, x))
          (spatialJet 3 (fun z : ℝ × V n =>
            g'.pullbackCoefficients (extChartAt (𝓡 n) p).symm z.2) (0, x)) d H A S =
          canonicalDomain_curvatureDifferenceRemainder U hU qS g D g' D' p x d H A S := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D g' D' p x hx d H A S
  dsimp only [curvatureDifferenceRemainderFromJets, canonicalDomain_curvatureDifferenceRemainder]
  rw [canonicalDomain_inverseMetricThreeJet U hU,
    canonicalDomain_inverseMetricThreeJet U hU,
    canonicalDomain_connectionThreeJet U hU g D p x hx,
    canonicalDomain_curvatureThreeJet U hU g' D' p x hx,
    canonicalDomain_covariantCurvatureThreeJet U hU g' D' p x hx,
    canonicalDomain_raisedCurvatureFluxThreeJet U hU g' D' p x hx]

end PoincareMT.M34
