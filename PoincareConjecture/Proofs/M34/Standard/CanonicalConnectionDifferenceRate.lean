import PoincareConjecture.Proofs.M34.Standard.CanonicalRicciGradientDifference
import PoincareConjecture.Proofs.M34.Standard.UniformConnectionJetRate











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy SpacetimeBounds SpacetimeBounds.Bootstrap

variable {n dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]



noncomputable def canonicalDomain_connectionDifferenceRate
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g0 : RiemannianMetric n U) (_D0 : LeviCivitaData g0)
      (g1 : RiemannianMetric n U) (_D1 : LeviCivitaData g1) (_p : U) (_x : V n),
      (Fin dS × Fin n → ℝ) → FH n → FA n → FS n → FA n := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g0 D0 g1 D1 p x d H A S
  exact connectionDifferenceRate qS
    (g0.pullbackCoefficients (extChartAt (𝓡 n) p).symm x).inverse
    (canonicalDomain_differenceEnergyBackground U hU g0 D0 p x).1.2
    (canonicalDomain_curvatureArray U hU g1 D1 p x)
    (canonicalDomain_connectionVelocity U hU g1 D1 p x) d H A S




theorem canonicalDomain_connectionVelocity_difference
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g0 : RiemannianMetric n U) (D0 : LeviCivitaData g0)
      (g1 : RiemannianMetric n U) (D1 : LeviCivitaData g1) (p : U) (x : V n), x ∈ U →
      ∀ (R0 R1 : V n → FS n),
        (∀ y ∈ U, raw (R0 y) = canonicalDomain_curvatureArray U hU g0 D0 p y) →
        (∀ y ∈ U, raw (R1 y) = canonicalDomain_curvatureArray U hU g1 D1 p y) →
        DifferentiableAt ℝ R0 x → DifferentiableAt ℝ R1 x →
        ContinuousLinearMap.piLpBilinearFromCoordinates (p := 2) (q := 2)
          (fun j i => canonicalDomain_connectionVelocity U hU g0 D0 p x i j -
            canonicalDomain_connectionVelocity U hU g1 D1 p x i j) =
          canonicalDomain_connectionDifferenceRate U hU qS g0 D0 g1 D1 p x
            (fun beta => fderiv ℝ (fun y => qS (R0 y - R1 y) beta.1) x
              (EuclideanSpace.single beta.2 1))
            (g0.pullbackCoefficients (extChartAt (𝓡 n) p).symm x -
              g1.pullbackCoefficients (extChartAt (𝓡 n) p).symm x)
            (CovariantDerivative.difference D0.connection D1.connection
              ((extChartAt (𝓡 n) p).symm x)) (R0 x - R1 x) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g0 D0 g1 D1 p x hx R0 R1 hR0 hR1 hd0 hd1
  have hxt : x ∈ (extChartAt (𝓡 n) p).target := by
    rw [canonicalOpen_extChart_target (𝕜 := ℝ) hU p]
    exact hx
  have hC := canonicalDomain_ricciGradient_difference qS U hU
    g0 D0 g1 D1 p x hx R0 R1 hR0 hR1 hd0 hd1
  have hf := connectionDifferenceRate_factorization qS
    (g0.pullbackCoefficients (extChartAt (𝓡 n) p).symm x)
    (g1.pullbackCoefficients (extChartAt (𝓡 n) p).symm x)
    (g0.isInvertible_chartCoefficients p hxt) (g1.isInvertible_chartCoefficients p hxt)
    _ _ _ _ _ _ _ hC
  rw [hR1 x hx] at hf
  let L : (Fin n → Fin n → V n) →L[ℝ] FA n :=
    ContinuousLinearMap.piLpBilinearFromCoordinates
  change L ((fun j i => canonicalDomain_connectionVelocity U hU g0 D0 p x i j) -
      (fun j i => canonicalDomain_connectionVelocity U hU g1 D1 p x i j)) = _
  rw [map_sub]
  exact hf



theorem canonicalDomain_connectionDifferenceRate_from_jets
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g0 : RiemannianMetric n U) (D0 : LeviCivitaData g0)
      (g1 : RiemannianMetric n U) (D1 : LeviCivitaData g1) (p : U) (x : V n), x ∈ U →
      ∀ (d : Fin dS × Fin n → ℝ) (H : FH n) (A : FA n) (S : FS n),
        connectionDifferenceRateFromJets qS
          (spatialJet 3 (fun z : ℝ × V n =>
            g0.pullbackCoefficients (extChartAt (𝓡 n) p).symm z.2) (0, x))
          (spatialJet 3 (fun z : ℝ × V n =>
            g1.pullbackCoefficients (extChartAt (𝓡 n) p).symm z.2) (0, x)) d H A S =
          canonicalDomain_connectionDifferenceRate U hU qS g0 D0 g1 D1 p x d H A S := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g0 D0 g1 D1 p x hx d H A S
  dsimp only [connectionDifferenceRateFromJets, canonicalDomain_connectionDifferenceRate]
  rw [canonicalDomain_inverseMetricThreeJet U hU,
    canonicalDomain_connectionThreeJet U hU g0 D0 p x hx,
    canonicalDomain_curvatureThreeJet U hU g1 D1 p x hx,
    canonicalDomain_connectionVelocity_from_jets U hU g1 D1 p x hx]

end PoincareConjecture.M34
