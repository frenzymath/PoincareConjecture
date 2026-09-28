import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceEnergyBackground
import PoincareConjecture.Proofs.M34.Standard.DifferenceJetFluxParameters











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy SpacetimeBounds SpacetimeBounds.Bootstrap

variable {n : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]



noncomputable def canonicalDomain_curvatureArray :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (_D : LeviCivitaData g) (_p : U), V n → Raw n := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x
  exact (canonicalDomain_differenceEnergyBackground U hU g D p x).2.1



noncomputable def canonicalDomain_covariantCurvatureArray :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (_D : LeviCivitaData g) (_p : U) (_x : V n), Flux n := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x d l j k m
  exact fderiv ℝ (fun y => canonicalDomain_curvatureArray U hU g D p y l j k m) x
    (EuclideanSpace.single d 1) +
      curvatureAction (canonicalDomain_differenceEnergyBackground U hU g D p x).1.2 d
        (canonicalDomain_curvatureArray U hU g D p x) l j k m



noncomputable def canonicalDomain_raisedCurvatureFlux :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (_D : LeviCivitaData g) (_p : U) (_x : V n), Flux n := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x i l j k m
  exact ∑ d : Fin n, EuclideanSpace.proj i
    ((g.pullbackCoefficients (extChartAt (𝓡 n) p).symm x).inverse (EuclideanSpace.proj d)) *
      canonicalDomain_covariantCurvatureArray U hU g D p x d l j k m



theorem canonicalDomain_differentiableAt_curvatureArray :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g) (p : U) (x : V n), x ∈ U →
      DifferentiableAt ℝ (canonicalDomain_curvatureArray U hU g D p) x := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x hx
  obtain ⟨gE, DE, W, hW, hxW, _hWU, _hcoeff, _hconn, hcurv⟩ :=
    canonicalDomain_exists_local_realization U hU g D p x hx
  apply (hasFDerivAt_raisedCurvatureJetArray DE x).differentiableAt.congr_of_eventuallyEq
  filter_upwards [hW.mem_nhds hxW] with y hy
  funext l j k m
  change EuclideanSpace.proj l (D.curvature ((extChartAt (𝓡 n) p).symm y)
    (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) (EuclideanSpace.single m 1)) = _
  rw [hcurv y hy]



theorem canonicalDomain_fderiv_curvature_component :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g) (p : U) (x : V n), x ∈ U →
      ∀ (l j k m : Fin n) (v : V n),
        fderiv ℝ (fun y => canonicalDomain_curvatureArray U hU g D p y l j k m) x v =
          (canonicalDomain_differenceEnergyBackground U hU g D p x).2.2 v l j k m := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x hx l j k m v
  let L0 : Raw n →L[ℝ] (Fin n → Fin n → Fin n → ℝ) := ContinuousLinearMap.proj l
  let L1 : (Fin n → Fin n → Fin n → ℝ) →L[ℝ] (Fin n → Fin n → ℝ) :=
    ContinuousLinearMap.proj j
  let L2 : (Fin n → Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.proj k
  let L3 : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj m
  let L : Raw n →L[ℝ] ℝ := L3.comp (L2.comp (L1.comp L0))
  have hd := L.hasFDerivAt.comp x
    (canonicalDomain_differentiableAt_curvatureArray U hU g D p x hx).hasFDerivAt
  exact congrArg (fun A => A v) hd.fderiv



theorem canonicalDomain_inverseMetricThreeJet :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (p : U) (x : V n),
      inverseMetricThreeJet n (spatialJet 3 (fun z : ℝ × V n =>
        g.pullbackCoefficients (extChartAt (𝓡 n) p).symm z.2) (0, x)) =
          (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm x).inverse := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g p x
  simp only [inverseMetricThreeJet, truncate_spatialJet, twoJetProjection_spatialJet]
  rfl



theorem canonicalDomain_connectionThreeJet :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g) (p : U) (x : V n), x ∈ U →
      connectionThreeJet n (spatialJet 3 (fun z : ℝ × V n =>
        g.pullbackCoefficients (extChartAt (𝓡 n) p).symm z.2) (0, x)) =
          (canonicalDomain_differenceEnergyBackground U hU g D p x).1.2 := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x hx
  exact congrArg (fun B => B.1.2)
    (canonicalDomain_differenceEnergyJetBackground U hU g D p x hx)



theorem canonicalDomain_curvatureThreeJet :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g) (p : U) (x : V n), x ∈ U →
      curvatureThreeJet n (spatialJet 3 (fun z : ℝ × V n =>
        g.pullbackCoefficients (extChartAt (𝓡 n) p).symm z.2) (0, x)) =
          canonicalDomain_curvatureArray U hU g D p x := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x hx
  exact congrArg (fun B => B.2.1)
    (canonicalDomain_differenceEnergyJetBackground U hU g D p x hx)



theorem canonicalDomain_covariantCurvatureThreeJet :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g) (p : U) (x : V n), x ∈ U →
      covariantCurvatureThreeJet n (spatialJet 3 (fun z : ℝ × V n =>
        g.pullbackCoefficients (extChartAt (𝓡 n) p).symm z.2) (0, x)) =
          canonicalDomain_covariantCurvatureArray U hU g D p x := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x hx
  have hb := canonicalDomain_differenceEnergyJetBackground U hU g D p x hx
  have hg := congrArg (fun B => B.1.2) hb
  have hR := congrArg (fun B => B.2.1) hb
  have hd := congrArg (fun B => B.2.2) hb
  funext d l j k m
  dsimp only [covariantCurvatureThreeJet, connectionThreeJet, curvatureThreeJet,
    canonicalDomain_covariantCurvatureArray]
  rw [show prolong 2 (raisedCurvatureJetArray n) (spatialJet 3
    (fun z : ℝ × V n => g.pullbackCoefficients (extChartAt (𝓡 n) p).symm z.2) (0, x)) =
      (canonicalDomain_differenceEnergyBackground U hU g D p x).2.2 from hd]
  rw [canonicalDomain_fderiv_curvature_component U hU g D p x hx]
  dsimp only [differenceEnergyJetBackground] at hg hR
  rw [hg, hR]
  rfl



theorem canonicalDomain_raisedCurvatureFluxThreeJet :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g) (p : U) (x : V n), x ∈ U →
      raisedCurvatureFluxThreeJet n (spatialJet 3 (fun z : ℝ × V n =>
        g.pullbackCoefficients (extChartAt (𝓡 n) p).symm z.2) (0, x)) =
          canonicalDomain_raisedCurvatureFlux U hU g D p x := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x hx
  funext i l j k m
  dsimp only [raisedCurvatureFluxThreeJet, canonicalDomain_raisedCurvatureFlux]
  rw [canonicalDomain_inverseMetricThreeJet U hU,
    canonicalDomain_covariantCurvatureThreeJet U hU g D p x hx]

end PoincareConjecture.M34
