import PoincareConjecture.Proofs.M34.Standard.CanonicalMetricRealization
import PoincareConjecture.Proofs.M34.Standard.DifferenceEnergyJetOperators
import PoincareConjecture.Proofs.M34.Standard.DifferenceFluxAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

open DifferenceEnergy SpacetimeBounds SpacetimeBounds.Bootstrap

variable {n : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]

noncomputable def canonicalDomain_differenceEnergyBackground :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (_D : LeviCivitaData g) (_p : U) (_x : V n),
      ((Fin n → Fin n → ℝ) × Gamma n) × (Raw n × (V n →L[ℝ] Raw n)) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x
  let r := (extChartAt (𝓡 n) p).symm
  exact ((fun i j => EuclideanSpace.proj i
      ((g.pullbackCoefficients r x).inverse (EuclideanSpace.proj j)),
    fun i j l => EuclideanSpace.proj l
      (D.connection (fun _ : U => EuclideanSpace.single j 1) (r x)
        (EuclideanSpace.single i 1))),
    (fun l j k m => EuclideanSpace.proj l
      (D.curvature (r x) (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1) (EuclideanSpace.single m 1)),
      fderiv ℝ (fun y l j k m => EuclideanSpace.proj l
        (D.curvature (r y) (EuclideanSpace.single j 1)
          (EuclideanSpace.single k 1) (EuclideanSpace.single m 1))) x))

theorem canonicalDomain_differenceEnergyBackground_realization :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g) (p : U) (x : V n), x ∈ U →
      ∃ (gE : RiemannianMetric n (V n)) (DE : LeviCivitaData gE),
        (gE.euclideanCoefficients =ᶠ[𝓝 x]
          g.pullbackCoefficients (extChartAt (𝓡 n) p).symm) ∧
        differenceEnergyBackground DE x =
          canonicalDomain_differenceEnergyBackground U hU g D p x := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x hx
  obtain ⟨gE, DE, W, hW, hxW, _hWU, hcoeff, hconn, hcurv⟩ :=
    canonicalDomain_exists_local_realization U hU g D p x hx
  have hB : gE.euclideanCoefficients =ᶠ[𝓝 x]
      g.pullbackCoefficients (extChartAt (𝓡 n) p).symm := by
    filter_upwards [hW.mem_nhds hxW] with y hy
    exact hcoeff y hy
  refine ⟨gE, DE, hB, ?_⟩
  apply Prod.ext
  · apply Prod.ext
    · funext i j
      change EuclideanSpace.proj i ((gE.euclideanCoefficients x).inverse
        (EuclideanSpace.proj j)) = _
      rw [hcoeff x hxW]
      rfl
    · funext i j l
      change EuclideanSpace.proj l (DE.euclideanConnection
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) x) = _
      rw [hconn x hxW]
      rfl
  · apply Prod.ext
    · funext l j k m
      change EuclideanSpace.proj l (DE.curvature x (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1) (EuclideanSpace.single m 1)) = _
      rw [hcurv x hxW]
      rfl
    · apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hW.mem_nhds hxW] with y hy
      funext l j k m
      change EuclideanSpace.proj l (DE.curvature y (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1) (EuclideanSpace.single m 1)) = _
      rw [hcurv y hy]

theorem canonicalDomain_differenceEnergyJetBackground :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g) (p : U) (x : V n), x ∈ U →
      differenceEnergyJetBackground n (spatialJet 3 (fun z : ℝ × V n =>
        g.pullbackCoefficients (extChartAt (𝓡 n) p).symm z.2) (0, x)) =
          canonicalDomain_differenceEnergyBackground U hU g D p x := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x hx
  obtain ⟨gE, DE, hB, hback⟩ :=
    canonicalDomain_differenceEnergyBackground_realization U hU g D p x hx
  rw [← hback, ← differenceEnergyJetBackground_spatialJet DE x]
  congr 1
  funext j
  exact ((hB.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds).symm

theorem canonicalDomain_differenceEnergyBackground_bound
    (n : ℕ) {a : ℝ} (ha : 0 < a) (H : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (U : Set (V n)) (hU : IsOpen U) (hNE : Nonempty U),
      letI := hNE
      letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g) (p : U) (x : V n), x ∈ U →
        (∀ j ≤ 3, ‖iteratedFDeriv ℝ j
          (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm) x‖ ≤ H) →
        (∀ v, a * ‖v‖ ^ 2 ≤ g.pullbackCoefficients (extChartAt (𝓡 n) p).symm x v v) →
        ‖canonicalDomain_differenceEnergyBackground U hU g D p x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := differenceEnergyBackground_bound_of_metric_jets n ha H
  refine ⟨C, hC, ?_⟩
  intro U hU hNE
  let := hNE
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x hx hjets hell
  obtain ⟨gE, DE, hB, hback⟩ :=
    canonicalDomain_differenceEnergyBackground_realization U hU g D p x hx
  rw [← hback]
  apply hbound gE DE x
  · intro j hj
    rw [(hB.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds]
    exact hjets j hj
  · intro v
    rw [hB.eq_of_nhds]
    exact hell v

end PoincareConjecture.M34
