import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.CanonicalGeometry.CanonicalMetricRealization
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Energy.DifferenceEnergyJetOperators
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Energy.DifferenceFluxAlgebra

/-!
# Actual canonical-domain background fields from finite metric jets

The static realization agrees on an open neighborhood, so it identifies
ordinary curvature derivatives as well as connection and curvature values.
The universal three-jet operator therefore bounds the actual fields with a
constant chosen before the domain and all geometry. This is the uniform
coefficient step for Morgan-Tian Section 12.5, pp. 309-319.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The jet and curvature targets contain dependent finite products of Hom fibers.
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34

open DifferenceEnergy SpacetimeBounds SpacetimeBounds.Bootstrap

variable {n : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]

/-- The actual inverse, connection, raised curvature and ordinary derivative
in one canonical chart (Section 12.5, pp. 309-319). -/
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

/-- A static local realization gives all four actual background fields,
including the ordinary derivative (Section 12.5, pp. 309-319). -/
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

/-- The formal three-jet readout equals the actual canonical-domain fields
on the open target (Section 12.5, pp. 309-319). -/
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

/-- One constant bounds all actual canonical-domain background fields before
choosing the domain, metric, connection, chart or point
(Section 12.5, pp. 309-319). -/
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

end PoincareMT.M34
