import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.Pullback.Geometry
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.Connections
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.Differential
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.EquationBridge
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.ProductCover
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.CalculusAssembly
import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.Choice
import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.Regularity










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Set

universe u v

namespace PoincareConjecture

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

def CompatibleSpacetimeCylinder.pullbackMetricGeometry
    {K : SpacetimeInterval} {T : SmoothSpacetimeInterval K}
    {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (e : CompatibleSpacetimeCylinder F T C) : SpacetimeCylinderMetric e where
  metric := e.toMovingSpacetimeGauge.geometry.metric
  smooth := e.toMovingSpacetimeGauge.geometry.smooth
  spatialTangentEquiv := e.toMovingSpacetimeGauge.geometry.spatialTangentEquiv
  spatialTangentEquiv_eq := e.toMovingSpacetimeGauge.geometry.spatialTangentEquiv_eq
  metric_eq := e.toMovingSpacetimeGauge.geometry.metric_eq

theorem spacetimeGaugeTheory_of_moving_calculus
    (hMetric : M12MetricPredecessors.{v} n)
    (D : LeafwiseLeviCivitaFamily F S) (T : SpacetimeIntervalSystem)
    (hCalc : ∀ (C : Type v) [TopologicalSpace C]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
      (K : SpacetimeInterval) (e : MovingSpacetimeGauge F (T.interval K) C)
      (G : MovingSpacetimeGaugeGeometry e) (c : MetricLeviCivitaFamily G.metric),
      MovingGaugeCalculus D G c) : SpacetimeGaugeTheory.{u, v} D T := by
  refine
    { moving_geometry := fun _ _ _ _ _ e => ⟨e.geometry⟩
      moving_connections := fun _ _ _ _ _ _ G => hMetric.exists_gaugeMetricLeviCivitaFamily G
      moving_calculus := hCalc
      compatible_zero_drift := fun _ _ _ _ _ e G => compatibleMovingGaugeDrift_zero e G
      compatible_equivalence := ?_
      compatible_ordinary := ?_
      compatible_realization := ?_
      cover_converse := ?_ }
  · intro C _ _ _ K e G c
    exact compatible_equivalence_of_calculus_zero_drift D e G c
      (hCalc C K e.toMovingSpacetimeGauge G.toMovingSpacetimeGaugeGeometry c)
      (compatibleMovingGaugeDrift_zero e G)
  · intro C _ _ _ K e G h
    obtain ⟨c⟩ := hMetric.exists_gaugeMetricLeviCivitaFamily G.toMovingSpacetimeGaugeGeometry
    exact compatible_ordinary_of_calculus_zero_drift D e G c
      (hCalc C K e.toMovingSpacetimeGauge G.toMovingSpacetimeGaugeGeometry c)
      (compatibleMovingGaugeDrift_zero e G) h
  · intro h C _ _ _ K e
    let G := e.pullbackMetricGeometry
    obtain ⟨c⟩ := hMetric.exists_gaugeMetricLeviCivitaFamily G.toMovingSpacetimeGaugeGeometry
    refine ⟨G, compatible_ordinary_of_calculus_zero_drift D e G c
      (hCalc C K e.toMovingSpacetimeGauge G.toMovingSpacetimeGaugeGeometry c)
      (compatibleMovingGaugeDrift_zero e G) ?_⟩
    exact fun p _ u v => h p u v
  · intro B C _ _ _ K e G c hc hp
    exact cover_converse_of_calculus_zero_drift D T B C K e G c
      (fun b => hCalc (C b) (K b) (e b).toMovingSpacetimeGauge
        (G b).toMovingSpacetimeGaugeGeometry (c b))
      (fun b => compatibleMovingGaugeDrift_zero (e b) (G b)) hc hp



theorem spacetimeGaugeTheory
    (hMetric : M12MetricPredecessors.{v} n)
    (D : LeafwiseLeviCivitaFamily F S) (T : SpacetimeIntervalSystem) :
    SpacetimeGaugeTheory.{u, v} D T := by
  apply spacetimeGaugeTheory_of_moving_calculus hMetric D T
  intro C _ _ _ K e G c
  exact movingGaugeCalculus D G c

theorem SpacetimeGaugeTheory.adapted_equation_iff
    {D : LeafwiseLeviCivitaFamily F S} {T : SpacetimeIntervalSystem}
    (h : SpacetimeGaugeTheory.{u, 0} D T) (cover : SpacetimeGaugeCover F T) :
    IntrinsicGeneralizedRicciEquation D ↔
      ∀ b, ∀ c : MetricLeviCivitaFamily (cover.metric b).metric,
        OrdinaryMetricRicciPDE (cover.metric b).metric c (cover.interval b) := by
  constructor
  · intro he b c
    apply (h.compatible_equivalence (cover.spatial b) (cover.interval b)
      (cover.cylinder b) (cover.metric b) c).mp
    exact fun p _ u v => he p u v
  · intro he
    let c : ∀ b, MetricLeviCivitaFamily (cover.metric b).metric := fun b =>
      (h.moving_connections (cover.spatial b) (cover.interval b)
        (cover.cylinder b).toMovingSpacetimeGauge
        (cover.metric b).toMovingSpacetimeGaugeGeometry).some
    exact h.cover_converse cover.index (fun b => cover.spatial b) cover.interval
      cover.cylinder cover.metric c cover.covers (fun b => he b (c b))

namespace OrdinaryProductSpacetimeConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : ℝ → RiemannianMetric n M}

theorem intrinsicEquation_iff_on_productCylinder (P : OrdinaryProductSpacetimeConclusion g I)
    (D : LeafwiseLeviCivitaFamily P.spacetime P.slices) :
    IntrinsicGeneralizedRicciEquation D ↔
      IntrinsicGeneralizedRicciEquationOn D (range P.productCylinder.toSpacetime) := by
  constructor
  · exact fun h p _ u v => h p u v
  · intro h p u v
    exact h p ⟨p, P.productCylinder_eq p⟩ u v

def ricciGeometry (P : OrdinaryProductSpacetimeConclusion g I)
    (D : LeafwiseLeviCivitaFamily P.spacetime P.slices)
    (hGauge : SpacetimeGaugeTheory.{u, u} D P.timeIntervals) : OrdinaryProductRicciGeometry g I where
  product := P
  cover := P.gaugeCover
  leafwiseConnection := D
  equation_iff := by
    intro c
    rw [P.intrinsicEquation_iff_on_productCylinder D]
    have h := hGauge.compatible_equivalence M I P.productCylinder P.productMetric
    rw [P.productMetric_eq] at h
    exact h c
  ordinary_from_equation := fun h => hGauge.compatible_ordinary M I
    P.productCylinder P.productMetric ((P.intrinsicEquation_iff_on_productCylinder D).mp h)

end OrdinaryProductSpacetimeConclusion



theorem exists_ordinaryProductRicciGeometry
    (hGeometry : GeneralizedSpacetimeGeometryTheory.{u} n)
    (hMetric : M12MetricPredecessors.{u} n)
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] [Nonempty M]
    (g : ℝ → RiemannianMetric n M) (I : SpacetimeInterval)
    (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain) :
    Nonempty (OrdinaryProductRicciGeometry g I) := by
  obtain ⟨P⟩ := hGeometry.ordinary_product M g I hg
  obtain ⟨D⟩ := hMetric.exists_leafwiseLeviCivitaFamily P.slices
  exact ⟨P.ricciGeometry D (spacetimeGaugeTheory hMetric D P.timeIntervals)⟩



theorem generalizedRicciGaugeTheory_of_calculus
    (hGeometry : GeneralizedSpacetimeGeometryTheory.{u} n)
    (hMetric : M12MetricPredecessors.{u} n)
    (hHorizontal : ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
      (I : SpacetimeInterval) (F : GeneralizedFlowSpacetime n X time I)
      (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) (T : SpacetimeIntervalSystem)
      (_cover : SpacetimeGaugeCover F T) (D : LeafwiseLeviCivitaFamily F S),
      HorizontalRicciCalculus D)
    (hGauges : ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
      (I : SpacetimeInterval) (F : GeneralizedFlowSpacetime n X time I)
      (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) (T : SpacetimeIntervalSystem)
      (_cover : SpacetimeGaugeCover F T) (D : LeafwiseLeviCivitaFamily F S),
      SpacetimeGaugeTheory.{u, u} D T)
    (hCoordinates : ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
      (I : SpacetimeInterval) (F : GeneralizedFlowSpacetime n X time I)
      (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) (T : SpacetimeIntervalSystem)
      (_cover : SpacetimeGaugeCover F T) (D : LeafwiseLeviCivitaFamily F S),
      SpacetimeGaugeTheory.{u, 0} D T) : GeneralizedRicciGaugeTheory.{u} n := by
  refine
    { leafwise_calculus := ?_
      gauges := hGauges
      coordinate_gauges := hCoordinates
      adapted_equation := ?_
      ordinary_product := ?_ }
  · intro X _ time I F S T cover
    exact ⟨hMetric.exists_leafwiseLeviCivitaFamily S,
      hHorizontal X time I F S T cover⟩
  · intro X _ time I F S T cover D
    exact (hCoordinates X time I F S T cover D).adapted_equation_iff cover
  · intro M _ _ _ _ _ _ g I hg
    obtain ⟨P⟩ := hGeometry.ordinary_product M g I hg
    obtain ⟨D⟩ := hMetric.exists_leafwiseLeviCivitaFamily P.slices
    exact ⟨P.ricciGeometry D
      (hGauges (I.domain × M) (fun p => p.1.val) I P.spacetime
        P.slices P.timeIntervals P.gaugeCover D)⟩



theorem generalizedRicciGaugeTheory_of_horizontal_calculus
    (hGeometry : GeneralizedSpacetimeGeometryTheory.{u} n)
    (hMetric : M12MetricPredecessors.{u} n)
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hHorizontal : ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
      (I : SpacetimeInterval) (F : GeneralizedFlowSpacetime n X time I)
      (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) (T : SpacetimeIntervalSystem)
      (_cover : SpacetimeGaugeCover F T) (D : LeafwiseLeviCivitaFamily F S),
      HorizontalRicciCalculus D) : GeneralizedRicciGaugeTheory.{u} n := by
  apply generalizedRicciGaugeTheory_of_calculus hGeometry hMetric hHorizontal
  · intro X _ time I F S T cover D
    exact spacetimeGaugeTheory hMetric D T
  · intro X _ time I F S T cover D
    exact spacetimeGaugeTheory hCoordinates D T



theorem generalizedRicciGaugeGeometry_proof (n : ℕ)
    (hGeometry : GeneralizedSpacetimeGeometryTheory.{u} n)
    (hMetric : M12MetricPredecessors.{u} n)
    (hCoordinates : M12MetricPredecessors.{0} n) :
    GeneralizedRicciGaugeTheory.{u} n := by
  apply generalizedRicciGaugeTheory_of_horizontal_calculus hGeometry hMetric hCoordinates
  intro X _ time I F S T cover D
  exact horizontalRicciCalculus_of_adapted_cover hMetric hCoordinates D T cover

end

end PoincareConjecture
