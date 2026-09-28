import PoincareConjecture.Statements.M12MovingGaugeTheory
import PoincareConjecture.Statements.M12GeneralizedEquation
import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Interval.UniqueDifferential

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture

open Set

section Moving

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  {e : MovingSpacetimeGauge F T C}

theorem movingGaugeEquation_iff_of_metric_derivative_ricci_eq
    (D : LeafwiseLeviCivitaFamily F S)
    (G : MovingSpacetimeGaugeGeometry e)
    (c : MetricLeviCivitaFamily G.metric)
    (hMetric : ∀ (t : T.Point) (x : C) (u v : TangentSpace (𝓡 n) x),
      HasDerivWithinAt (fun s ↦ (G.metric s).inner x u v)
        (horizontalMetricLieDerivative F (e.toSpacetime (t, x))
          (G.spatialTangentEquiv t x u) (G.spatialTangentEquiv t x v) -
          ordinaryMetricLieDerivative (G.metric t.val) (c t.val)
            (movingGaugeDrift G t) x u v) K.domain t.val)
    (hRicci : ∀ (t : T.Point) (x : C) (u v : TangentSpace (𝓡 n) x),
      (c t.val).ricci x u v = horizontalRicci D (e.toSpacetime (t, x))
        (G.spatialTangentEquiv t x u) (G.spatialTangentEquiv t x v)) :
    IntrinsicGeneralizedRicciEquationOn D (Set.range e.toSpacetime) ↔
      MovingGaugeRicciPDE G c := by
  constructor
  · intro h t' ht' x' u v
    let t : T.Point := ⟨t', ht'⟩
    have hpoint := h (e.toSpacetime (t, x')) ⟨(t, x'), rfl⟩
      (G.spatialTangentEquiv t x' u)
      (G.spatialTangentEquiv t x' v)
    have hderiv := hMetric t x' u v
    rw [← hRicci t x' u v] at hpoint
    rw [hpoint] at hderiv
    simpa [t] using hderiv
  · intro h p hp u v
    rcases hp with ⟨⟨t, x⟩, rfl⟩
    let u' : TangentSpace (𝓡 n) x := (G.spatialTangentEquiv t x).symm u
    let v' : TangentSpace (𝓡 n) x := (G.spatialTangentEquiv t x).symm v
    have hPDE := h (t : ℝ) t.property x u' v'
    have hMetric' := hMetric t x u' v'
    have hRicci' := hRicci t x u' v'
    have hUnique : UniqueDiffWithinAt ℝ K.domain (t : ℝ) :=
      uniqueDiffWithinAt_of_spacetimeInterval K t
    have hEq :
        horizontalMetricLieDerivative F (e.toSpacetime (t, x))
            (G.spatialTangentEquiv t x u') (G.spatialTangentEquiv t x v') -
          ordinaryMetricLieDerivative (G.metric t.val) (c t.val)
            (movingGaugeDrift G t) x u' v' =
        -2 * (c t.val).ricci x u' v' -
          ordinaryMetricLieDerivative (G.metric t.val) (c t.val)
            (movingGaugeDrift G t) x u' v' := by
      exact hUnique.eq_deriv K.domain hMetric' hPDE
    rw [hRicci'] at hEq
    have hEq' :
        horizontalMetricLieDerivative F (e.toSpacetime (t, x)) u v =
          -2 * horizontalRicci D (e.toSpacetime (t, x)) u v := by
      simpa [u', v'] using (show
        horizontalMetricLieDerivative F (e.toSpacetime (t, x))
            (G.spatialTangentEquiv t x u') (G.spatialTangentEquiv t x v') =
          -2 * horizontalRicci D (e.toSpacetime (t, x))
            (G.spatialTangentEquiv t x u') (G.spatialTangentEquiv t x v') by
        linarith)
    exact hEq'

theorem movingGaugeEquation_iff_of_calculus
    (D : LeafwiseLeviCivitaFamily F S)
    (G : MovingSpacetimeGaugeGeometry e)
    (c : MetricLeviCivitaFamily G.metric)
    (h : MovingGaugeCalculus D G c) :
    IntrinsicGeneralizedRicciEquationOn D (Set.range e.toSpacetime) ↔
      MovingGaugeRicciPDE G c :=
  movingGaugeEquation_iff_of_metric_derivative_ricci_eq D G c
    h.metric_derivative h.ricci_eq

theorem ordinaryMetricLieDerivative_zero
    {n : ℕ} {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C]
    (g : RiemannianMetric n C) (D : LeviCivitaData g)
    (x : C) (u v : TangentSpace (𝓡 n) x) :
    ordinaryMetricLieDerivative g D (fun _ ↦ 0) x u v = 0 := by
  change g.inner x (D.connection 0 x u) v + g.inner x u (D.connection 0 x v) = 0
  rw [show D.connection 0 = 0 by simp]
  simp

theorem movingGaugePDE_iff_ordinaryMetricRicciPDE_of_zero_drift
    {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
    {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
    {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    {e : MovingSpacetimeGauge F T C}
    (G : MovingSpacetimeGaugeGeometry e)
    (c : MetricLeviCivitaFamily G.metric)
    (hzero : ∀ (t : T.Point) (x : C), movingGaugeDrift G t x = 0) :
    MovingGaugeRicciPDE G c ↔ OrdinaryMetricRicciPDE G.metric c K := by
  constructor
  · intro h t ht x u v
    have h' := h t ht x u v
    have hz : movingGaugeDrift G ⟨t, ht⟩ = fun _ ↦ 0 := by
      funext y
      exact hzero ⟨t, ht⟩ y
    rw [hz] at h'
    simpa [ordinaryMetricLieDerivative_zero] using h'
  · intro h t ht x u v
    have h' := h t ht x u v
    have hz : movingGaugeDrift G ⟨t, ht⟩ = fun _ ↦ 0 := by
      funext y
      exact hzero ⟨t, ht⟩ y
    rw [hz]
    simpa [ordinaryMetricLieDerivative_zero] using h'

section Witness

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]

theorem ordinaryGaugeWitness_of_ordinaryPDE
    (D : LeafwiseLeviCivitaFamily F S)
    (e : CompatibleSpacetimeCylinder F T C)
    (G : SpacetimeCylinderMetric e)
    (c : MetricLeviCivitaFamily G.metric)
    (hPDE : OrdinaryMetricRicciPDE G.metric c K)
    (hRicci : ∀ (t : T.Point) (x : C) (u v : TangentSpace (𝓡 n) x),
      (c t.val).ricci x u v =
        horizontalRicci D (e.toSpacetime (t, x))
          (G.spatialTangentEquiv t x u) (G.spatialTangentEquiv t x v)) :
    Nonempty (OrdinaryGaugeWitness D e G) := by
  let flow : RicciFlow n C K.domain :=
    { metric := G.metric
      connection := c
      interval := K.ordConnected
      nontrivial := K.nontrivial
      smooth := G.smooth
      equation := hPDE }
  let witness : OrdinaryGaugeWitness D e G :=
    { flow := flow
      metric_eq := rfl
      metric_pullback := by
        intro t x u v
        exact G.metric_eq t x u v
      ricci_pullback := by
        intro t x u v
        exact hRicci t x u v }
  exact ⟨witness⟩

theorem compatible_equivalence_of_calculus_zero_drift
    (D : LeafwiseLeviCivitaFamily F S)
    (e : CompatibleSpacetimeCylinder F T C)
    (G : SpacetimeCylinderMetric e)
    (c : MetricLeviCivitaFamily G.metric)
    (hCalc : MovingGaugeCalculus D
      G.toMovingSpacetimeGaugeGeometry c)
    (hzero : ∀ (t : T.Point) (x : C),
      movingGaugeDrift G.toMovingSpacetimeGaugeGeometry t x = 0) :
    IntrinsicGeneralizedRicciEquationOn D (Set.range e.toSpacetime) ↔
      OrdinaryMetricRicciPDE G.metric c K := by
  exact (movingGaugeEquation_iff_of_calculus D
      G.toMovingSpacetimeGaugeGeometry c hCalc).trans
    (movingGaugePDE_iff_ordinaryMetricRicciPDE_of_zero_drift
      G.toMovingSpacetimeGaugeGeometry c hzero)

theorem compatible_ordinary_of_calculus_zero_drift
    (D : LeafwiseLeviCivitaFamily F S)
    (e : CompatibleSpacetimeCylinder F T C)
    (G : SpacetimeCylinderMetric e)
    (c : MetricLeviCivitaFamily G.metric)
    (hCalc : MovingGaugeCalculus D
      G.toMovingSpacetimeGaugeGeometry c)
    (hzero : ∀ (t : T.Point) (x : C),
      movingGaugeDrift G.toMovingSpacetimeGaugeGeometry t x = 0)
    (hIntrinsic : IntrinsicGeneralizedRicciEquationOn D (Set.range e.toSpacetime)) :
    Nonempty (OrdinaryGaugeWitness D e G) := by
  apply ordinaryGaugeWitness_of_ordinaryPDE D e G c
    ((compatible_equivalence_of_calculus_zero_drift D e G c hCalc hzero).mp
      hIntrinsic)
  exact hCalc.ricci_eq

theorem cover_converse_of_calculus_zero_drift
    {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
    {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
    {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}
    (D : LeafwiseLeviCivitaFamily F S)
    (T : SpacetimeIntervalSystem)
    (B : Type u) (C : B → Type v)
    [∀ b, TopologicalSpace (C b)]
    [∀ b, ChartedSpace (EuclideanSpace ℝ (Fin n)) (C b)]
    [∀ b, IsManifold (𝓡 n) ∞ (C b)]
    (K : B → SpacetimeInterval)
    (e : ∀ b, CompatibleSpacetimeCylinder F (T.interval (K b)) (C b))
    (G : ∀ b, SpacetimeCylinderMetric (e b))
    (c : ∀ b, MetricLeviCivitaFamily (G b).metric)
    (hCalc : ∀ b, MovingGaugeCalculus D
      (G b).toMovingSpacetimeGaugeGeometry (c b))
    (hzero : ∀ b (t : (T.interval (K b)).Point) (x : C b),
      movingGaugeDrift (G b).toMovingSpacetimeGaugeGeometry t x = 0)
    (hcover : ∀ p : F.Point, ∃ b, ∃ q, (e b).toSpacetime q = p)
    (hPDE : ∀ b, OrdinaryMetricRicciPDE (G b).metric (c b) (K b)) :
    IntrinsicGeneralizedRicciEquation D := by
  intro p u v
  obtain ⟨b, q, hq⟩ := hcover p
  subst p
  have hEq := compatible_equivalence_of_calculus_zero_drift D (e b) (G b)
    (c b) (hCalc b) (hzero b)
  have hLocal := hEq.mpr (hPDE b)
    ((e b).toSpacetime q) ⟨q, rfl⟩ u v
  exact hLocal

end Witness

end Moving

end PoincareConjecture
