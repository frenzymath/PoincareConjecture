import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Provider
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Compact.Data
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Geometry
import PoincareLib.Geometry.RicciFlow.Rescaling.Theory

/-! Adapted from Mapher `PoincareMT/Proofs/M15/Prop8_2_CylinderFlow.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

/-!
# The ordinary flow on the actual based cylinder

Morgan-Tian Definition 3.38 and Remark 3.37, pp. 60-61, used in Claim 8.5,
p. 172. The flow retains the actual cylinder metric and chosen compatible
connection. Its terminal source map pulls back the selected slice metric.
See `references/ricci-flow/mapher/noncollapse/derivations/2026-09-20-cylinder-flow.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.Generalized.Noncollapse

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T r : ℝ} {x : (G.slices T).Point} {K : SpacetimeInterval}
  {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  [T2Space C] [SecondCountableTopology C]

/-- The actual cylinder carries an ordinary flow with exactly its metric,
scalar curvature and full curvature norm. Source: Definition 3.38 and
Remark 3.37, pp. 60-61, as used in Claim 8.5, p. 172. -/
theorem actualBallCylinder_exists_flow
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (B : M15ActualBallCylinder G T x r K C) :
    ∃ F : RicciFlow n C K.domain, F.metric = B.metric.metric ∧
      (∀ (t : (G.timeIntervals.interval K).Point) (c : C),
        (F.connection t.val).curvatureTensorNorm c =
          horizontalCurvatureNorm G.leafwise (B.embedding.toSpacetime (t, c))) ∧
      (∀ (t : (G.timeIntervals.interval K).Point) (c : C),
        (F.connection t.val).scalarCurvature c =
          horizontalScalarCurvature G.leafwise (B.embedding.toSpacetime (t, c))) := by
  have H := hM12.gauges X time I G.spacetime G.slices G.timeIntervals
    G.gaugeCover G.leafwise
  obtain ⟨c⟩ := H.moving_connections C K B.embedding.toMovingSpacetimeGauge
    B.metric.toMovingSpacetimeGaugeGeometry
  have heq : IntrinsicGeneralizedRicciEquationOn G.leafwise
      (Set.range B.embedding.toSpacetime) := fun p _ u v => G.ricciEquation p u v
  have hPDE := (H.compatible_equivalence C K B.embedding B.metric c).mp heq
  let F : RicciFlow n C K.domain :=
    { metric := B.metric.metric
      connection := c
      interval := K.ordConnected
      nontrivial := K.nontrivial
      smooth := B.metric.smooth
      equation := hPDE }
  have hcalc := H.moving_calculus C K B.embedding.toMovingSpacetimeGauge
    B.metric.toMovingSpacetimeGaugeGeometry c
  exact ⟨F, rfl, hcalc.curvature_norm_eq, hcalc.scalar_eq⟩

/-- The terminal slice map is the specified source map on every source
point. Source: Definition 3.38, p. 61, and the based cylinder in Claim 8.5,
p. 172. -/
theorem actualBallCylinder_terminal_sliceMap_eq
    (B : M15ActualBallCylinder G T x r K C) :
    movingGaugeSliceMap B.embedding.toMovingSpacetimeGauge G.slices
      ⟨T, B.base_mem⟩ = B.source_map := by
  funext c
  exact Subtype.ext (B.based c)

/-- The actual terminal source map pulls back the selected slice metric
to the cylinder metric. Source: Definition 3.38, p. 61, used for the
metric comparison in Claim 8.5, p. 172. -/
theorem actualBallCylinder_terminal_metric_pullback
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (B : M15ActualBallCylinder G T x r K C)
    (c : C) (u v : TangentSpace (𝓡 n) c) :
    (G.slices T).metricOnPoints.inner (B.source_map c)
      (mfderiv (𝓡 n) (𝓡 n) B.source_map c u)
      (mfderiv (𝓡 n) (𝓡 n) B.source_map c v) =
        (B.metric.metric T).inner c u v := by
  have H := hM12.gauges X time I G.spacetime G.slices G.timeIntervals
    G.gaugeCover G.leafwise
  obtain ⟨D⟩ := H.moving_connections C K B.embedding.toMovingSpacetimeGauge
    B.metric.toMovingSpacetimeGaugeGeometry
  have hcalc := H.moving_calculus C K B.embedding.toMovingSpacetimeGauge
    B.metric.toMovingSpacetimeGaugeGeometry D
  have h := hcalc.slice_metric_eq ⟨T, B.base_mem⟩ c u v
  rw [actualBallCylinder_terminal_sliceMap_eq B] at h
  exact h

end PoincareMT.Generalized.Noncollapse
