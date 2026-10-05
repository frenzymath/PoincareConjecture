import PoincareLib.Geometry.Spacetime.Horizontal.Basic
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Moving

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/M12GaugeTransport.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Declaration bodies are unchanged;
only imports and module placement differ. See
`references/ricci-flow/mapher/spacetime-port.json`. -/

/-!
# Actual section transport through a moving gauge

Horizontal sections are pulled back through the actual spatial differential.
Their time derivative fixes the spatial point and differentiates into its
normed tangent fiber using the selected interval charts, including endpoints.
No connection law or gauge equation is assumed by these raw operators.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  {e : MovingSpacetimeGauge F T C}

/-- Pull back a horizontal section by the actual spatial tangent equivalence. -/
noncomputable def pullbackHorizontalSection (G : MovingSpacetimeGaugeGeometry e)
    (V : HorizontalSection F) (t : T.Point) (x : C) : TangentSpace (𝓡 n) x :=
  (G.spatialTangentEquiv t x).symm (V (e.toSpacetime (t, x)))

/-- The actual time derivative at fixed spatial point, normalized by the
positive tangent of the selected interval rather than a chart-coordinate sign. -/
noncomputable def movingGaugeSectionTimeDerivative (G : MovingSpacetimeGaugeGeometry e)
    (V : HorizontalSection F) (t : T.Point) (x : C) : TangentSpace (𝓡 n) x :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : C → Type _) :=
    ⟨(G.metric t.val).toRiemannianMetric⟩
  mfderiv (𝓡∂ 1) (𝓘(ℝ, TangentSpace (𝓡 n) x))
    (fun s : T.Point ↦ pullbackHorizontalSection G V s x) t (T.positiveTangent t)

end PoincareMT
