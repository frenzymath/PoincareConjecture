import PoincareConjecture.Definitions.M12HorizontalCalculus
import PoincareConjecture.Definitions.M12MovingGauge

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  {e : MovingSpacetimeGauge F T C}

noncomputable def pullbackHorizontalSection (G : MovingSpacetimeGaugeGeometry e)
    (V : HorizontalSection F) (t : T.Point) (x : C) : TangentSpace (𝓡 n) x :=
  (G.spatialTangentEquiv t x).symm (V (e.toSpacetime (t, x)))

noncomputable def movingGaugeSectionTimeDerivative (G : MovingSpacetimeGaugeGeometry e)
    (V : HorizontalSection F) (t : T.Point) (x : C) : TangentSpace (𝓡 n) x :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : C → Type _) :=
    ⟨(G.metric t.val).toRiemannianMetric⟩
  mfderiv (𝓡∂ 1) (𝓘(ℝ, TangentSpace (𝓡 n) x))
    (fun s : T.Point ↦ pullbackHorizontalSection G V s x) t (T.positiveTangent t)

end PoincareConjecture
