import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.OpenGeometry.OpenMetricBalls

/-!
# Compact ball closures through two actual open restrictions

Morgan--Tian Definition 5.1 and Claim 10.5, pp. 83 and 251-252.
An ambient compact ball closure contained in the final open region
remains compact for the literal nested inclusion metric. Only the
captured balls are identified, not arbitrary distances. M28 derivation 87.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

/-- A compact ambient ball closure contained in an open region gives
the same-radius compact closure for its inclusion metric (Definition 5.1;
Claim 10.5; M28 derivation 87). -/
theorem intrinsicOpenMetric_isCompact_closure_ball
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M) (p : U) {r : ℝ}
    (hcompact : IsCompact (closure (g.ball (p : M) r)))
    (hclosure : closure (g.ball (p : M) r) ⊆ (U : Set M)) :
    IsCompact (closure ((intrinsicOpenMetric g U).ball p r)) := by
  rw [intrinsicOpenMetric_closure_ball_eq_preimage g U p
    (subset_closure.trans hclosure)]
  apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hcompact
  intro x hx
  exact ⟨⟨x, hclosure hx⟩, rfl⟩

/-- Ambient compact capture inside two nested open regions survives
both actual inclusion metrics (Definition 5.1; Claim 10.5; derivation 87). -/
theorem nested_intrinsicOpenMetric_isCompact_closure_ball
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens U) (p : V) {r : ℝ}
    (hcompact : IsCompact (closure (g.ball ((p : U) : M) r)))
    (hclosure : closure (g.ball ((p : U) : M) r) ⊆
      (Subtype.val : U → M) '' (V : Set U)) :
    IsCompact (closure ((intrinsicOpenMetric (intrinsicOpenMetric g U) V).ball p r)) := by
  have hU : closure (g.ball ((p : U) : M) r) ⊆ (U : Set M) := by
    intro x hx
    obtain ⟨y, _hy, rfl⟩ := hclosure hx
    exact y.property
  have hcompactU := intrinsicOpenMetric_isCompact_closure_ball g U (p : U) hcompact hU
  have hV : closure ((intrinsicOpenMetric g U).ball (p : U) r) ⊆ (V : Set U) := by
    rw [intrinsicOpenMetric_closure_ball_eq_preimage g U (p : U)
      (subset_closure.trans hU)]
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hclosure hy
    have heq : z = y := Subtype.ext hzy
    exact heq ▸ hz
  exact intrinsicOpenMetric_isCompact_closure_ball (intrinsicOpenMetric g U) V p hcompactU hV

end PoincareMT.M28
