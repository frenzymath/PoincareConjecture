import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.RegularSets.NestedBallClosure
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.RegularSets.Regularity

/-!
# A compact local ball with room inside an open restriction

A compact ball closure at radius delta and containment of the ball of
radius twice delta give literal delta-regularity in the open metric.
Source: Morgan--Tian Definition 5.1 and Proposition 10.7, pp. 83 and
253-254; M28 derivation 92, simultaneous source-path regularity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareMT.M28

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- The doubled open ball captures the compact closure before restricting
the metric. No completeness or equality of arbitrary distances is used.
Source: Definition 5.1 and Proposition 10.7; M28 derivation 92. -/
theorem mem_regularPoints_intrinsicOpenMetric_of_compact_ball
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M) (p : U)
    {delta : ℝ} (hdelta : 0 < delta)
    (hcompact : IsCompact (closure (g.ball (p : M) delta)))
    (hball : g.ball (p : M) (2 * delta) ⊆ (U : Set M)) :
    p ∈ regularPoints (intrinsicOpenMetric g U) delta := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  have hclosed : IsClosed {x : M | g.edist (p : M) x ≤ ENNReal.ofReal delta} :=
    isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hsub : g.ball (p : M) delta ⊆
      {x : M | g.edist (p : M) x ≤ ENNReal.ofReal delta} := by
    intro x hx
    change g.edist (p : M) x < ENNReal.ofReal delta at hx
    exact hx.le
  have hclosure : closure (g.ball (p : M) delta) ⊆ (U : Set M) := by
    intro x hx
    have hle : g.edist (p : M) x ≤ ENNReal.ofReal delta :=
      closure_minimal hsub hclosed hx
    apply hball
    exact hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
  have hcompactU := intrinsicOpenMetric_isCompact_closure_ball g U p hcompact hclosure
  intro r hr
  apply hcompactU.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro x hx
  exact hx.trans_le (ENNReal.ofReal_le_ofReal hr.le)

end PoincareMT.M28
