import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Attainment.Gauge.GaugeActionLimit

/-!
# Finite actual gauge primitives

Proposition 16.4 and Claim 16.25, pp. 369 and 389-390. This local record
retains the disjoint action partition, its overlapping gauge intervals
and the actual weak spatial primitives. It assumes no attainment,
minimality or regularity of the underlying continuous curve.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareMT.M08
export PoincareMT.LGeometry (ChartL2)
end PoincareMT.M08

namespace PoincareMT.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}

/-- The finite geometric and weak-primitive data used by recovery in
the direct method. Source: Proposition 16.4, p. 369. -/
structure GaugePrimitivePartition (gamma : ℝ → G.Point) (a b : ℝ) where
  count : ℕ
  node : Fin (count + 1) → ℝ
  monotone : Monotone node
  first : node 0 = a
  last : node (Fin.last count) = b
  gauge : Fin count → AttainmentGauge G
  left : Fin count → ℝ
  right : Fin count → ℝ
  big_subset : ∀ i, Icc (left i) (right i) ⊆ Icc a b
  core_subset : ∀ i, Icc (node i.castSucc) (node i.succ) ⊆ Icc (left i) (right i)
  near : ∀ i s, s ∈ Icc (node i.castSucc) (node i.succ) →
    Icc (left i) (right i) ∈ 𝓝[Icc a b] s
  source : ∀ i, MapsTo gamma (Icc (left i) (right i)) (gauge i).source
  velocity : ∀ i : Fin count,
    M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (node i.castSucc) (node i.succ)
  primitive : ∀ i s, s ∈ Icc (node i.castSucc) (node i.succ) →
    ((gauge i).lift (gamma s)).2.val = ((gauge i).lift (gamma (node i.castSucc))).2.val +
      ∫ r in node i.castSucc..s, velocity i r

/-- Only the disjoint pieces enter the action, even though their
inverse gauges extend to overlapping intervals. Source: equation (6.2)
and Proposition 16.4, pp. 106, 369. -/
noncomputable def GaugePrimitivePartition.action {gamma : ℝ → G.Point} {a b : ℝ}
    (R : GaugePrimitivePartition gamma a b) : ℝ :=
  ∑ i, gaugePieceAction (R.gauge i) gamma (R.velocity i)

end PoincareMT.Proofs.M46
