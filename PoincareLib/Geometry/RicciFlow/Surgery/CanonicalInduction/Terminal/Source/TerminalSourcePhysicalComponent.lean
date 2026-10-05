import PoincareLib.Geometry.Riemannian.Metric.ConnectedComponent
import PoincareLib.Geometry.Riemannian.Distance.Basic
import PoincareLib.Geometry.RicciFlow.Compactness.GeometricLimit.BoundaryCoverage

/-!
# The finite metric of the actual physical base component

The unchanged component inclusion preserves intrinsic distance and
every ball. Its true connectedness supplies finite distances without
any connectedness assumption on the whole physical slice or source.
MT Theorem 5.11; terminal-source-physical-component.md, G9a.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- The actual component metric, retaining its original manifold topology. -/
@[instance_reducible] noncomputable def terminalSourceComponentMetricSpace
    (g : RiemannianMetric 3 M) (p : M) :
    MetricSpace (Poincare.connectedComponentOpens E p) :=
  let C := Poincare.connectedComponentOpens E p
  let h := g.connectedComponentMetric p
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : C → Type _) :=
    ⟨h.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace (𝓡 3) : C → Type _) :=
    ⟨⟨h.inner, h.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  letI : EMetricSpace C := EMetricSpace.ofRiemannianMetric (𝓡 3) C
  EMetricSpace.toMetricSpace (fun x y => h.edist_ne_top x y)

/-- Every real and extended distance is the original ambient readout. -/
theorem terminalSourceComponent_distances (g : RiemannianMetric 3 M) (p : M) :
    let C := Poincare.connectedComponentOpens E p
    letI := terminalSourceComponentMetricSpace g p
    ∀ x y : C, edist x y = g.edist x.val y.val ∧
      dist x y = (g.edist x.val y.val).toReal := by
  let C := Poincare.connectedComponentOpens E p
  let h := g.connectedComponentMetric p
  let : MetricSpace C := terminalSourceComponentMetricSpace g p
  change ∀ x y : C, edist x y = g.edist x.val y.val ∧
    dist x y = (g.edist x.val y.val).toReal
  intro x y
  have heq : h.edist x y = g.edist x.val y.val :=
    RiemannianMetric.edist_subtype_val isClosed_connectedComponent g h
      (fun _ _ _ => rfl) x y
  exact ⟨heq, congrArg ENNReal.toReal heq⟩

/-- Actual component balls have the same ambient image and are connected
in the sense required by the original terminal chart extraction. -/
theorem terminalSourceComponent_balls (g : RiemannianMetric 3 M) (p : M) :
    let C := Poincare.connectedComponentOpens E p
    let h := g.connectedComponentMetric p
    letI := terminalSourceComponentMetricSpace g p
    ∀ (x : C) (r : ℝ), Metric.ball x r = h.ball x r ∧
      Subtype.val '' Metric.ball x r = g.ball x.val r ∧
      IsPreconnected (Metric.ball x r) := by
  let C := Poincare.connectedComponentOpens E p
  let h := g.connectedComponentMetric p
  let : MetricSpace C := terminalSourceComponentMetricSpace g p
  change ∀ (x : C) (r : ℝ), Metric.ball x r = h.ball x r ∧
    Subtype.val '' Metric.ball x r = g.ball x.val r ∧
    IsPreconnected (Metric.ball x r)
  intro x r
  have hball : Metric.ball x r = h.ball x r := by
    ext y
    change dist y x < r ↔ h.edist x y < ENNReal.ofReal r
    rw [dist_comm]
    change (h.edist x y).toReal < r ↔ h.edist x y < ENNReal.ofReal r
    exact (ENNReal.lt_ofReal_iff_toReal_lt (h.edist_ne_top x y)).symm
  refine ⟨hball, ?_, ?_⟩
  · rw [hball]
    exact RiemannianMetric.image_ball_subtype_val isClosed_connectedComponent g h
      (fun _ _ _ => rfl) x r
  · rw [hball]
    exact h.isPreconnected_ball x r

end PoincareMT.M47
