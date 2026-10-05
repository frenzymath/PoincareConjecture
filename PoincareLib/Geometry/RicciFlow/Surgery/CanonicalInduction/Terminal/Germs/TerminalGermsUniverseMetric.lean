import PoincareLib.Geometry.Manifold.Lift
import PoincareLib.Geometry.Riemannian.Metric.Diffeomorph
import PoincareLib.Geometry.Riemannian.Metric.LocalDiffeomorph

/-!
# The same complete terminal metric in the required universe

The transported atlas makes the literal down map a diffeomorphism.
Its actual pullback metric preserves intrinsic distances and completeness.
Source: MT Theorems 5.9-5.11, pp. 88-90;
derivations/terminal-germs-overlap.md, Stage A5k.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

universe u v

namespace PoincareMT.M47

/-- Universe lifting preserves the actual complete terminal metric and
every intrinsic extended distance through the literal down map. -/
theorem terminalGerms_lifted_complete_metric
    {n : ℕ} {Q : Type u} [TopologicalSpace Q] [T3Space Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q] [IsManifold (𝓡 n) ∞ Q]
    (g : RiemannianMetric n Q) (hg : MetricComplete g) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{v} Q) :=
      Poincare.Manifold.uliftChartedSpace _ Q
    letI : IsManifold (𝓡 n) ∞ (ULift.{v} Q) :=
      Poincare.Manifold.uliftIsManifold (𝓡 n) Q
    let d := Poincare.Manifold.uliftDiffeomorph (𝓡 n) Q
    let gL := g.pullbackOfLocalDiffeomorph d d.isLocalDiffeomorph
    MetricComplete gL ∧ ∀ (x y : ULift.{v} Q), gL.edist x y = g.edist x.down y.down := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{v} Q) :=
    Poincare.Manifold.uliftChartedSpace _ Q
  let : IsManifold (𝓡 n) ∞ (ULift.{v} Q) :=
    Poincare.Manifold.uliftIsManifold (𝓡 n) Q
  let d := Poincare.Manifold.uliftDiffeomorph (𝓡 n) Q
  let gL := g.pullbackOfLocalDiffeomorph d d.isLocalDiffeomorph
  refine ⟨(RiemannianMetric.metricComplete_iff_diffeomorph gL g d
    (fun _ _ _ => rfl)).mpr hg, ?_⟩
  intro x y
  exact RiemannianMetric.edist_diffeomorph gL g d (fun _ _ _ => rfl) x y

/-- The original terminal covering maps lift through the actual inverse
diffeomorphism and cover the same target in the larger universe. -/
theorem terminalGerms_lifted_chart_cover
    {n : ℕ} {ι : Type*} {P : ι → Type*} {Q : Type u}
    [∀ i, TopologicalSpace (P i)] [TopologicalSpace Q]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q] [IsManifold (𝓡 n) ∞ Q]
    (q : ∀ i, P i → Q)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q i))
    (hcover : ∀ y, ∃ i x, q i x = y) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{v} Q) :=
      Poincare.Manifold.uliftChartedSpace _ Q
    (∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (fun x => ULift.up.{v} (q i x))) ∧
      ∀ y : ULift.{v} Q, ∃ i x, ULift.up.{v} (q i x) = y := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{v} Q) :=
    Poincare.Manifold.uliftChartedSpace _ Q
  let d := Poincare.Manifold.uliftDiffeomorph (𝓡 n) Q
  refine ⟨?_, ?_⟩
  · intro i x
    exact (hq i x).comp (𝓡 n) (ULift.{v} Q) (d.symm.isLocalDiffeomorph (q i x))
  · intro y
    obtain ⟨i, x, hx⟩ := hcover y.down
    exact ⟨i, x, (congrArg ULift.up hx).trans (ULift.up_down y)⟩

end PoincareMT.M47
