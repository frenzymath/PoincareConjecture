import PoincareLib.Geometry.Alexandrov.ComparisonAngle
import PoincareLib.Geometry.Alexandrov.FiniteApproximation

/-!
# The curvature minus one four-point condition

The condition is expressed entirely in distances. Its stability under
convergence of finite configurations uses positivity of the limiting adjacent
sides; it does not require nondegenerate comparison triangles.

Reference: Burago--Gromov--Perelman (1992), Definition 2.3, p. 5.
-/

noncomputable section
set_option autoImplicit false

open Filter Topology

namespace Poincare.Alexandrov

/-- The curvature minus one Alexandrov four-point comparison condition. -/
def CurvatureGEnegOne (X : Type*) [MetricSpace X] : Prop :=
  ∀ q : Fin 4 → X, Function.Injective q →
    comparisonAngle (dist (q 0) (q 1)) (dist (q 0) (q 2)) (dist (q 1) (q 2)) +
      comparisonAngle (dist (q 0) (q 1)) (dist (q 0) (q 3)) (dist (q 1) (q 3)) +
      comparisonAngle (dist (q 0) (q 2)) (dist (q 0) (q 3)) (dist (q 2) (q 3)) ≤
      2 * Real.pi

/-- Four-point comparison restricts along isometric embeddings. -/
theorem CurvatureGEnegOne.of_isometry {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (hY : CurvatureGEnegOne Y) {f : X → Y} (hf : Isometry f) :
    CurvatureGEnegOne X := by
  intro q hq
  simpa only [Function.comp_apply, hf.dist_eq] using hY (f ∘ q) (hf.injective.comp hq)

/-- A distance limit of quadruples satisfying the four-point inequality
satisfies that inequality, provided the limiting points are distinct. -/
theorem fourPoint_comparison_of_tendsto_dist
    {X : ℕ → Type*} [∀ j, MetricSpace (X j)]
    {Y : Type*} [MetricSpace Y] {q : Fin 4 → Y} {f : ∀ j, Fin 4 → X j}
    (hX : ∀ j, CurvatureGEnegOne (X j)) (hq : Function.Injective q)
    (hf : ∀ a b, Tendsto (fun j => dist (f j a) (f j b)) atTop (𝓝 (dist (q a) (q b)))) :
    comparisonAngle (dist (q 0) (q 1)) (dist (q 0) (q 2)) (dist (q 1) (q 2)) +
      comparisonAngle (dist (q 0) (q 1)) (dist (q 0) (q 3)) (dist (q 1) (q 3)) +
      comparisonAngle (dist (q 0) (q 2)) (dist (q 0) (q 3)) (dist (q 2) (q 3)) ≤
      2 * Real.pi := by
  have h01 : 0 < dist (q 0) (q 1) := dist_pos.mpr (hq.ne (by decide))
  have h02 : 0 < dist (q 0) (q 2) := dist_pos.mpr (hq.ne (by decide))
  have h03 : 0 < dist (q 0) (q 3) := dist_pos.mpr (hq.ne (by decide))
  apply le_of_tendsto (((tendsto_comparisonAngle (hf 0 1) (hf 0 2) (hf 1 2) h01 h02).add
    (tendsto_comparisonAngle (hf 0 1) (hf 0 3) (hf 1 3) h01 h03)).add
    (tendsto_comparisonAngle (hf 0 2) (hf 0 3) (hf 2 3) h02 h03))
  filter_upwards [eventually_injective_of_tendsto_dist hq hf] with j hj
  exact hX j (f j) hj

end Poincare.Alexandrov
