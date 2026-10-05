import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.ReflectedDeckField
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Cylinder.Geometry.CylinderCharts

/-!
# One bounded chart containing two actual reflected points

An equatorial antipodal pair avoids both omitted poles of one sphere chart.
Their zero axial coordinates lie in one bounded connected Euclidean ball.
This keeps the same subsequence and chart for the reflected-field argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- A single bounded cylinder chart contains a literal reflected pair. -/
theorem exists_reflected_pair_in_chart_ball :
    ∃ (q : UnitTwoSphere) (x y : V) (R : ℝ), 0 < R ∧
      x ∈ Metric.ball 0 R ∧ y ∈ Metric.ball 0 R ∧
      cylinderChart q y = m27TwistedProductInvolution (cylinderChart q x) := by
  let : Fact (Module.finrank ℝ V = 2 + 1) := ⟨by simp⟩
  let q : UnitTwoSphere := ⟨EuclideanSpace.single (2 : Fin 3) 1, by simp⟩
  let p : UnitTwoSphere := ⟨EuclideanSpace.single (0 : Fin 3) 1, by simp⟩
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have hp : p ∈ (chartAt E2 q).source := by
    change p ∈ (stereographic' 2 (-q)).source
    rw [stereographic'_source]
    change p ≠ -q
    intro he
    have h := congrArg (fun z : UnitTwoSphere => z.val 0) he
    norm_num [p, q, h02] at h
  have hnp : -p ∈ (chartAt E2 q).source := by
    change -p ∈ (stereographic' 2 (-q)).source
    rw [stereographic'_source]
    change -p ≠ -q
    intro he
    have h := congrArg (fun z : UnitTwoSphere => z.val 0) he
    norm_num [p, q, h02] at h
  let x := cylinderCoordinateEquiv.symm ((chartAt E2 q) p, 0)
  let y := cylinderCoordinateEquiv.symm ((chartAt E2 q) (-p), 0)
  have hx : cylinderChart q x = (p, 0) := by
    simp only [x, cylinderChart, ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext ((chartAt E2 q).left_inv hp) rfl
  have hy : cylinderChart q y = (-p, 0) := by
    simp only [y, cylinderChart, ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext ((chartAt E2 q).left_inv hnp) rfl
  refine ⟨q, x, y, max ‖x‖ ‖y‖ + 1, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt ((norm_nonneg x).trans (le_max_left _ _))
      (lt_add_of_pos_right _ zero_lt_one)
  · rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (le_max_left _ _) (lt_add_of_pos_right _ zero_lt_one)
  · rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (le_max_right _ _) (lt_add_of_pos_right _ zero_lt_one)
  · rw [hx, hy]
    simp only [m27TwistedProductInvolution, neg_zero]

end PoincareMT.M35
