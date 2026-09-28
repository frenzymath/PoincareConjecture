import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactChart
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false

open scoped ContDiff
open Set Metric

namespace PoincareConjecture.M25.Topology3D
namespace PlanarSchoenfliesData

variable {c : UnitCircle → E2} (D : PlanarSchoenfliesData c)

noncomputable def discChart : OpenPartialHomeomorph E2 E2 where
  toFun := D.chart
  invFun := Classical.choose D.chart_inverse
  source := ball 0 D.radius
  target := D.chart '' ball 0 D.radius
  map_source' := fun x hx => mem_image_of_mem D.chart hx
  map_target' := by
    rintro y ⟨x, hx, rfl⟩
    simpa only [(Classical.choose_spec D.chart_inverse).2 x hx] using hx
  left_inv' := (Classical.choose_spec D.chart_inverse).2
  right_inv' := by
    rintro y ⟨x, hx, rfl⟩
    rw [(Classical.choose_spec D.chart_inverse).2 x hx]
  open_source := isOpen_ball
  open_target := D.chart_open_map
  continuousOn_toFun := D.chart_smooth.continuousOn
  continuousOn_invFun := (Classical.choose_spec D.chart_inverse).1.continuousOn

@[simp] theorem discChart_apply (x : E2) : D.discChart x = D.chart x := rfl

@[simp] theorem discChart_source : D.discChart.source = ball 0 D.radius := rfl

@[simp] theorem discChart_target :
    D.discChart.target = D.chart '' ball 0 D.radius := rfl

theorem discChart_contDiffOn : ContDiffOn ℝ ∞ D.discChart D.discChart.source :=
  D.chart_smooth

theorem discChart_symm_contDiffOn :
    ContDiffOn ℝ ∞ D.discChart.symm D.discChart.target :=
  (Classical.choose_spec D.chart_inverse).1

theorem closedBall_subset_discChart_source : closedBall 0 1 ⊆ D.discChart.source :=
  closedBall_subset_ball D.one_lt_radius

theorem discChart_image_sphere : D.discChart '' sphere 0 1 = range c := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, (D.chart_boundary ⟨x, hx⟩).symm⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, q.2, D.chart_boundary q⟩

theorem discChart_image_closedBall :
    D.discChart '' closedBall 0 1 = D.inside ∪ range c := by
  rw [← ball_union_sphere, image_union, D.discChart_image_sphere]
  change D.chart '' ball 0 1 ∪ range c = D.inside ∪ range c
  rw [D.chart_image_inside]

theorem closure_inside_eq_discChart_image :
    closure D.inside = D.discChart '' closedBall 0 1 := by
  rw [← D.chart_image_inside]
  exact compactChart_closure_ball D.discChart 0 zero_lt_one
    D.closedBall_subset_discChart_source

theorem frontier_inside_eq_range : frontier D.inside = range c := by
  rw [← D.chart_image_inside, ← D.discChart_image_sphere]
  exact compactChart_frontier_ball D.discChart 0 zero_lt_one
    D.closedBall_subset_discChart_source

noncomputable def cylinderChart : OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ) :=
  D.discChart.prod (OpenPartialHomeomorph.refl ℝ)

@[simp] theorem cylinderChart_apply (p : E2 × ℝ) :
    D.cylinderChart p = (D.chart p.1, p.2) := rfl

@[simp] theorem cylinderChart_source :
    D.cylinderChart.source = ball 0 D.radius ×ˢ (univ : Set ℝ) := rfl

@[simp] theorem cylinderChart_target :
    D.cylinderChart.target = (D.chart '' ball 0 D.radius) ×ˢ (univ : Set ℝ) := rfl

theorem cylinderChart_contDiffOn :
    ContDiffOn ℝ ∞ D.cylinderChart D.cylinderChart.source :=
  D.discChart_contDiffOn.prodMap contDiff_id.contDiffOn

theorem cylinderChart_symm_contDiffOn :
    ContDiffOn ℝ ∞ D.cylinderChart.symm D.cylinderChart.target :=
  D.discChart_symm_contDiffOn.prodMap contDiff_id.contDiffOn

theorem cylinderChart_boundary (q : UnitCircle) (z : ℝ) :
    D.cylinderChart (q.1, z) = (c q, z) := by
  simp only [cylinderChart_apply, D.chart_boundary]

theorem cylinderChart_image_inside (s : Set ℝ) :
    D.cylinderChart '' (ball 0 1 ×ˢ s) = D.inside ×ˢ s := by
  change Prod.map D.chart id '' (ball 0 1 ×ˢ s) = D.inside ×ˢ s
  rw [prodMap_image_prod, D.chart_image_inside, image_id]

end PlanarSchoenfliesData
end PoincareConjecture.M25.Topology3D
