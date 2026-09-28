import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.AddCircle.Real

set_option autoImplicit false

open Set

namespace AddCircle

variable {Y : Type*} [TopologicalSpace Y]
  [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y]

theorem exists_lift_eq_on_connected_set (p : ℝ) [Fact (0 < p)]
    (f : C(Y, AddCircle p)) {A : Set Y} (hA : IsConnected A)
    (theta : ℝ) (hf : ∀ y ∈ A, f y = (theta : AddCircle p)) :
    ∃ l : C(Y, ℝ), (∀ y, (l y : AddCircle p) = f y) ∧
      ∀ y ∈ A, l y = theta := by
  obtain ⟨y0, hy0⟩ := hA.nonempty
  let cov := isCoveringMap_coe p
  obtain ⟨l, ⟨hl0, hl⟩, _⟩ := cov.existsUnique_continuousMap_lifts f y0 theta
    (hf y0 hy0).symm
  refine ⟨l, fun y => congrFun hl y, ?_⟩
  intro y hy
  have hconst := cov.constOn_of_comp hA.isPreconnected l.continuous.continuousOn
    (fun x hx z hz => (congrFun hl x).trans ((hf x hx).trans
      ((hf z hz).symm.trans (congrFun hl z).symm))) hy hy0
  exact hconst.trans hl0

theorem exists_homotopyRel_const_of_connected_set (p : ℝ) [Fact (0 < p)]
    (f : C(Y, AddCircle p)) {A : Set Y} (hA : IsConnected A)
    (theta : ℝ) (hf : ∀ y ∈ A, f y = (theta : AddCircle p)) :
    ∃ (l : C(Y, ℝ)) (H : f.HomotopyRel (ContinuousMap.const Y (theta : AddCircle p)) A),
      (∀ y, (l y : AddCircle p) = f y) ∧ (∀ y ∈ A, l y = theta) ∧
      ∀ (t : unitInterval) (y : Y),
        H (t, y) = (((1 - (t : ℝ)) * l y + (t : ℝ) * theta : ℝ) : AddCircle p) := by
  obtain ⟨l, hl, hlA⟩ := exists_lift_eq_on_connected_set p f hA theta hf
  refine ⟨l, {
    toFun := fun z => (((1 - (z.1 : ℝ)) * l z.2 + (z.1 : ℝ) * theta : ℝ) : AddCircle p)
    continuous_toFun := by fun_prop
    map_zero_left := by intro y; simpa using hl y
    map_one_left := by intro y; simp
    prop' := by
      intro t y hy
      change (((1 - (t : ℝ)) * l y + (t : ℝ) * theta : ℝ) : AddCircle p) = f y
      rw [hlA y hy, hf y hy]
      congr 1
      ring }, hl, hlA, fun _ _ => rfl⟩

end AddCircle
