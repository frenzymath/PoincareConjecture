import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Isotopy.Mathlib.RelativeCircleLift
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false
open Set

namespace AddCircle

variable {Y : Type*} [TopologicalSpace Y]
  [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y]

theorem exists_lift_eq_prescribed_on_connected_set (period : ℝ) [Fact (0 < period)]
    (f : C(Y, AddCircle period)) {A : Set Y} (hA : IsConnected A)
    (boundary : C(A, ℝ)) (hboundary : ∀ y : A, (boundary y : AddCircle period) = f y) :
    ∃ lift : C(Y, ℝ), (∀ y, (lift y : AddCircle period) = f y) ∧
      ∀ y : A, lift y = boundary y := by
  obtain ⟨y0, hy0⟩ := hA.nonempty
  let base : A := ⟨y0, hy0⟩
  let cov := isCoveringMap_coe period
  obtain ⟨lift, ⟨hlift0, hlift⟩, _⟩ :=
    cov.existsUnique_continuousMap_lifts f y0 (boundary base) (hboundary base)
  let : ConnectedSpace A := isConnected_iff_connectedSpace.mp hA
  have heq : (fun y : A => lift y) = boundary :=
    cov.eq_of_comp_eq (lift.continuous.comp continuous_subtype_val) boundary.continuous
      (by funext y; exact (congrFun hlift y).trans (hboundary y).symm)
      base hlift0
  exact ⟨lift, fun y => congrFun hlift y, fun y => congrFun heq y⟩

theorem exists_homotopyRel_clamped_lift_of_connected_set
    (period : ℝ) [Fact (0 < period)]
    (f : C(Y, AddCircle period)) {A : Set Y} (hA : IsConnected A)
    (boundary : C(A, ℝ)) (hboundary : ∀ y : A, (boundary y : AddCircle period) = f y)
    (lower upper : ℝ) (horder : lower ≤ upper)
    (hboundaryRange : ∀ y : A, boundary y ∈ Icc lower upper) :
    ∃ (lift : C(Y, ℝ)) (endpoint : C(Y, AddCircle period))
      (H : f.HomotopyRel endpoint A),
      (∀ y, (lift y : AddCircle period) = f y) ∧
      (∀ y : A, lift y = boundary y) ∧
      (∀ y, endpoint y = ((projIcc lower upper horder (lift y) : ℝ) : AddCircle period)) ∧
      range endpoint ⊆ ((↑) : ℝ → AddCircle period) '' Icc lower upper ∧
      ∀ (t : unitInterval) (y : Y), H (t, y) =
        (((1 - (t : ℝ)) * lift y + (t : ℝ) *
          (projIcc lower upper horder (lift y) : ℝ) : ℝ) : AddCircle period) := by
  obtain ⟨lift, hlift, hliftA⟩ :=
    exists_lift_eq_prescribed_on_connected_set period f hA boundary hboundary
  let clipped : C(Y, ℝ) :=
    ⟨fun y => projIcc lower upper horder (lift y), by fun_prop⟩
  let endpoint : C(Y, AddCircle period) := ⟨fun y => (clipped y : AddCircle period), by fun_prop⟩
  have hclipA (y : A) : clipped y = lift y := by
    change (projIcc lower upper horder (lift y) : ℝ) = lift y
    rw [hliftA y]
    exact congrArg Subtype.val (projIcc_of_mem horder (hboundaryRange y))
  let H : f.HomotopyRel endpoint A := {
    toFun := fun z =>
      (((1 - (z.1 : ℝ)) * lift z.2 + (z.1 : ℝ) * clipped z.2 : ℝ) : AddCircle period)
    continuous_toFun := by fun_prop
    map_zero_left := by intro y; simpa using hlift y
    map_one_left := by intro y; simp [endpoint]
    prop' := by
      intro t y hy
      change (((1 - (t : ℝ)) * lift y + (t : ℝ) * clipped y : ℝ) : AddCircle period) = f y
      rw [hclipA ⟨y, hy⟩]
      convert hlift y using 1
      congr 1
      ring }
  refine ⟨lift, endpoint, H, hlift, hliftA, fun _ => rfl, ?_, fun _ _ => rfl⟩
  rintro _ ⟨y, rfl⟩
  exact ⟨projIcc lower upper horder (lift y),
    (projIcc lower upper horder (lift y)).property, rfl⟩

end AddCircle
