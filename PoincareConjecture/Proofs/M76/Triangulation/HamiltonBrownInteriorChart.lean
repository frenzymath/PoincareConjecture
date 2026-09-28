import PoincareConjecture.Proofs.M76.Triangulation.HamiltonMarkedBrownCollar










set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "B" => (closedBall (0 : V3) 1)
local notation "S0" => (sphere (0 : V3) 1)

variable {X : Type*} [TopologicalSpace X] {D S : Set X}





theorem exists_marked_brown_interior_chart
    (phi : B ≃ₜ D) (hfront : frontier D = S)
    (hboundary : ∀ z : B, (z : V3) ∈ S0 ↔ (phi z : X) ∈ S) :
    ∃ C : OpenPartialHomeomorph X V3,
      C.source = interior D ∧ C.target = ball (0 : V3) 1 ∧
      (∀ x : D, C (x : X) = (phi.symm x : V3)) ∧
      ∀ z : B, C.symm (z : V3) = (phi z : X) := by
  classical
  have hiff (x : D) : (x : X) ∈ interior D ↔
      (phi.symm x : V3) ∈ ball (0 : V3) 1 := by
    rw [← self_sdiff_frontier D, hfront, mem_ball_zero_iff]
    change ((x : X) ∈ D ∧ (x : X) ∉ S) ↔ ‖(phi.symm x : V3)‖ < 1
    simp only [x.property, true_and]
    have hb := hboundary (phi.symm x)
    rw [phi.apply_symm_apply] at hb
    rw [← hb, mem_sphere_zero_iff_norm]
    have hle := mem_closedBall_zero_iff.mp (phi.symm x).property
    exact ⟨fun h => lt_of_le_of_ne hle h, fun h => ne_of_lt h⟩
  let f : X → V3 := fun x => if hx : x ∈ D then (phi.symm ⟨x, hx⟩ : V3) else 0
  let g : V3 → X := fun z => if hz : z ∈ B then (phi ⟨z, hz⟩ : X)
    else (phi ⟨0, mem_closedBall_self zero_le_one⟩ : X)
  have hfval (x : D) : f x = (phi.symm x : V3) := by
    simp only [f, dif_pos x.property]
  have hgval (z : B) : g z = (phi z : X) := by
    simp only [g, dif_pos z.property]
  have hfmap : MapsTo f (interior D) (ball (0 : V3) 1) := by
    intro x hx
    rw [hfval ⟨x, interior_subset hx⟩]
    exact (hiff ⟨x, interior_subset hx⟩).mp hx
  have hgmap : MapsTo g (ball (0 : V3) 1) (interior D) := by
    intro z hz
    let zB : B := ⟨z, ball_subset_closedBall hz⟩
    rw [hgval zB]
    apply (hiff (phi zB)).mpr
    rw [phi.symm_apply_apply]
    exact hz
  have hleft : LeftInvOn g f (interior D) := by
    intro x hx
    let xD : D := ⟨x, interior_subset hx⟩
    rw [hfval xD, hgval (phi.symm xD), phi.apply_symm_apply]
  have hright : LeftInvOn f g (ball (0 : V3) 1) := by
    intro z hz
    let zB : B := ⟨z, ball_subset_closedBall hz⟩
    rw [hgval zB, hfval (phi zB), phi.symm_apply_apply]
  have hf : ContinuousOn f (interior D) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let q : interior D → D := fun x => ⟨x, interior_subset x.property⟩
    have hq : Continuous q := continuous_subtype_val.subtype_mk _
    exact (continuous_subtype_val.comp (phi.symm.continuous.comp hq)).congr
      (fun x => (hfval (q x)).symm)
  have hg : ContinuousOn g (ball (0 : V3) 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let q : ball (0 : V3) 1 → B := fun z => ⟨z, ball_subset_closedBall z.property⟩
    have hq : Continuous q := continuous_subtype_val.subtype_mk _
    exact (continuous_subtype_val.comp (phi.continuous.comp hq)).congr
      (fun z => (hgval (q z)).symm)
  let C : OpenPartialHomeomorph X V3 := {
    toFun := f
    invFun := g
    source := interior D
    target := ball (0 : V3) 1
    map_source' := hfmap
    map_target' := hgmap
    left_inv' := hleft
    right_inv' := hright
    open_source := isOpen_interior
    open_target := isOpen_ball
    continuousOn_toFun := hf
    continuousOn_invFun := hg }
  exact ⟨C, rfl, rfl, hfval, hgval⟩

end PoincareConjecture.M76
