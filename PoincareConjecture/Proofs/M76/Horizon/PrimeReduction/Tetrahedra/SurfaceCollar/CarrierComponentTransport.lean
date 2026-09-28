import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false
open Set

namespace Homeomorph

theorem exists_inter_restriction
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A T : Set X} {B U : Set Y} (H : A ≃ₜ B)
    (hmark : ∀ x : A, (H x : Y) ∈ U ↔ (x : X) ∈ T) :
    ∃ G : (A ∩ T : Set X) ≃ₜ (B ∩ U : Set Y),
      ∀ x : (A ∩ T : Set X), (G x : Y) = H ⟨x,x.property.1⟩ := by
  let f : (A ∩ T : Set X) → (B ∩ U : Set Y) := fun x =>
    ⟨H ⟨x,x.property.1⟩,⟨(H ⟨x,x.property.1⟩).property,
      (hmark ⟨x,x.property.1⟩).mpr x.property.2⟩⟩
  have hinv (y : (B ∩ U : Set Y)) : (H.symm ⟨y,y.property.1⟩ : X) ∈ T := by
    apply (hmark (H.symm ⟨y,y.property.1⟩)).mp
    simpa only [H.apply_symm_apply] using y.property.2
  let q : (B ∩ U : Set Y) → (A ∩ T : Set X) := fun y =>
    ⟨H.symm ⟨y,y.property.1⟩,⟨(H.symm ⟨y,y.property.1⟩).property,hinv y⟩⟩
  let G : (A ∩ T : Set X) ≃ₜ (B ∩ U : Set Y) := {
    toFun := f
    invFun := q
    left_inv := by
      intro x
      apply Subtype.ext
      change (H.symm (H ⟨x,x.property.1⟩) : X) = x
      exact congrArg Subtype.val (H.symm_apply_apply _)
    right_inv := by
      intro y
      apply Subtype.ext
      change (H (H.symm ⟨y,y.property.1⟩) : Y) = y
      exact congrArg Subtype.val (H.apply_symm_apply _)
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (H.continuous.comp
        (continuous_subtype_val.subtype_mk (fun x => x.property.1)))
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (H.symm.continuous.comp
        (continuous_subtype_val.subtype_mk (fun y => y.property.1))) }
  exact ⟨G,fun _ => rfl⟩

theorem image_connectedComponentIn_of_values
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (H : A ≃ₜ B) {f : X → Y}
    (hval : ∀ x : A, f x = (H x : Y))
    {U : Set X} (hUA : U ⊆ A) {x : X} (hx : x ∈ U) :
    f '' connectedComponentIn U x = connectedComponentIn (f '' U) (f x) := by
  classical
  have hf : ContinuousOn f A := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp H.continuous).congr (fun z => (hval z).symm)
  let q : Y → X := fun y => if hy : y ∈ B then (H.symm ⟨y,hy⟩ : X) else x
  have hqval (y : B) : q y = (H.symm y : X) := by simp only [q,dif_pos y.property]
  have hq : ContinuousOn q B := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp H.symm.continuous).congr
      (fun y => (hqval y).symm)
  have hfB (z : X) (hz : z ∈ A) : f z ∈ B := by
    rw [hval ⟨z,hz⟩]
    exact (H ⟨z,hz⟩).property
  have hleft (z : X) (hz : z ∈ A) : q (f z) = z := by
    rw [hval ⟨z,hz⟩,hqval,H.symm_apply_apply]
  have hright (y : Y) (hy : y ∈ B) : f (q y) = y := by
    rw [hqval ⟨y,hy⟩,hval,H.apply_symm_apply]
  have hUim : q '' (f '' U) = U := by
    rw [←image_comp]
    exact image_congr (fun z hz => hleft z (hUA hz)) |>.trans (image_id U)
  apply Subset.antisymm ((hf.mono hUA).image_connectedComponentIn_subset hx)
  intro y hy
  have hsubB : f '' U ⊆ B := by
    rintro _ ⟨z,hz,rfl⟩
    exact hfB z (hUA hz)
  have hqcc := (hq.mono hsubB).image_connectedComponentIn_subset (mem_image_of_mem f hx)
  rw [hUim,hleft x (hUA hx)] at hqcc
  exact ⟨q y,hqcc (mem_image_of_mem q hy),
    hright y (hsubB (connectedComponentIn_subset _ _ hy))⟩

end Homeomorph
