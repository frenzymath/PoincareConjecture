import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TwoBranchWindows










set_option autoImplicit false

open Set Topology

namespace Geometry.OriginalPLTower

variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace E] {p : X → Y}



theorem right_branch_chart_support_subset
    (w : TwoBranchWindow p) (Q : OpenPartialHomeomorph Y E)
    {J : Set E} {V : Set Y} (hJ : J ⊆ Q.target)
    (hQw : Q.source ⊆ w.target) (hQV : Q.source ⊆ V) :
    (w.right.trans Q).symm '' J ⊆ p ⁻¹' V := by
  rintro x ⟨z, hz, rfl⟩
  have hzQ : Q.symm z ∈ Q.source := Q.map_target (hJ hz)
  have hzW : Q.symm z ∈ w.right.target := w.right_target.symm ▸ hQw hzQ
  change p (w.right.symm (Q.symm z)) ∈ V
  have heq : p (w.right.symm (Q.symm z)) = Q.symm z :=
    (congrFun w.right_eq _).symm.trans (w.right.right_inv hzW)
  rw [heq]
  exact hQV hzQ



theorem right_branch_motion_fixed_off_window
    (w : TwoBranchWindow p) (Q : OpenPartialHomeomorph Y E)
    {J : Set E} {V : Set Y} (hJ : J ⊆ Q.target)
    (hQw : Q.source ⊆ w.target) (hQV : Q.source ⊆ V)
    {g : X → X} (hfix : EqOn g id ((w.right.trans Q).symm '' J)ᶜ) :
    EqOn g id (p ⁻¹' V)ᶜ := by
  intro x hx
  exact hfix (fun hmem ↦ hx (right_branch_chart_support_subset w Q hJ hQw hQV hmem))

omit [TopologicalSpace Y] in


theorem motion_image_inter_eq_off_target_support
    (G : X ≃ₜ X) {V W : Set Y} (hVW : Disjoint V W)
    (hfix : EqOn G id (p ⁻¹' V)ᶜ) (A B : Set X) :
    G '' A ∩ (B ∩ p ⁻¹' W) = A ∩ (B ∩ p ⁻¹' W) := by
  have hfixed (x : X) (hx : x ∈ B ∩ p ⁻¹' W) : G x = x :=
    hfix (fun hv ↦ disjoint_left.mp hVW hv hx.2)
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hx⟩
    have heq : y = G y := G.injective (hfixed (G y) hx).symm
    exact ⟨heq ▸ hy, hx⟩
  · rintro ⟨hx, hxB⟩
    exact ⟨⟨x, hx, hfixed x hxB⟩, hxB⟩

omit [TopologicalSpace Y] in


theorem motion_projected_branch_image_eq_off_target_support
    (G : X ≃ₜ X) {V W : Set Y} (hVW : Disjoint V W)
    (hfix : EqOn G id (p ⁻¹' V)ᶜ) (A B : Set X) :
    p '' (G '' A ∩ B) ∩ W = p '' (A ∩ B) ∩ W := by
  have hsplit (C : Set X) : p '' C ∩ W = p '' (C ∩ p ⁻¹' W) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hw⟩
      exact ⟨x, ⟨hx, hw⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hw⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hw⟩
  rw [hsplit, hsplit, inter_assoc, inter_assoc,
    motion_image_inter_eq_off_target_support G hVW hfix A B]

end Geometry.OriginalPLTower
