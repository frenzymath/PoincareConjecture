import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.FiniteBranchMotions

set_option autoImplicit false

open Set Topology

namespace Geometry

variable {X Y E α T : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace E]

theorem homeomorph_eq_of_image_mem_support
    (H G : X ≃ₜ X) {U : Set X} (heq : EqOn H G U)
    (hfix : EqOn G id Uᶜ) {x : X} (hx : H x ∈ U) : H x = G x := by
  have hi : EqOn G.symm id Uᶜ := by
    intro y hy
    apply G.injective
    rw [G.apply_symm_apply]
    exact (hfix hy).symm
  have hy := supported_homeomorph_mapsTo G.symm hi hx
  have he : H (G.symm (H x)) = H x := (heq hy).trans (G.apply_symm_apply _)
  exact heq (H.injective he ▸ hy)

theorem homeomorph_eq_self_of_image_not_mem
    (H : X ≃ₜ X) {U : Set X} (hfix : EqOn H id Uᶜ)
    {x : X} (hx : H x ∉ U) : H x = x :=
  H.injective (hfix hx)

theorem right_branch_motion_closed_support [T2Space Y]
    {p : X → Y} (w : TwoBranchWindow p) (Q : OpenPartialHomeomorph Y E)
    {J : Set E} (hJ : IsCompact J) (hJQ : J ⊆ Q.target)
    (hQw : Q.source ⊆ w.target) {g : X → X}
    (hfix : EqOn g id ((w.right.trans Q).symm '' J)ᶜ) :
    IsClosed (Q.symm '' J) ∧ EqOn g id (p ⁻¹' (Q.symm '' J))ᶜ := by
  refine ⟨(hJ.image_of_continuousOn (Q.continuousOn_symm.mono hJQ)).isClosed, ?_⟩
  intro x hx
  apply hfix
  rintro ⟨z, hz, rfl⟩
  apply hx
  have hzW : Q.symm z ∈ w.right.target :=
    w.right_target.symm ▸ hQw (Q.map_target (hJQ hz))
  change p (w.right.symm (Q.symm z)) ∈ Q.symm '' J
  rw [← congrFun w.right_eq _, w.right.right_inv hzW]
  exact mem_image_of_mem Q.symm hz

theorem composeSupportedMotions_whole_branch_chart
    (p : X → Y) (F : α → T → X ≃ₜ X) (V : α → Set Y)
    (hfix : ∀ a t, EqOn (F a t) id (p ⁻¹' V a)ᶜ)
    (hdis : Pairwise (fun a b ↦ Disjoint (V a) (V b)))
    (l : List α) (hl : l.Nodup) (t : T) {a : α} (ha : a ∈ l)
    (A : Set X) (w : TwoBranchWindow p) (Q : OpenPartialHomeomorph Y E)
    (hQV : Q.source ⊆ V a) (L R : E → Prop)
    (hleft : ∀ y ∈ Q.source, y ∈ p '' (F a t '' A ∩ w.left.source) ↔ L (Q y))
    (hright : ∀ y ∈ Q.source, y ∈ p '' (F a t '' A ∩ w.right.source) ↔ R (Q y)) :
    (∀ y ∈ Q.source,
      y ∈ p '' (composeSupportedMotions F l t '' A ∩ w.left.source) ↔ L (Q y)) ∧
    ∀ y ∈ Q.source,
      y ∈ p '' (composeSupportedMotions F l t '' A ∩ w.right.source) ↔ R (Q y) := by
  exact ⟨fun y hy ↦ (composeSupportedMotions_branch_iff p F V hfix hdis
    l hl t ha A w.left.source (hQV hy)).trans (hleft y hy),
    fun y hy ↦ (composeSupportedMotions_branch_iff p F V hfix hdis
    l hl t ha A w.right.source (hQV hy)).trans (hright y hy)⟩

theorem composeSupportedMotions_open_unchanged_neighborhood
    (p : X → Y) (F : α → T → X ≃ₜ X) (C : α → Set Y)
    (hC : ∀ a, IsClosed (C a))
    (hfix : ∀ a t, EqOn (F a t) id (p ⁻¹' C a)ᶜ)
    (l : List α) (t : T) {y : Y} (hy : y ∉ ⋃ a ∈ l, C a) :
    ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧ W ⊆ (⋃ a ∈ l, C a)ᶜ ∧
      (∀ x, p (composeSupportedMotions F l t x) ∈ W →
        composeSupportedMotions F l t x = x) ∧
      ∀ A B : Set X,
        p '' (composeSupportedMotions F l t '' A ∩ B) ∩ W = p '' (A ∩ B) ∩ W := by
  have hclosed : IsClosed (⋃ a ∈ l, C a) :=
    l.finite_toSet.isClosed_biUnion (fun a _ ↦ hC a)
  have hfull : EqOn (composeSupportedMotions F l t) id
      (p ⁻¹' (⋃ a ∈ l, C a))ᶜ := by
    simpa only [preimage_iUnion] using
      composeSupportedMotions_eqOn_compl F (fun a ↦ p ⁻¹' C a) hfix l t
  refine ⟨(⋃ a ∈ l, C a)ᶜ, hclosed.isOpen_compl, hy, Subset.rfl, ?_, ?_⟩
  · intro x hx
    exact homeomorph_eq_self_of_image_not_mem _ hfull hx
  · intro A B
    exact OriginalPLTower.motion_projected_branch_image_eq_off_target_support
      _ disjoint_compl_right hfull A B

end Geometry
