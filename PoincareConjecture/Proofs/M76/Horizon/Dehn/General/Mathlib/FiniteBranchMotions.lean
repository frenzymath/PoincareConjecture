import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.DisjointSupportedMotions
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.BranchMotionSupport











set_option autoImplicit false

open Set

namespace Geometry

variable {X T α Y : Type*} [TopologicalSpace X] [TopologicalSpace T]

omit [TopologicalSpace T] in


theorem homeomorph_image_inter_eq_of_eqOn_support
    (H G : X ≃ₜ X) {U : Set X} (heq : EqOn H G U)
    (hfix : EqOn G id Uᶜ) (A B : Set X) :
    H '' A ∩ (B ∩ U) = G '' A ∩ (B ∩ U) := by
  have hsymm : EqOn G.symm id Uᶜ := by
    intro x hx
    apply G.injective
    rw [G.apply_symm_apply]
    exact (hfix hx).symm
  have hGinv := supported_homeomorph_mapsTo G.symm hsymm
  have hHpre (x : X) (hx : H x ∈ U) : x ∈ U := by
    have hy : G.symm (H x) ∈ U := hGinv hx
    have he : H (G.symm (H x)) = H x := (heq hy).trans (G.apply_symm_apply _)
    exact H.injective he ▸ hy
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hx⟩
    exact ⟨⟨y, hy, (heq (hHpre y hx.2)).symm⟩, hx⟩
  · rintro ⟨⟨y, hy, rfl⟩, hx⟩
    have hyU : y ∈ U := by simpa only [G.symm_apply_apply] using hGinv hx.2
    exact ⟨⟨y, hy, heq hyU⟩, hx⟩

omit [TopologicalSpace T] in


theorem composeSupportedMotions_branch_image
    (p : X → Y) (F : α → T → X ≃ₜ X) (V : α → Set Y)
    (hfix : ∀ a t, EqOn (F a t) id (p ⁻¹' V a)ᶜ)
    (hdis : Pairwise (fun a b ↦ Disjoint (V a) (V b)))
    (l : List α) (hl : l.Nodup) (t : T) {a : α} (ha : a ∈ l) (A B : Set X) :
    p '' (composeSupportedMotions F l t '' A ∩ B) ∩ V a =
      p '' (F a t '' A ∩ B) ∩ V a := by
  have hpre : Pairwise (fun a b ↦ Disjoint (p ⁻¹' V a) (p ⁻¹' V b)) :=
    fun a b hne ↦ (hdis hne).preimage p
  have heq := composeSupportedMotions_eqOn_support F (fun a ↦ p ⁻¹' V a)
    hfix hpre l hl t a ha
  rw [← image_inter_preimage p (composeSupportedMotions F l t '' A ∩ B) (V a),
    ← image_inter_preimage p (F a t '' A ∩ B) (V a), inter_assoc, inter_assoc,
    homeomorph_image_inter_eq_of_eqOn_support _ _ heq (hfix a t) A B]

omit [TopologicalSpace T] in


theorem composeSupportedMotions_branch_iff
    (p : X → Y) (F : α → T → X ≃ₜ X) (V : α → Set Y)
    (hfix : ∀ a t, EqOn (F a t) id (p ⁻¹' V a)ᶜ)
    (hdis : Pairwise (fun a b ↦ Disjoint (V a) (V b)))
    (l : List α) (hl : l.Nodup) (t : T) {a : α} (ha : a ∈ l)
    (A B : Set X) {y : Y} (hy : y ∈ V a) :
    y ∈ p '' (composeSupportedMotions F l t '' A ∩ B) ↔
      y ∈ p '' (F a t '' A ∩ B) := by
  have h := congrArg (fun S : Set Y ↦ y ∈ S)
    (composeSupportedMotions_branch_image p F V hfix hdis l hl t ha A B)
  exact Eq.to_iff (by simpa only [mem_inter_iff, hy, and_true] using h)

omit [TopologicalSpace T] in


theorem composeSupportedMotions_branch_image_off_supports
    (p : X → Y) (F : α → T → X ≃ₜ X) (V : α → Set Y)
    (hfix : ∀ a t, EqOn (F a t) id (p ⁻¹' V a)ᶜ)
    (l : List α) (t : T) (A B : Set X) :
    p '' (composeSupportedMotions F l t '' A ∩ B) \ (⋃ a ∈ l, V a) =
      p '' (A ∩ B) \ (⋃ a ∈ l, V a) := by
  have hfull : EqOn (composeSupportedMotions F l t) id (p ⁻¹' (⋃ a ∈ l, V a))ᶜ := by
    simpa only [preimage_iUnion] using
      composeSupportedMotions_eqOn_compl F (fun a ↦ p ⁻¹' V a) hfix l t
  simpa only [sdiff_eq] using
    OriginalPLTower.motion_projected_branch_image_eq_off_target_support
      (composeSupportedMotions F l t) disjoint_compl_right hfull A B



theorem exists_finite_scheduled_branch_motion
    [TopologicalSpace Y] {E : Type*} [TopologicalSpace E]
    (p : X → Y) (F : α → T → X ≃ₜ X) (t₀ : T)
    (hF : ∀ a, Continuous (fun z : T × X ↦ F a z.1 z.2))
    (hFinv : ∀ a, Continuous (fun z : T × X ↦ (F a z.1).symm z.2))
    (hzero : ∀ a x, F a t₀ x = x)
    (w : α → Topology.TwoBranchWindow p) (Q : α → OpenPartialHomeomorph Y E)
    (J : α → Set E) (V : α → Set Y)
    (hJ : ∀ a, J a ⊆ (Q a).target)
    (hQw : ∀ a, (Q a).source ⊆ (w a).target)
    (hQV : ∀ a, (Q a).source ⊆ V a)
    (hfix : ∀ a t, EqOn (F a t) id (((w a).right.trans (Q a)).symm '' J a)ᶜ)
    (hdis : Pairwise (fun a b ↦ Disjoint (V a) (V b)))
    (l : List α) (hl : l.Nodup) :
    ∃ H : T → X ≃ₜ X,
      H = composeSupportedMotions F l ∧
      Continuous (fun z : T × X ↦ H z.1 z.2) ∧
      Continuous (fun z : T × X ↦ (H z.1).symm z.2) ∧
      (∀ x, H t₀ x = x) ∧
      (∀ t, EqOn (H t) id (⋃ a ∈ l, p ⁻¹' V a)ᶜ) ∧
      (∀ t a, a ∈ l → EqOn (H t) (F a t) (p ⁻¹' V a)) ∧
      ∀ t a, a ∈ l → ∀ A B : Set X,
        p '' (H t '' A ∩ B) ∩ V a = p '' (F a t '' A ∩ B) ∩ V a := by
  have hfull (a : α) (t : T) : EqOn (F a t) id (p ⁻¹' V a)ᶜ :=
    OriginalPLTower.right_branch_motion_fixed_off_window
      (w a) (Q a) (hJ a) (hQw a) (hQV a) (hfix a t)
  have hpre : Pairwise (fun a b ↦ Disjoint (p ⁻¹' V a) (p ⁻¹' V b)) :=
    fun a b hne ↦ (hdis hne).preimage p
  exact ⟨composeSupportedMotions F l, rfl,
    composeSupportedMotions_continuous F hF l,
    composeSupportedMotions_inverse_continuous F hFinv l,
    composeSupportedMotions_initial F t₀ hzero l,
    composeSupportedMotions_eqOn_compl F _ hfull l,
    composeSupportedMotions_eqOn_support F _ hfull hpre l hl,
    fun t a ha A B ↦ composeSupportedMotions_branch_image p F V hfull hdis l hl t ha A B⟩

end Geometry
