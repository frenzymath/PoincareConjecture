import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.ScheduledBranchCharts

/-!
# Whole disk images outside the actual change support

A motion need only fix the original disk off a small set. The union of
that set with its endpoint image contains every change in the whole disk
image. Disjoint scheduling windows give the same exact statement for
the finite composite.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {X Y α T : Type*} [TopologicalSpace X]

/-- Off the old and new change supports, every complete branch image is
unchanged, even when the ambient homeomorphism moves points off the disk. -/
theorem homeomorph_disk_branch_image_off_change
    (p : X → Y) (H : X ≃ₜ X) (A S : Set X)
    (hfix : EqOn H id (A \ S)) (B : Set X) :
    p '' (H '' A ∩ B) \ p '' (S ∪ H '' S) =
      p '' (A ∩ B) \ p '' (S ∪ H '' S) := by
  ext y
  constructor
  · rintro ⟨⟨_, ⟨⟨x, hx, rfl⟩, hxB⟩, rfl⟩, hy⟩
    have hxS : x ∉ S := fun hs ↦ hy ⟨H x, Or.inr ⟨x, hs, rfl⟩, rfl⟩
    have heq : H x = x := hfix ⟨hx, hxS⟩
    exact ⟨⟨x, ⟨hx, heq ▸ hxB⟩, congrArg p heq.symm⟩, hy⟩
  · rintro ⟨⟨x, ⟨hx, hxB⟩, rfl⟩, hy⟩
    have hxS : x ∉ S := fun hs ↦ hy ⟨x, Or.inl hs, rfl⟩
    have heq : H x = x := hfix ⟨hx, hxS⟩
    exact ⟨⟨x, ⟨⟨x, hx, heq⟩, hxB⟩, rfl⟩, hy⟩

/-- An original disk point whose endpoint lies off the changed image
was fixed by the motion. -/
theorem homeomorph_disk_fixed_of_output_off_change
    (p : X → Y) (H : X ≃ₜ X) (A S : Set X)
    (hfix : EqOn H id (A \ S)) {x : X} (hx : x ∈ A)
    (hy : p (H x) ∉ p '' (S ∪ H '' S)) : H x = x := by
  exact hfix ⟨hx, fun hs ↦ hy ⟨H x, Or.inr ⟨x, hs, rfl⟩, rfl⟩⟩

/-- Finite disjoint supports prevent another repair from changing the
endpoint image of the selected small source support. -/
theorem composeSupportedMotions_agree_of_output_mem
    (p : X → Y) (F : α → T → X ≃ₜ X) (V : α → Set Y)
    (hfix : ∀ a t, EqOn (F a t) id (p ⁻¹' V a)ᶜ)
    (hdis : Pairwise (fun a b ↦ Disjoint (V a) (V b)))
    (l : List α) (hl : l.Nodup) (t : T) {a : α} (ha : a ∈ l) {x : X}
    (hx : p (F a t x) ∈ V a ∨ p (composeSupportedMotions F l t x) ∈ V a) :
    composeSupportedMotions F l t x = F a t x := by
  have hpre : Pairwise (fun a b ↦ Disjoint (p ⁻¹' V a) (p ⁻¹' V b)) :=
    fun a b hne ↦ (hdis hne).preimage p
  have heq := composeSupportedMotions_eqOn_support F (fun a ↦ p ⁻¹' V a)
    hfix hpre l hl t a ha
  rcases hx with hx | hx
  · apply heq
    by_contra hn
    have hv : F a t x = x := hfix a t hn
    exact hn (hv ▸ hx)
  · exact homeomorph_eq_of_image_mem_support _ _ heq (hfix a t) hx

/-- Finite disjoint supports prevent another repair from changing the
endpoint image of the selected small source support. -/
theorem composeSupportedMotions_change_image
    (p : X → Y) (F : α → T → X ≃ₜ X) (V : α → Set Y)
    (hfix : ∀ a t, EqOn (F a t) id (p ⁻¹' V a)ᶜ)
    (hdis : Pairwise (fun a b ↦ Disjoint (V a) (V b)))
    (S : α → Set X) (hSV : ∀ a, S a ⊆ p ⁻¹' V a)
    (l : List α) (hl : l.Nodup) (t : T) :
    composeSupportedMotions F l t '' (⋃ a ∈ l, S a) =
      ⋃ a ∈ l, F a t '' S a := by
  have hpre : Pairwise (fun a b ↦ Disjoint (p ⁻¹' V a) (p ⁻¹' V b)) :=
    fun a b hne ↦ (hdis hne).preimage p
  have heq := composeSupportedMotions_eqOn_support F (fun a ↦ p ⁻¹' V a)
    hfix hpre l hl t
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨a, ha, hzS⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨a, ha, z, hzS, (heq a ha (hSV a hzS)).symm⟩
  · intro hx
    obtain ⟨a, ha, z, hzS, rfl⟩ := mem_iUnion₂.mp hx
    exact ⟨z, mem_iUnion₂.mpr ⟨a, ha, hzS⟩, heq a ha (hSV a hzS)⟩

/-- A finite family fixing the original disk outside its individual
small supports fixes that disk outside their union. -/
theorem composeSupportedMotions_disk_fixed
    (F : α → T → X ≃ₜ X) (A : Set X) (S : α → Set X)
    (hfix : ∀ a t, EqOn (F a t) id (A \ S a)) (l : List α) (t : T) :
    EqOn (composeSupportedMotions F l t) id (A \ ⋃ a ∈ l, S a) := by
  induction l with
  | nil => exact fun _ _ ↦ rfl
  | cons a l ih =>
    intro x hx
    have hxS : x ∉ S a := fun h ↦ hx.2 (mem_iUnion₂.mpr ⟨a, List.mem_cons_self, h⟩)
    have hxl : x ∉ ⋃ b ∈ l, S b := by
      intro h
      obtain ⟨b, hb, hxB⟩ := mem_iUnion₂.mp h
      exact hx.2 (mem_iUnion₂.mpr ⟨b, List.mem_cons_of_mem a hb, hxB⟩)
    change F a t (composeSupportedMotions F l t x) = x
    rw [ih ⟨hx.1, hxl⟩]
    exact hfix a t ⟨hx.1, hxS⟩

/-- The finite composite changes the disk only over the finite union of
the individual old and endpoint supports. -/
theorem composeSupportedMotions_disk_branch_image_off_change
    (p : X → Y) (F : α → T → X ≃ₜ X) (V : α → Set Y)
    (hfix : ∀ a t, EqOn (F a t) id (p ⁻¹' V a)ᶜ)
    (hdis : Pairwise (fun a b ↦ Disjoint (V a) (V b)))
    (A : Set X) (S : α → Set X) (hSV : ∀ a, S a ⊆ p ⁻¹' V a)
    (hdisk : ∀ a t, EqOn (F a t) id (A \ S a))
    (l : List α) (hl : l.Nodup) (t : T) (B : Set X) :
    p '' (composeSupportedMotions F l t '' A ∩ B) \
        (⋃ a ∈ l, p '' (S a ∪ F a t '' S a)) =
      p '' (A ∩ B) \ (⋃ a ∈ l, p '' (S a ∪ F a t '' S a)) := by
  have h := homeomorph_disk_branch_image_off_change p (composeSupportedMotions F l t)
    A (⋃ a ∈ l, S a) (composeSupportedMotions_disk_fixed F A S hdisk l t) B
  rw [composeSupportedMotions_change_image p F V hfix hdis S hSV l hl t] at h
  simpa only [image_union, image_iUnion, iUnion_union_distrib] using h

/-- Either old or new membership in the unchanged region forces literal
agreement at an original disk point. -/
theorem composeSupportedMotions_disk_agree_off_change
    (p : X → Y) (F : α → T → X ≃ₜ X) (V : α → Set Y)
    (hfix : ∀ a t, EqOn (F a t) id (p ⁻¹' V a)ᶜ)
    (hdis : Pairwise (fun a b ↦ Disjoint (V a) (V b)))
    (A : Set X) (S : α → Set X) (hSV : ∀ a, S a ⊆ p ⁻¹' V a)
    (hdisk : ∀ a t, EqOn (F a t) id (A \ S a))
    (l : List α) (hl : l.Nodup) (t : T) {x : X} (hx : x ∈ A)
    (hy : p x ∉ ⋃ a ∈ l, p '' (S a ∪ F a t '' S a) ∨
      p (composeSupportedMotions F l t x) ∉ ⋃ a ∈ l, p '' (S a ∪ F a t '' S a)) :
    composeSupportedMotions F l t x = x := by
  apply composeSupportedMotions_disk_fixed F A S hdisk l t
  refine ⟨hx, ?_⟩
  intro hxS
  obtain ⟨a, ha, hxA⟩ := mem_iUnion₂.mp hxS
  rcases hy with hy | hy
  · exact hy (mem_iUnion₂.mpr ⟨a, ha, x, Or.inl hxA, rfl⟩)
  · have himage := composeSupportedMotions_change_image p F V hfix hdis S hSV l hl t
    have hm := himage.subset (mem_image_of_mem (composeSupportedMotions F l t)
      (mem_iUnion₂.mpr ⟨a, ha, hxA⟩))
    obtain ⟨b, hb, hz⟩ := mem_iUnion₂.mp hm
    exact hy (mem_iUnion₂.mpr ⟨b, hb, _, Or.inr hz, rfl⟩)

/-- Compact old supports and their actual endpoint images give a closed
change set in the target. -/
theorem isClosed_finite_disk_change [TopologicalSpace Y] [T2Space Y]
    (p : X → Y) (hp : Continuous p) (F : α → T → X ≃ₜ X)
    (S : α → Set X) (hS : ∀ a, IsCompact (S a)) (l : List α) (t : T) :
    IsClosed (⋃ a ∈ l, p '' (S a ∪ F a t '' S a)) :=
  l.finite_toSet.isClosed_biUnion (fun a _ ↦
    ((hS a).union ((hS a).image (F a t).continuous)).image hp |>.isClosed)

end Geometry
