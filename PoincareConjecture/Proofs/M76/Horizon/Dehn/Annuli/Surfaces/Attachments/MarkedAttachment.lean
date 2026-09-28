import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.HalfCollarAttachment
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.SquareCylinder

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "Cyl" => Set.prod Q I

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem exists_named_cylinder_level {A M : Set E} (a : Cyl ≃ₜ A)
    (ha : a.IsFinitePL) (hMA : M ⊆ A) (v : I)
    (hlevel : ∀ x : Cyl, (a x : E) ∈ M ↔ x.val.2 = v) :
    ∃ g : Q ≃ₜ M, g.IsFinitePL ∧
      ∀ u : Q, (g u : E) = a ⟨(u, v), u.property, v.property⟩ := by
  obtain ⟨R, g, hg, hRA, hgv, hR⟩ := exists_cylinder_level_chart a ha v
  have hRM : R = M := by
    ext y
    constructor
    · intro hy
      let x := a.symm ⟨y, hRA hy⟩
      have hx : (a x : E) = y := congrArg Subtype.val (a.apply_symm_apply _)
      exact hx ▸ (hlevel x).mpr ((hR x).mp (hx.symm ▸ hy))
    · intro hy
      let x := a.symm ⟨y, hMA hy⟩
      have hx : (a x : E) = y := congrArg Subtype.val (a.apply_symm_apply _)
      exact hx ▸ (hR x).mpr ((hlevel x).mp (hx.symm ▸ hy))
  exact ⟨g.trans (Homeomorph.setCongr hRM), hg.setCongr rfl hRM, hgv⟩

theorem exists_marked_half_collar_attachment {A S B M₀ M₁ : Set E}
    (a : Cyl ≃ₜ A) (c : Cyl ≃ₜ S) (b : Cyl ≃ₜ B)
    (ha : a.IsFinitePL) (hc : c.IsFinitePL) (hb : b.IsFinitePL)
    (hdis : Disjoint A B) (σ τ : ℝ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1)
    (hac : ∀ x : Cyl, (a x : E) ∈ S ↔ x.val.2 = σ)
    (hca : ∀ x : Cyl, (c x : E) ∈ A ↔ x.val.2 = -1)
    (hcb : ∀ x : Cyl, (c x : E) ∈ B ↔ x.val.2 = 1)
    (hbc : ∀ x : Cyl, (b x : E) ∈ S ↔ x.val.2 = τ)
    (hM₀ : M₀ ⊆ A) (hM₁ : M₁ ⊆ B)
    (haM : ∀ x : Cyl, (a x : E) ∈ M₀ ↔ x.val.2 = 0)
    (hbM : ∀ x : Cyl, (b x : E) ∈ M₁ ↔ x.val.2 = 0) :
    ∃ (T : Set E) (H : squareAnnulus 8 1 ≃ₜ T), H.IsFinitePL ∧
      S ⊆ T ∧ T ⊆ (A ∪ S) ∪ B ∧ M₀ ⊆ T ∧ M₁ ⊆ T ∧
      (∀ x, (H x : E) ∈ M₀ ↔ depth 8 x = -1) ∧
      ∀ x, (H x : E) ∈ M₁ ↔ depth 8 x = 1 := by
  obtain ⟨T, H, q, hH, _, hST, hT, hleft, hright⟩ :=
    exists_half_collar_attachment a c b ha hc hb hdis σ τ hσ hτ hac hca hcb hbc
  obtain ⟨g, _, hgv⟩ := exists_named_cylinder_level a ha hM₀ ⟨0, by norm_num⟩ haM
  obtain ⟨f, _, hfv⟩ := exists_named_cylinder_level b hb hM₁ ⟨0, by norm_num⟩ hbM
  have hgH (u : Q) :
      (H ⟨(u, (-1 : ℝ)), u.property, le_rfl, by norm_num⟩ : E) = g u :=
    (hleft u).trans (hgv u).symm
  have hfH (u : Q) :
      (H ⟨(u, (1 : ℝ)), u.property, by norm_num, le_rfl⟩ : E) = (q.trans f) u :=
    (hright u).trans (hfv (q u)).symm
  have hM₀T : M₀ ⊆ T := by
    intro y hy
    obtain ⟨u, hu⟩ := g.surjective ⟨y, hy⟩
    have heq := (hgH u).trans (congrArg Subtype.val hu)
    have hm := (H ⟨(u, -1), u.property, le_rfl, by norm_num⟩).property
    simpa only [heq] using hm
  have hM₁T : M₁ ⊆ T := by
    intro y hy
    obtain ⟨u, hu⟩ := (q.trans f).surjective ⟨y, hy⟩
    have heq := (hfH u).trans (congrArg Subtype.val hu)
    have hm := (H ⟨(u, 1), u.property, by norm_num, le_rfl⟩).property
    simpa only [heq] using hm
  obtain ⟨C, hC, hCv⟩ := exists_selected_annulus_cylinder
  refine ⟨T, C.trans H, hC.trans hH, hST, hT, hM₀T, hM₁T, ?_, ?_⟩
  · intro x
    exact (cylinder_rim_mem_iff H g ⟨-1, by norm_num⟩ hgH (C x)).trans
      (by rw [hCv])
  · intro x
    exact (cylinder_rim_mem_iff H (q.trans f) ⟨1, by norm_num⟩ hfH (C x)).trans
      (by rw [hCv])

end PoincareConjecture.M76.Dehn.Annuli
