import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.CylinderRims



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "Cyl" => Set.prod Q I

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_three_cylinder_attachment {A S B : Set E}
    (a : Cyl ≃ₜ A) (c : Cyl ≃ₜ S) (b : Cyl ≃ₜ B)
    (ha : a.IsFinitePL) (hc : c.IsFinitePL) (hb : b.IsFinitePL)
    (hdis : Disjoint A B)
    (hac : ∀ x : Cyl, (a x : E) ∈ S ↔ x.val.2 = 1)
    (hca : ∀ x : Cyl, (c x : E) ∈ A ↔ x.val.2 = -1)
    (hcb : ∀ x : Cyl, (c x : E) ∈ B ↔ x.val.2 = 1)
    (hbc : ∀ x : Cyl, (b x : E) ∈ S ↔ x.val.2 = -1) :
    ∃ (H : Cyl ≃ₜ ((A ∪ S) ∪ B : Set E)) (q : Q ≃ₜ Q),
      H.IsFinitePL ∧ q.IsFinitePL ∧
      (∀ u : Q, (H ⟨(u, -1), u.property, le_rfl, by norm_num⟩ : E) =
        a ⟨(u, -1), u.property, le_rfl, by norm_num⟩) ∧
      ∀ u : Q, (H ⟨(u, 1), u.property, by norm_num, le_rfl⟩ : E) =
        b ⟨(q u, 1), (q u).property, by norm_num, le_rfl⟩ := by
  obtain ⟨G, q, hG, _, hGa, hGc⟩ := exists_cylinder_end_gluing a c ha hc hac hca
  obtain ⟨R, g, _, hRS, hgv, hgmem⟩ :=
    exists_cylinder_level_chart c hc ⟨1, by norm_num⟩
  have hRiff (y : E) (hy : y ∈ A ∪ S) : y ∈ B ↔ y ∈ R := by
    constructor
    · intro hyB
      have hyS : y ∈ S := hy.resolve_left (fun hyA ↦ Set.disjoint_left.mp hdis hyA hyB)
      let x := c.symm ⟨y, hyS⟩
      have hx : (c x : E) = y := congrArg Subtype.val (c.apply_symm_apply _)
      exact hx ▸ (hgmem x).mpr ((hcb x).mp (hx.symm ▸ hyB))
    · intro hyR
      let x := c.symm ⟨y, hRS hyR⟩
      have hx : (c x : E) = y := congrArg Subtype.val (c.apply_symm_apply _)
      exact hx ▸ (hcb x).mpr ((hgmem x).mp (hx.symm ▸ hyR))
  have hGrim (u : Q) :
      (G ⟨(u, (1 : ℝ)), u.property, by norm_num, le_rfl⟩ : E) = (q.trans g) u :=
    (hGc u).trans (hgv (q u)).symm
  have hGB (x : Cyl) : (G x : E) ∈ B ↔ x.val.2 = 1 :=
    (hRiff (G x) (G x).property).trans
      (cylinder_rim_mem_iff G (q.trans g) ⟨1, by norm_num⟩ hGrim x)
  have hBG (x : Cyl) : (b x : E) ∈ A ∪ S ↔ x.val.2 = -1 := by
    constructor
    · intro hx
      apply (hbc x).mp
      exact hx.resolve_left (fun hA ↦ Set.disjoint_left.mp hdis hA (b x).property)
    · intro hx
      exact Or.inr ((hbc x).mpr hx)
  obtain ⟨H, r, hH, hr, hHG, hHb⟩ := exists_cylinder_end_gluing G b hG hb hGB hBG
  exact ⟨H, r, hH, hr, fun u ↦ (hHG u).trans (hGa u), hHb⟩

end PoincareConjecture.M76.Dehn.Annuli
