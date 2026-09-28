import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.HalfCylinder

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "Cyl" => Set.prod Q I

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_selected_half_cylinder {A S : Set E} (a : Cyl ≃ₜ A) (ha : a.IsFinitePL)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (haS : ∀ x : Cyl, (a x : E) ∈ S ↔ x.val.2 = σ) :
    ∃ (Z : Set E) (H : Cyl ≃ₜ Z), H.IsFinitePL ∧ Z ⊆ A ∧
      (∀ x : Cyl, (H x : E) ∈ S ↔ x.val.2 = 1) ∧
      (∀ y ∈ S, y ∈ Z ↔ y ∈ A) ∧
      (∀ u : Q, (H ⟨(u, -1), u.property, le_rfl, by norm_num⟩ : E) =
        a ⟨(u, 0), u.property, by norm_num, by norm_num⟩) ∧
      ∀ u : Q, (H ⟨(u, 1), u.property, by norm_num, le_rfl⟩ : E) =
        a ⟨(u, σ), u.property, by rcases hσ with rfl | rfl <;> norm_num⟩ := by
  obtain ⟨Z, hZA, H, hH, hcoord, hhalf, hbottom, htop⟩ :=
    exists_cylinder_half a ha σ hσ
  refine ⟨Z, H, hH, hZA, ?_, ?_, hbottom, htop⟩
  · intro x
    let y := a.symm ⟨H x, hZA (H x).property⟩
    have hy : (a y : E) = H x := congrArg Subtype.val (a.apply_symm_apply _)
    have ht : y.val.2 = σ * (x.val.2 + 1) / 2 := congrArg Prod.snd (hcoord x)
    rw [← hy, haS, ht]
    rcases hσ with rfl | rfl <;> constructor <;> intro h <;> linarith
  · intro y hy
    refine ⟨fun hz ↦ hZA hz, ?_⟩
    intro hyA
    let x := a.symm ⟨y, hyA⟩
    have hx : (a x : E) = y := congrArg Subtype.val (a.apply_symm_apply _)
    have ht : x.val.2 = σ := (haS x).mp (hx.symm ▸ hy)
    exact hx ▸ (hhalf x).mpr (by rw [ht]; rcases hσ with rfl | rfl <;> norm_num)

end PoincareConjecture.M76.Dehn.Annuli
