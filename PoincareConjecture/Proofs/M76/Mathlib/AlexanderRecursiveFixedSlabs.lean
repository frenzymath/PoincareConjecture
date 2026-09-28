import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith









set_option autoImplicit false

open Set

namespace Homeomorph

variable {X : Type*} [TopologicalSpace X]




theorem image_inter_eq_of_fixedOn (H : X ≃ₜ X) {s V : Set X}
    (hfix : ∀ x ∈ V, H x = x) : (H '' s) ∩ V = s ∩ V := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, hyV⟩
    have hxy' : x = y := H.injective (hxy.trans (hfix y hyV).symm)
    exact ⟨hxy' ▸ hx, hyV⟩
  · intro hy
    exact ⟨⟨y, hy.1, hfix y hy.2⟩, hy.2⟩



theorem capped_image_inter_eq_of_fixedOn (H : X ≃ₜ X) {s d V : Set X}
    (hfix : ∀ x ∈ V, H x = x) (hdV : Disjoint d V) :
    (H '' (s ∪ d)) ∩ V = s ∩ V := by
  rw [H.image_inter_eq_of_fixedOn hfix, union_inter_distrib_right,
    hdV.inter_eq, union_empty]





theorem capped_image_height_band_eq (H : X ≃ₜ X) (A : X → ℝ)
    {s d : Set X} {δ : ℝ} (hδ : 0 < δ)
    (hfix : ∀ x, δ ≤ |A x| → H x = x) (hd : d ⊆ {x | A x = 0})
    (I : Set ℝ) (hI : ∀ c ∈ I, δ ≤ |c|) :
    (H '' (s ∪ d)) ∩ A ⁻¹' I = s ∩ A ⁻¹' I := by
  apply H.capped_image_inter_eq_of_fixedOn (fun x hx => hfix x (hI (A x) hx))
  apply disjoint_left.mpr
  intro x hxd hxI
  have h := hI (A x) hxI
  rw [hd hxd, abs_zero] at h
  exact (not_le_of_gt hδ) h





theorem exists_capped_image_fixed_height_band (H : X ≃ₜ X) (A : X → ℝ)
    {s d : Set X} {δ : ℝ} (hδ : 0 < δ)
    (hfix : ∀ x, δ ≤ |A x| → H x = x) (hd : d ⊆ {x | A x = 0})
    {c : ℝ} (hc : δ < |c|) :
    ∃ ε : ℝ, 0 < ε ∧
      (H '' (s ∪ d)) ∩ {x | A x ∈ Icc (c - ε) (c + ε)} =
        s ∩ {x | A x ∈ Icc (c - ε) (c + ε)} := by
  let ε := (|c| - δ) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  refine ⟨ε, hε, H.capped_image_height_band_eq A hδ hfix hd _ ?_⟩
  intro a ha
  have hdist : |c - a| ≤ ε := abs_le.mpr ⟨by linarith [ha.2], by linarith [ha.1]⟩
  have htriangle : |c| ≤ |a| + |c - a| := by
    calc
      |c| = |a + (c - a)| := by congr 1; linarith
      _ ≤ |a| + |c - a| := abs_add_le _ _
  dsimp [ε] at hdist
  linarith

end Homeomorph
