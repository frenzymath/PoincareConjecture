import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.SelectedHalf
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.CylinderReversal
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.ThreeCylinders

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "Cyl" => Set.prod Q I

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_half_collar_attachment {A S B : Set E}
    (a : Cyl ≃ₜ A) (c : Cyl ≃ₜ S) (b : Cyl ≃ₜ B)
    (ha : a.IsFinitePL) (hc : c.IsFinitePL) (hb : b.IsFinitePL)
    (hdis : Disjoint A B) (σ τ : ℝ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1)
    (hac : ∀ x : Cyl, (a x : E) ∈ S ↔ x.val.2 = σ)
    (hca : ∀ x : Cyl, (c x : E) ∈ A ↔ x.val.2 = -1)
    (hcb : ∀ x : Cyl, (c x : E) ∈ B ↔ x.val.2 = 1)
    (hbc : ∀ x : Cyl, (b x : E) ∈ S ↔ x.val.2 = τ) :
    ∃ (T : Set E) (H : Cyl ≃ₜ T) (q : Q ≃ₜ Q),
      H.IsFinitePL ∧ q.IsFinitePL ∧ S ⊆ T ∧ T ⊆ (A ∪ S) ∪ B ∧
      (∀ u : Q, (H ⟨(u, -1), u.property, le_rfl, by norm_num⟩ : E) =
        a ⟨(u, 0), u.property, by norm_num, by norm_num⟩) ∧
      ∀ u : Q, (H ⟨(u, 1), u.property, by norm_num, le_rfl⟩ : E) =
        b ⟨(q u, 0), (q u).property, by norm_num, by norm_num⟩ := by
  obtain ⟨Z, A0, hA0, hZA, hA0S, hSZ, hA0bottom, _⟩ :=
    exists_selected_half_cylinder a ha σ hσ hac
  obtain ⟨W, B0, hB0, hWB, hB0S, hSW, hB0bottom, _⟩ :=
    exists_selected_half_cylinder b hb τ hτ hbc
  obtain ⟨J, hJ, hJv⟩ := exists_cylinder_reversal
  let B1 := J.trans B0
  have hB1 : B1.IsFinitePL := hJ.trans hB0
  have hB1S (x : Cyl) : (B1 x : E) ∈ S ↔ x.val.2 = -1 := by
    change (B0 (J x) : E) ∈ S ↔ _
    rw [hB0S, hJv]
    change -x.val.2 = 1 ↔ x.val.2 = -1
    constructor <;> intro h <;> linarith
  have hcZ (x : Cyl) : (c x : E) ∈ Z ↔ x.val.2 = -1 :=
    (hSZ (c x) (c x).property).trans (hca x)
  have hcW (x : Cyl) : (c x : E) ∈ W ↔ x.val.2 = 1 :=
    (hSW (c x) (c x).property).trans (hcb x)
  have hZW : Disjoint Z W := hdis.mono hZA hWB
  obtain ⟨H, q, hH, hq, hHA, hHB⟩ :=
    exists_three_cylinder_attachment A0 c B1 hA0 hc hB1 hZW hA0S hcZ hcW hB1S
  refine ⟨(Z ∪ S) ∪ W, H, q, hH, hq, fun _ hx ↦ Or.inl (Or.inr hx), ?_,
    fun u ↦ (hHA u).trans (hA0bottom u), ?_⟩
  · intro x hx
    rcases hx with (h | h) | h
    · exact Or.inl (Or.inl (hZA h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr (hWB h)
  · intro u
    have hrev : J ⟨(q u, 1), (q u).property, by norm_num, le_rfl⟩ =
        ⟨(q u, -1), (q u).property, le_rfl, by norm_num⟩ := by
      apply Subtype.ext
      exact (hJv _).trans (by rfl)
    refine (hHB u).trans ?_
    change (B0 (J _) : E) = _
    rw [hrev]
    exact hB0bottom (q u)

end PoincareConjecture.M76.Dehn.Annuli
