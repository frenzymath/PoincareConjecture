import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.NestedDiskAnnulus
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FinitePLSphereDiskComplement










set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_square_annulus_two_cap_complement
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {S : Set E} {C : Set F} (e : S ≃ₜ frontier C) (he : e.IsFinitePL)
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hdim : Module.finrank ℝ F = 3)
    {d₀ q₀ d₁ q₁ : Set E} (h₀ : IsFinitePLBallPair P2 d₀ q₀)
    (h₁ : IsFinitePLBallPair P2 d₁ q₁) (h₀S : d₀ ⊆ S) (h₁S : d₁ ⊆ S)
    (hdis : Disjoint d₀ d₁) :
    ∃ H : Ann ≃ₜ (S \ ((d₀ \ q₀) ∪ (d₁ \ q₁)) : Set E), H.IsFinitePL ∧
      (∀ z : Ann, depth 8 (z : P2) = -1 ↔ (H z : E) ∈ q₀) ∧
      (∀ z : Ann, depth 8 (z : P2) = 1 ↔ (H z : E) ∈ q₁) := by
  have hout : (S \ d₀).Nonempty := by
    obtain ⟨x, hx, _⟩ := h₁.sdiff_nonempty
    exact ⟨x, h₁S hx, fun hx₀ ↦ disjoint_left.mp hdis hx₀ hx⟩
  have hD := he.sphere_disk_complement hC hcv hne hdim h₀ h₀S hout
  have hinner : d₁ ⊆ (S \ (d₀ \ q₀)) \ q₀ := by
    intro x hx
    have hx₀ : x ∉ d₀ := fun h ↦ disjoint_left.mp hdis h hx
    exact ⟨⟨h₁S hx, fun h ↦ hx₀ h.1⟩, fun h ↦ hx₀ (h₀.1 h)⟩
  obtain ⟨A, hA, hout, hin⟩ := exists_square_annulus_nested_ball_pairs h₁ hD hinner
  have hcarrier : (S \ (d₀ \ q₀)) \ (d₁ \ q₁) =
      S \ ((d₀ \ q₀) ∪ (d₁ \ q₁)) := by ext x; simp only [mem_sdiff, mem_union, not_or, and_assoc]
  let H := A.trans (Homeomorph.setCongr hcarrier)
  exact ⟨H, hA.setCongr rfl hcarrier, hout, hin⟩

end PoincareConjecture.M76.Dehn
