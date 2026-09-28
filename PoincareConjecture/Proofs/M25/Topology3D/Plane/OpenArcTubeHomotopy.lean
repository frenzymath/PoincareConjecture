import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenLineHomotopyTransport

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_openArc_tube_homotopy_transport
    (D : (ℝ × ℝ) × ℝ → ℝ × ℝ) {R : ℝ} (hR : 0 < R)
    (hD : ContDiff ℝ ∞ D)
    (hinj : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      Injective (fun u : ℝ => D (z, u)))
    (hreg : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∀ u : ℝ,
      fderiv ℝ (fun v : ℝ => D (z, v)) u 1 ≠ 0)
    (htail : ∀ z u, R ≤ |u| → D (z, u) = (u, 0))
    (hstat : ∀ t s u, t ≤ 0 ∨ 1 ≤ t →
      D ((t, s), u) = D ((t, 0), u))
    (haxis : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : ℝ,
      (D ((t, 1), u)).2 = 0) :
    ∃ G : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (G p.1).symm p.2) ∧
      (∃ Q : Set (ℝ × ℝ), IsCompact Q ∧
        ∀ t x, x ∉ Q → G t x = x ∧ (G t).symm x = x) ∧
      (∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, G t x = x ∧ (G t).symm x = x) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : ℝ,
        (G t (D ((t, 0), u))).2 = 0 := by
  obtain ⟨G, hG, hGi, hQ, hends, hrange⟩ :=
    exists_compact_openLine_homotopy_transport D hR hD hinj hreg htail hstat
  refine ⟨G, hG, hGi, hQ, hends, ?_⟩
  intro t ht u
  have hmem : G t (D ((t, 0), u)) ∈
      range (fun v : ℝ => D ((t, 1), v)) := by
    rw [← hrange t ht]
    exact ⟨u, rfl⟩
  rcases hmem with ⟨v, hv⟩
  rw [← hv]
  exact haxis t ht v

end PoincareConjecture.M25.Topology3D
