import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenArcTubeHomotopy

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_axis_preserving_correction_of_certified_homotopy
    (F : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ))
    (_hline : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 (p.2, 0)))
    (_hinj : ∀ z, Injective (fun u : ℝ => F z (u, 0)))
    (_hreg : ∀ z u : ℝ, deriv (fun s => F z (s, 0)) u ≠ 0)
    {Q : Set (ℝ × ℝ)} (_hQ : IsCompact Q)
    (_hQfix : ∀ z x, x ∉ Q → F z x = x)
    (hends : ∀ z, z ≤ 1 / 3 ∨ 2 / 3 ≤ z → ∀ u : ℝ,
      F z (u, 0) = (u, 0))
    (D : (ℝ × ℝ) × ℝ → ℝ × ℝ) {R : ℝ} (hR : 0 < R)
    (hD : ContDiff ℝ ∞ D)
    (hDinj : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      Injective (fun u : ℝ => D (z, u)))
    (hDreg : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∀ u : ℝ,
      fderiv ℝ (fun v : ℝ => D (z, v)) u 1 ≠ 0)
    (hDtail : ∀ z u, R ≤ |u| → D (z, u) = (u, 0))
    (hDstat : ∀ t s u, t ≤ 0 ∨ 1 ≤ t →
      D ((t, s), u) = D ((t, 0), u))
    (hDinitial : ∀ t u, D ((t, 0), u) = F t (u, 0))
    (hDaxis : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : ℝ,
      (D ((t, 1), u)).2 = 0) :
    ∃ G : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2) ∧
      (∃ S : Set (ℝ × ℝ), IsCompact S ∧
        ∀ z x, x ∉ S → G z x = x ∧ (G z).symm x = x) ∧
      (∀ z, z ≤ 0 ∨ 1 ≤ z → ∀ x, G z x = x) ∧
      ∀ z u : ℝ, (G z (F z (u, 0))).2 = 0 := by
  obtain ⟨G, hG, _hGi, hsupport, hstationary, haxis⟩ :=
    exists_openArc_tube_homotopy_transport D hR hD hDinj hDreg hDtail hDstat
      hDaxis
  refine ⟨G, hG, hsupport, ?_, ?_⟩
  · intro z hz x
    exact (hstationary z hz x).1
  · intro z u
    by_cases hzlo : z ≤ 0
    · have hGid := (hstationary z (Or.inl hzlo) (F z (u, 0))).1
      rw [hGid, hends z (Or.inl (by linarith)) u]
    · by_cases hzhi : 1 ≤ z
      · have hGid := (hstationary z (Or.inr hzhi) (F z (u, 0))).1
        rw [hGid, hends z (Or.inr (by linarith)) u]
      · have hzI : z ∈ Icc (0 : ℝ) 1 := ⟨le_of_not_ge hzlo, le_of_not_ge hzhi⟩
        rw [← hDinitial z u]
        exact haxis z hzI u

end PoincareConjecture.M25.Topology3D
