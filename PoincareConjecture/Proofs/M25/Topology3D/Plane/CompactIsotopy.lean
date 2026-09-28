import PoincareConjecture.Proofs.M25.Topology3D.Sphere2.CompactPlaneTransfer
import PoincareConjecture.Proofs.M25.Topology3D.Plane.MunkresPiecewise
import PoincareConjecture.Proofs.M25.Topology3D.Plane.MunkresNormalization
import PoincareConjecture.Proofs.M25.Topology3D.Plane.CompactIsotopyConcat
import PoincareConjecture.Proofs.M25.Topology3D.Plane.MovingAxisCorrection

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem compactPlanarIsotopyProperty_of_axis_preserving_correction
    (hCorrection : ∀ (F : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)),
      ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 (p.2, 0)) →
      (∀ z, Injective (fun u : ℝ => F z (u, 0))) →
      (∀ z u : ℝ, deriv (fun s => F z (s, 0)) u ≠ 0) →
      ∀ {Q : Set (ℝ × ℝ)}, IsCompact Q →
      (∀ z x, x ∉ Q → F z x = x) →
      (∀ z, z ≤ 1 / 3 ∨ 2 / 3 ≤ z → ∀ u : ℝ, F z (u, 0) = (u, 0)) →
      ∃ G : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
        ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2) ∧
        (∃ S : Set (ℝ × ℝ), IsCompact S ∧ ∀ z x, x ∉ S → G z x = x) ∧
        (∀ z, z ≤ 0 ∨ 1 ≤ z → ∀ x, G z x = x) ∧
        ∀ z u : ℝ, (G z (F z (u, 0))).2 = 0) :
    CompactPlanarIsotopyProperty := by
  intro h K hK hfix
  obtain ⟨g, b, d, hb, hd, hglow, hgup, N, hN, hNi, hN0, hN1,
    ⟨Q₁, hQ₁, hNfix, hgfix⟩, -⟩ := exists_munkres_normalization h hK hfix
  have hgK : ∀ x, x ∉ Q₁ → g x = x := fun x hx => (hgfix x hx).1
  obtain ⟨F, hF, -, -, hF0, hF1, ⟨ε, hε, hstrip⟩, hline, hinj, hreg,
    ⟨Q₂, hQ₂, hFfix⟩, -⟩ := exists_munkres_slide g hQ₁ hgK hb hd hglow hgup
  have hends : ∀ z, z ≤ 1 / 3 ∨ 2 / 3 ≤ z → ∀ u : ℝ, F z (u, 0) = (u, 0) :=
    fun z hz u => hstrip z hz (u, 0) (by simpa only [abs_zero] using hε)
  obtain ⟨G, hG, ⟨S, hS, hGfix⟩, hGend, haxis⟩ :=
    hCorrection F hline hinj hreg hQ₂ (fun z x hx => (hFfix z x hx).1) hends
  obtain ⟨H, hH, hHi, hH0, hH1, S', hS', hHfix⟩ :=
    exists_isotopy_of_axis_preserving_correction g
      (fun x hx => hglow x (lt_of_le_of_lt hx hd)) F G hF hG hQ₂ hS
      (fun z x hx => (hFfix z x hx).1) hGfix
      (fun z hz x => hF0 z (by linarith) x)
      (fun z hz x hx => hF1 z (by linarith) x hx) hε
      (fun z hz x hx => hstrip z (hz.imp (fun h => by linarith) (fun h => by linarith)) x hx)
      hGend haxis
  obtain ⟨M, hM, hMi, hM0, hM1, S'', hS'', hMfix⟩ :=
    exists_concat_compact_isotopy h g N H hN hNi hN0 hN1 hH hHi hH0 hH1
      (hQ₁.union hS')
      (fun t x hx => hNfix t x (fun h' => hx (Or.inl h')))
      (fun x hx => hgfix x (fun h' => hx (Or.inl h')))
      (fun z x hx => hHfix z x (fun h' => hx (Or.inr h')))
  exact ⟨M, hM, hMi, hM0, hM1, S'', hS'', hMfix⟩

theorem compactPlanarIsotopyProperty : CompactPlanarIsotopyProperty :=
  compactPlanarIsotopyProperty_of_axis_preserving_correction
    exists_axis_preserving_correction_of_slide

end PoincareConjecture.M25.Topology3D
