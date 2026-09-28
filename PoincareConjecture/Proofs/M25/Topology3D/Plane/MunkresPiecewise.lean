import PoincareConjecture.Proofs.M25.Topology3D.Plane.AxisStripCorrection
import PoincareConjecture.Proofs.M25.Topology3D.Plane.HalfPlaneCut










set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D




theorem exists_isotopy_of_axis_preserving_correction
    (h : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ))
    (hlower : ∀ x : ℝ × ℝ, x.2 ≤ 0 → h x = x)
    (F G : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ))
    (hF : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2))
    (hG : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2))
    {K Q : Set (ℝ × ℝ)} (hK : IsCompact K) (hQ : IsCompact Q)
    (hFfix : ∀ z x, x ∉ K → F z x = x)
    (hGfix : ∀ z x, x ∉ Q → G z x = x)
    (hFzero : ∀ z, z ≤ 0 → ∀ x, F z x = h x)
    (hFone : ∀ z, 1 ≤ z → ∀ x : ℝ × ℝ, 0 ≤ x.2 → F z x = x)
    {ε : ℝ} (hε : 0 < ε)
    (hstrip : ∀ z, z ≤ 0 ∨ 1 ≤ z → ∀ x : ℝ × ℝ, |x.2| < ε → F z x = x)
    (hGend : ∀ z, z ≤ 0 ∨ 1 ≤ z → ∀ x, G z x = x)
    (haxis : ∀ z u : ℝ, (G z (F z (u, 0))).2 = 0) :
    ∃ H : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => H p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (H p.1).symm p.2) ∧
      (∀ z, z ≤ 0 → ∀ x, H z x = h x) ∧
      (∀ z, 1 ≤ z → ∀ x, H z x = x) ∧
      ∃ S : Set (ℝ × ℝ), IsCompact S ∧
        ∀ z x, x ∉ S → H z x = x ∧ (H z).symm x = x := by
  let L : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) := fun z => (F z).trans (G z)
  have hL : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => L p.1 p.2) :=
    hG.comp (contDiff_fst.prodMk hF)
  have hLi := contDiff_diffeomorph_family_symm L hL
  have hLfix (z : ℝ) (x : ℝ × ℝ) (hx : x ∉ K ∪ Q) : L z x = x := by
    change G z (F z x) = x
    rw [hFfix z x (fun hxK => hx (Or.inl hxK)),
      hGfix z x (fun hxQ => hx (Or.inr hxQ))]
  have hLstrip (z : ℝ) (hz : z ≤ 0 ∨ 1 ≤ z) (x : ℝ × ℝ) (hx : |x.2| < ε) :
      L z x = x := by
    change G z (F z x) = x
    rw [hstrip z hz x hx, hGend z hz]
  obtain ⟨δ, hδ, C, hC, hCi, hCstrip, hCend, R, hR, hCfix⟩ :=
    exists_axis_strip_correction L hL (hK.union hQ) hLfix haxis hε hLstrip
  let J : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) := fun z => (L z).trans (C z)
  have hJ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => J p.1 p.2) :=
    hC.comp (contDiff_fst.prodMk hL)
  have hJi : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (J p.1).symm p.2) :=
    hLi.comp (contDiff_fst.prodMk hCi)
  have hJstrip (z : ℝ) (x : ℝ × ℝ) (hx : |x.2| < δ) : J z x = x :=
    hCstrip z x hx.le
  let S := (K ∪ Q) ∪ R
  have hS : IsCompact S := (hK.union hQ).union hR
  have hJfix (z : ℝ) (x : ℝ × ℝ) (hx : x ∉ S) : J z x = x := by
    change C z (L z x) = x
    rw [hLfix z x (fun hxKQ => hx (Or.inl hxKQ)),
      (hCfix z x (fun hxR => hx (Or.inr hxR))).1]
  obtain ⟨H, hH, hHi, hupper, hlowerH, _, _, hHfix, _⟩ :=
    exists_upper_halfSpace_diffeomorph_family J hJ hJi hδ hJstrip hS hJfix
  refine ⟨H, hH, hHi, ?_, ?_, S, hS, hHfix⟩
  · intro z hz x
    by_cases hx : 0 ≤ x.2
    · rw [hupper z x hx]
      change C z (G z (F z x)) = h x
      rw [hCend z (Or.inl hz), hGend z (Or.inl hz), hFzero z hz]
    · rw [hlowerH z x (le_of_lt (lt_of_not_ge hx)),
        hlower x (le_of_lt (lt_of_not_ge hx))]
  · intro z hz x
    by_cases hx : 0 ≤ x.2
    · rw [hupper z x hx]
      change C z (G z (F z x)) = x
      rw [hCend z (Or.inr hz), hGend z (Or.inr hz), hFone z hz x hx]
    · exact hlowerH z x (le_of_lt (lt_of_not_ge hx))

end PoincareConjecture.M25.Topology3D
