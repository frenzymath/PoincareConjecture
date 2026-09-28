import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem exists_concat_compact_isotopy
    (h g : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ))
    (N H : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ))
    (hN : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => N p.1 p.2))
    (hNi : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (N p.1).symm p.2))
    (hN0 : ∀ t, t ≤ 1 / 3 → ∀ x, N t x = h x)
    (hN1 : ∀ t, 2 / 3 ≤ t → ∀ x, N t x = g x)
    (hH : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => H p.1 p.2))
    (hHi : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (H p.1).symm p.2))
    (hH0 : ∀ z, z ≤ 0 → ∀ x, H z x = g x)
    (hH1 : ∀ z, 1 ≤ z → ∀ x, H z x = x)
    {Q : Set (ℝ × ℝ)} (hQ : IsCompact Q)
    (hNfix : ∀ t x, x ∉ Q → N t x = x ∧ (N t).symm x = x)
    (hgfix : ∀ x, x ∉ Q → g x = x ∧ g.symm x = x)
    (hHfix : ∀ z x, x ∉ Q → H z x = x ∧ (H z).symm x = x) :
    ∃ M : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => M p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (M p.1).symm p.2) ∧
      (∀ t, t ≤ 0 → ∀ x, M t x = h x) ∧
      (∀ t, 1 ≤ t → ∀ x, M t x = x) ∧
      ∃ S : Set (ℝ × ℝ), IsCompact S ∧
        ∀ t x, x ∉ S → M t x = x ∧ (M t).symm x = x := by
  let M : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) :=
    fun t => (H (2 * t - 1)).trans (g.symm.trans (N (2 * t)))
  have htime : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => 2 * p.1) :=
    contDiff_const.mul contDiff_fst
  have hshift : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => 2 * p.1 - 1) :=
    htime.sub contDiff_const
  refine ⟨M, ?_, ?_, ?_, ?_, Q, hQ, ?_⟩
  · exact hN.comp (htime.prodMk
      (g.symm.contDiff.comp (hH.comp (hshift.prodMk contDiff_snd))))
  · exact hHi.comp (hshift.prodMk
      (g.contDiff.comp (hNi.comp (htime.prodMk contDiff_snd))))
  · intro t ht x
    change N (2 * t) (g.symm (H (2 * t - 1) x)) = h x
    rw [hH0 (2 * t - 1) (by linarith), Diffeomorph.symm_apply_apply,
      hN0 (2 * t) (by linarith)]
  · intro t ht x
    change N (2 * t) (g.symm (H (2 * t - 1) x)) = x
    rw [hH1 (2 * t - 1) (by linarith), hN1 (2 * t) (by linarith),
      Diffeomorph.apply_symm_apply]
  · intro t x hx
    change N (2 * t) (g.symm (H (2 * t - 1) x)) = x ∧
      (H (2 * t - 1)).symm (g ((N (2 * t)).symm x)) = x
    rw [(hHfix (2 * t - 1) x hx).1, (hgfix x hx).2, (hNfix (2 * t) x hx).1,
      (hNfix (2 * t) x hx).2, (hgfix x hx).1, (hHfix (2 * t - 1) x hx).2]
    exact ⟨rfl, rfl⟩

end PoincareConjecture.M25.Topology3D
