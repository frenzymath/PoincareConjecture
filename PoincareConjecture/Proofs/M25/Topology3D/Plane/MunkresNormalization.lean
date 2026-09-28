import PoincareConjecture.Proofs.M25.Topology3D.Plane.MunkresSlide
import Mathlib.Analysis.Normed.Group.Bounded










set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem exists_munkres_normalization (h : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hfix : ∀ x, x ∉ K → h x = x) :
    ∃ g : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ), ∃ b d : ℝ,
      0 < b ∧ 0 < d ∧
      (∀ x : ℝ × ℝ, x.2 < d → g x = x) ∧
      (∀ x : ℝ × ℝ, b / 2 ≤ x.2 → g x = x) ∧
      ∃ N : ℝ → ((ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)),
        ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => N p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (N p.1).symm p.2) ∧
        (∀ t, t ≤ 1 / 3 → ∀ x, N t x = h x) ∧
        (∀ t, 2 / 3 ≤ t → ∀ x, N t x = g x) ∧
        (∃ Q : Set (ℝ × ℝ), IsCompact Q ∧
          (∀ t x, x ∉ Q → N t x = x ∧ (N t).symm x = x) ∧
          ∀ x, x ∉ Q → g x = x ∧ g.symm x = x) ∧
        ∀ t, HasCompactSupport (fun x => N t x - x) ∧
          HasCompactSupport (fun x => (N t).symm x - x) := by
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_lt
  let α : ℝ → ℝ := fun t => Real.smoothTransition (3 * t - 1)
  let v : ℝ × ℝ := (0, -(R + 1))
  have hα : ContDiff ℝ ∞ α := Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hαrange (t : ℝ) : α t ∈ Icc 0 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hα0 (t : ℝ) (ht : t ≤ 1 / 3) : α t = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hα1 (t : ℝ) (ht : 2 / 3 ≤ t) : α t = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  obtain ⟨N, hN, hNi, hformula, _, ⟨Q, hQ, hQfix⟩, hsupport⟩ :=
    exists_translation_conjugate_family h v α hα hαrange hK hfix
  let g := N 1
  have hg (x : ℝ × ℝ) : g x = h (x + v) - v := by
    change N 1 x = _
    rw [hformula, hα1 1 (by norm_num), one_smul]
  have hheight (x : ℝ × ℝ) (hx : x + v ∈ K) : |x.2 - (R + 1)| < R := by
    have hh := (norm_snd_le (x + v)).trans_lt (hbound (x + v) hx)
    simpa only [v, Prod.snd_add, Real.norm_eq_abs, sub_eq_add_neg] using hh
  refine ⟨g, 4 * R + 4, 1, by positivity, by norm_num, ?_, ?_,
    N, hN, hNi, ?_, ?_, ⟨Q, hQ, hQfix, hQfix 1⟩, hsupport⟩
  · intro x hx
    have hout : x + v ∉ K := by
      intro hm
      have hh := (abs_lt.mp (hheight x hm)).1
      linarith
    rw [hg, hfix (x + v) hout, add_sub_cancel_right]
  · intro x hx
    have hout : x + v ∉ K := by
      intro hm
      have hh := (abs_lt.mp (hheight x hm)).2
      linarith
    rw [hg, hfix (x + v) hout, add_sub_cancel_right]
  · intro t ht x
    rw [hformula, hα0 t ht, zero_smul, add_zero, sub_zero]
  · intro t ht x
    rw [hformula, hα1 t ht, one_smul, hg]

end PoincareConjecture.M25.Topology3D
