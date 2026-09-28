import PoincareConjecture.Proofs.M35.RadialGauge.SmoothTargetCoupling
import PoincareConjecture.Proofs.M35.RadialGauge.ScalarRapidProducts

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

theorem smoothTargetCoupling_rapid_jets {A : Type*} {f : A → ℝ → ℝ}
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hf0 : ∀ a, f a 0 = 0)
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      |iteratedDeriv j (f a) r| ≤ C)
    (hr : ∀ j N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      (1 + r) ^ N * |iteratedDeriv j (deriv (f a)) r| ≤ C) :
    ∀ j N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      (1 + r) ^ N * |iteratedDeriv j (smoothTargetCoupling (f a)) r| ≤ C := by
  have hp := scalar_rapid_product (fun a => (hf a).contDiffOn)
    (fun a => (contDiff_infty_iff_deriv.mp (hf a)).2.contDiffOn) hb hr
  have hi (a : A) : ContDiffOn ℝ ∞ (fun r : ℝ => 1 / r) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun _ hr => ne_of_gt hr)
  have hib (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (_a : A) r, 1 ≤ r →
      |iteratedDeriv j (fun s : ℝ => 1 / s) r| ≤ C :=
    ⟨j.factorial, Nat.cast_nonneg _, fun _ _ hr => reciprocal_radius_jet_bound j hr⟩
  have hh := scalar_rapid_product hi
    (fun a => ((hf a).mul (contDiff_infty_iff_deriv.mp (hf a)).2).contDiffOn) hib hp
  intro j N
  obtain ⟨C, hC, hCb⟩ := hh j N
  refine ⟨C, hC, ?_⟩
  intro a r hrad
  have hpos : 0 < r := lt_of_lt_of_le zero_lt_one hrad
  have heq : smoothTargetCoupling (f a) =ᶠ[𝓝 r]
      fun s => (1 / s) * (f a s * deriv (f a) s) := by
    filter_upwards [eventually_gt_nhds hpos] with s hs
    rw [smoothTargetCoupling_eq_exterior (hf a) (hf0 a) hs.ne']
    simp only [radialTargetCoupling, div_eq_mul_inv, one_mul]
    ring
  rw [heq.iteratedDeriv_eq j]
  exact hCb a r hrad

end PoincareConjecture.M35.RadialGauge
