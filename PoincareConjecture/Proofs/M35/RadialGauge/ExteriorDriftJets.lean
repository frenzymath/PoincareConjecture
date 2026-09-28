import PoincareConjecture.Proofs.M35.RadialGauge.ScalarWeightedProducts
import PoincareConjecture.Proofs.M35.RadialGauge.ExteriorCoefficients










set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {A : Type*} {f v : A → ℝ → ℝ}


theorem radialGaugeDrift_jets_bounded
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hv : ∀ a, ContDiff ℝ ∞ (v a))
    (hpos : ∀ a r, 0 < r → 0 < f a r)
    (hfb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      |iteratedDeriv j (f a) r| ≤ C)
    (hib : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      |iteratedDeriv j (fun s => 1 / f a s) r| ≤ C)
    (hvb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      |iteratedDeriv j (v a) r| ≤ C) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      |iteratedDeriv j (radialGaugeDrift (f a) (v a)) r| ≤ C := by
  have hdf (a : A) : ContDiff ℝ ∞ (deriv (f a)) := (contDiff_infty_iff_deriv.mp (hf a)).2
  have hi (a : A) : ContDiffOn ℝ ∞ (fun s => 1 / f a s) (Ioi 0) :=
    contDiffOn_const.div (hf a).contDiffOn (fun r hr => (hpos a r hr).ne')
  have hdb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      |iteratedDeriv j (deriv (f a)) r| ≤ C := by
    simpa only [iteratedDeriv_succ'] using hfb (j + 1)
  have hw (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      (1 + r) ^ (0 : ℕ) * |iteratedDeriv j (fun s => 1 / f a s) r| ≤ C := by
    simpa only [pow_zero, one_mul] using hib j
  have hpb := scalar_weighted_product (fun a => (hdf a).contDiffOn) hi hdb hw
  intro j
  obtain ⟨C, hC, hCb⟩ := hpb j
  simp only [pow_zero, one_mul] at hCb
  obtain ⟨V, hV, hVb⟩ := hvb j
  refine ⟨2 * C + 2 * (j.factorial : ℝ) + V, by positivity, ?_⟩
  intro a r hr
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let q : ℝ → ℝ := fun s => deriv (f a) s * (1 / f a s)
  have hq : ContDiffAt ℝ ∞ q r :=
    (hdf a).contDiffAt.mul ((hi a r hrp).contDiffAt (Ioi_mem_nhds hrp))
  have hir : ContDiffAt ℝ ∞ (fun s : ℝ => 1 / s) r :=
    contDiffAt_const.div contDiffAt_id hrp.ne'
  have heq : radialGaugeDrift (f a) (v a) =
      fun s => (2 * q s - 2 * (1 / s)) - v a s := by
    funext s
    simp only [radialGaugeDrift, q, div_eq_mul_inv, one_mul]
    ring
  have horder : (j : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  rw [heq, iteratedDeriv_fun_sub
    (((contDiffAt_const.mul hq).sub (contDiffAt_const.mul hir)).of_le horder)
    (((hv a).contDiffAt).of_le horder),
    iteratedDeriv_fun_sub ((contDiffAt_const.mul hq).of_le horder)
      ((contDiffAt_const.mul hir).of_le horder), iteratedDeriv_const_mul_field,
    iteratedDeriv_const_mul_field]
  have htriangle : |2 * iteratedDeriv j q r -
      2 * iteratedDeriv j (fun s : ℝ => 1 / s) r - iteratedDeriv j (v a) r| ≤
      |2 * iteratedDeriv j q r| +
        |2 * iteratedDeriv j (fun s : ℝ => 1 / s) r| + |iteratedDeriv j (v a) r| := by
    have h1 := norm_sub_le (2 * iteratedDeriv j q r -
      2 * iteratedDeriv j (fun s : ℝ => 1 / s) r) (iteratedDeriv j (v a) r)
    have h2 := norm_sub_le (2 * iteratedDeriv j q r)
      (2 * iteratedDeriv j (fun s : ℝ => 1 / s) r)
    simp only [Real.norm_eq_abs] at h1 h2
    linarith
  rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num] at htriangle
  have hqbound : |iteratedDeriv j q r| ≤ C := hCb a r hr
  have hinv := reciprocal_radius_jet_bound j hr
  have hvbound := hVb a r hr
  linarith



theorem radialGaugeDrift_div_radius_weighted_jets
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hv : ∀ a, ContDiff ℝ ∞ (v a))
    (hpos : ∀ a r, 0 < r → 0 < f a r)
    (hfb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      |iteratedDeriv j (f a) r| ≤ C)
    (hib : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      |iteratedDeriv j (fun s => 1 / f a s) r| ≤ C)
    (hvb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      |iteratedDeriv j (v a) r| ≤ C) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      (1 + r) * |iteratedDeriv j (fun s => radialGaugeDrift (f a) (v a) s / s) r| ≤ C := by
  have hs (a : A) : ContDiffOn ℝ ∞ (radialGaugeDrift (f a) (v a)) (Ioi 0) :=
    (((contDiffOn_const.mul (contDiff_infty_iff_deriv.mp (hf a)).2.contDiffOn).div
      (hf a).contDiffOn (fun r hr => (hpos a r hr).ne')).sub
      (contDiffOn_const.div contDiffOn_id (fun _ hr => ne_of_gt hr))).sub (hv a).contDiffOn
  have hi (a : A) : ContDiffOn ℝ ∞ (fun s : ℝ => 1 / s) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun _ hr => ne_of_gt hr)
  have hib' (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (_a : A) r, 1 ≤ r →
      (1 + r) ^ (1 : ℕ) * |iteratedDeriv j (fun s : ℝ => 1 / s) r| ≤ C :=
    ⟨2 * j.factorial, by positivity, fun _ r hr => by
      simpa only [pow_one] using reciprocal_radius_weighted_jet_bound j hr⟩
  simpa only [pow_one, div_eq_mul_inv, one_mul] using
    scalar_weighted_product hs hi (radialGaugeDrift_jets_bounded hf hv hpos hfb hib hvb) hib'

end PoincareConjecture.M35.RadialGauge
