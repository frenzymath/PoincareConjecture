import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.LGeometry.Variation.MinimumComparison

/-!
# Scalar comparison with an inactive constant cap

Morgan--Tian Proposition 16.4, pp. 389-391. In square-root time an
active free minimum has derivative at most (3-2l)/s; the constant
action cap has normalized derivative -l/s. Both upper competitors
point strictly below every constant level above 3/2.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareMT.Proofs.M46

/-- The scalar threshold is preserved with either an actual minimizing
branch or the inactive constant-action cap as upper competitor. -/
theorem capped_minimum_le_of_upper_competitors {f : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hf : ContinuousOn f (Icc a b)) (hstart : f a ≤ 3 / 2)
    (hcontact : ∀ t ∈ Ico a b, ∃ phi : ℝ → ℝ, ∃ d : ℝ,
      HasDerivAt phi d t ∧ phi t = f t ∧
      (∀ᶠ s in 𝓝[>] t, f s ≤ phi s) ∧
      d ≤ max ((3 - 2 * f t) / t) (-f t / t)) :
    ∀ t ∈ Icc a b, f t ≤ 3 / 2 := by
  have hslope : ∀ t ∈ Ico a b, ∀ r,
      max ((3 - 2 * f t) / t) (-f t / t) < r →
      ∃ᶠ s in 𝓝[>] t, slope f t s < r := by
    intro t ht
    obtain ⟨phi, d, hphi, heq, hnear, hd⟩ := hcontact t ht
    exact right_slope_bound_of_upper_competitor hphi heq hnear hd
  intro t ht
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  apply image_le_of_liminf_slope_right_lt_deriv_boundary hf hslope
    (B := fun _ => 3 / 2 + epsilon) (B' := fun _ => 0)
    (hstart.trans (le_add_of_nonneg_right hepsilon.le))
    (fun s => hasDerivAt_const s (3 / 2 + epsilon)) _ ht
  intro s hs heq
  have hspos : 0 < s := ha.trans_le hs.1
  rw [heq]
  exact max_lt (div_neg_of_neg_of_pos (by linarith) hspos)
    (div_neg_of_neg_of_pos (by linarith) hspos)

end PoincareMT.Proofs.M46
