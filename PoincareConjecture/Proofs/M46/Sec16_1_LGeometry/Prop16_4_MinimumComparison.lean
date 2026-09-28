import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.Proofs.M46

theorem right_slope_bound_of_upper_competitor {f phi : ℝ → ℝ} {t d v : ℝ}
    (hphi : HasDerivAt phi d t) (heq : phi t = f t)
    (hnear : ∀ᶠ s in 𝓝[>] t, f s ≤ phi s) (hd : d ≤ v) :
    ∀ r, v < r → ∃ᶠ s in 𝓝[>] t, slope f t s < r := by
  intro r hr
  have hslope : ∃ᶠ s in 𝓝[>] t, slope phi t s < r :=
    (hphi.hasDerivWithinAt (s := Ici t)).liminf_right_slope_le (hd.trans_lt hr)
  apply (hslope.and_eventually (hnear.and self_mem_nhdsWithin)).mono
  intro s hs
  have hst : t < s := hs.2.2
  apply lt_of_le_of_lt _ hs.1
  rw [slope_def_field, slope_def_field, heq]
  exact div_le_div_of_nonneg_right (sub_le_sub_right hs.2.1 _)
    (sub_pos.mpr hst).le

theorem minimum_le_of_right_upper_competitors {f : ℝ → ℝ} {a b c : ℝ}
    (ha : 0 < a) (hf : ContinuousOn f (Icc a b)) (hstart : f a ≤ c)
    (hcontact : ∀ t ∈ Ico a b, ∃ phi : ℝ → ℝ, ∃ d : ℝ,
      HasDerivAt phi d t ∧ phi t = f t ∧
      (∀ᶠ s in 𝓝[>] t, f s ≤ phi s) ∧ d ≤ (c - f t) / t) :
    ∀ t ∈ Icc a b, f t ≤ c := by
  have hslope : ∀ t ∈ Ico a b, ∀ r,
      (c - f t) / t < r → ∃ᶠ s in 𝓝[>] t, slope f t s < r := by
    intro t ht
    obtain ⟨phi, d, hphi, heq, hnear, hd⟩ := hcontact t ht
    exact right_slope_bound_of_upper_competitor hphi heq hnear hd
  intro t ht
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  apply image_le_of_liminf_slope_right_lt_deriv_boundary hf hslope
    (B := fun _ => c + epsilon) (B' := fun _ => 0)
    (hstart.trans (le_add_of_nonneg_right hepsilon.le))
    (fun s => hasDerivAt_const s (c + epsilon)) _ ht
  intro s hs heq
  have hspos : 0 < s := ha.trans_le hs.1
  rw [heq]
  exact div_neg_of_neg_of_pos (by linarith) hspos

end PoincareConjecture.Proofs.M46
