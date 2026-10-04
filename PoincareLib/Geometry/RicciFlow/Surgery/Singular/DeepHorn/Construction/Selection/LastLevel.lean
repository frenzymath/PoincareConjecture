import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# A last level crossing on a compact real interval

The intermediate-value step in Morgan--Tian Theorem 11.31, printed
pp. 291-292, can be chosen so that the remaining ray stays above the
prescribed scalar level. Compactness of the actual level set gives a
last crossing even when the continuous function oscillates.
Reviewed derivation: `selected-horn-level.md`, section 1.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M32

/-- A continuous real function crossing a level has a last crossing on
the compact interval, after which it stays above that level. The
application is the selected scalar level in Theorem 11.31, pp. 291-292. -/
theorem exists_last_level_Icc {a b r : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (ha : f a ≤ r) (hb : r ≤ f b) :
    ∃ c ∈ Icc a b, f c = r ∧ ∀ t ∈ Icc c b, r ≤ f t := by
  obtain ⟨c₀, hc₀, hfc₀⟩ := intermediate_value_Icc hab hf ⟨ha, hb⟩
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let K : Set (Icc a b) := {x | f x = r}
  have hK : IsCompact K := (isClosed_eq hf.domRestrict continuous_const).isCompact
  obtain ⟨c, hc, hmax⟩ := hK.exists_isMaxOn ⟨⟨c₀, hc₀⟩, hfc₀⟩
    (continuous_subtype_val : Continuous (fun x : Icc a b => (x : ℝ))).continuousOn
  refine ⟨c, c.property, hc, ?_⟩
  intro t ht
  by_contra hnot
  have htr : f t < r := lt_of_not_ge hnot
  have hct : (c : ℝ) < t := by
    apply lt_of_le_of_ne ht.1
    intro heq
    have heq' : f t = r := heq ▸ hc
    exact htr.ne heq'
  have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc (c.property.1.trans ht.1) le_rfl
  obtain ⟨d, hd, hfd⟩ := intermediate_value_Icc ht.2 (hf.mono hsub) ⟨htr.le, hb⟩
  have hdc : d ≤ c := hmax (show (⟨d, hsub hd⟩ : Icc a b) ∈ K from hfd)
  exact (hct.trans_le hd.1).not_ge hdc

end PoincareMT.M32
