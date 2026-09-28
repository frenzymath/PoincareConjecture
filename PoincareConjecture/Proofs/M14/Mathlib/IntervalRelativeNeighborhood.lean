import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M14

theorem ordConnected_mem_nhdsWithin_of_directions {C D : Set ℝ} {t : ℝ}
    (hC : OrdConnected C) (ht : t ∈ C)
    (hleft : (∃ a ∈ D, a < t) → ∃ a ∈ C, a < t)
    (hright : (∃ b ∈ D, t < b) → ∃ b ∈ C, t < b) : C ∈ 𝓝[D] t := by
  have hl : ∃ a < t, ∀ s ∈ D, a < s → s ≤ t → s ∈ C := by
    by_cases hprev : ∃ a ∈ D, a < t
    · obtain ⟨a, ha, hat⟩ := hleft hprev
      exact ⟨a, hat, fun _ _ has hst => hC.out ha ht ⟨has.le, hst⟩⟩
    · refine ⟨t - 1, by linarith, ?_⟩
      intro s hs _ hst
      have heq : s = t := le_antisymm hst (le_of_not_gt (fun hlt => hprev ⟨s, hs, hlt⟩))
      simpa only [heq] using ht
  have hr : ∃ b > t, ∀ s ∈ D, t ≤ s → s < b → s ∈ C := by
    by_cases hnext : ∃ b ∈ D, t < b
    · obtain ⟨b, hb, htb⟩ := hright hnext
      exact ⟨b, htb, fun _ _ hts hsb => hC.out ht hb ⟨hts, hsb.le⟩⟩
    · refine ⟨t + 1, by linarith, ?_⟩
      intro s hs hts _
      have heq : s = t := le_antisymm (le_of_not_gt (fun hlt => hnext ⟨s, hs, hlt⟩)) hts
      simpa only [heq] using ht
  obtain ⟨a, ha, hla⟩ := hl
  obtain ⟨b, hb, hrb⟩ := hr
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds ha hb)]
    with s hs hab
  rcases le_total s t with hst | hts
  · exact hla s hs hab.1 hst
  · exact hrb s hs hts hab.2

end PoincareConjecture.M14
