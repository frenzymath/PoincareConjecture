import PoincareConjecture.Proofs.M34.Thm12_5_Existence.PartialFlowUnion
import Mathlib.Order.Zorn

set_option autoImplicit false

open Set

namespace PoincareConjecture.M34

theorem maximalStandardCapFlow_exists_of_bounded_lifetimes
    {g0 : StandardInitialMetric} (F0 : PartialStandardCapFlow g0)
    {B : ℝ} (hB : ∀ F : PartialStandardCapFlow g0, F.lifetime ≤ B) :
    Nonempty (MaximalStandardCapFlow g0) := by
  let : Nonempty (PartialStandardCapFlow g0) := ⟨F0⟩
  have hchains : ∀ c : Set (PartialStandardCapFlow g0), IsChain partialFlowLE c →
      c.Nonempty → ∃ G, ∀ F ∈ c, partialFlowLE F G := by
    intro c hc hne
    have hbdd : BddAbove ((fun F : PartialStandardCapFlow g0 => F.lifetime) '' c) := by
      refine ⟨B, ?_⟩
      rintro T ⟨F, _hF, rfl⟩
      exact hB F
    obtain ⟨G, _hGtime, hG⟩ := partialFlowChain_has_upper_bound hc hne hbdd
    exact ⟨G, hG⟩
  obtain ⟨F, hF⟩ := exists_maximal_of_nonempty_chains_bounded hchains
    (fun hFG hGH => partialFlowLE_trans hFG hGH)
  refine ⟨⟨F, ?_⟩⟩
  intro T ⟨E⟩
  have hback := hF (partialFlowOfExtension E) (partialFlowLE_extension E)
  exact (not_lt_of_ge hback.1) E.lifetime_gt

end PoincareConjecture.M34
