import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Flow.PartialFlowUnion
import Mathlib.Order.Zorn

/-!
# Maximal continuation under a universal finite lifetime bound

The relation form of Zorn avoids identifying total records outside their
included domains. This isolates the order-theoretic step in Morgan-Tian
Definition 12.4 and Theorem 12.5, pp. 295-297. The universal analytic
lifetime bound is an explicit hypothesis, not a conclusion of this file.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M34

/-- A first partial flow and a universal finite upper bound on all partial
lifetimes give a maximal flow in the exact frozen sense
(Definition 12.4 and Theorem 12.5, pp. 295-297). -/
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

end PoincareMT.M34
