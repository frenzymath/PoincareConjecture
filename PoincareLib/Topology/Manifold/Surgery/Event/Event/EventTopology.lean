import PoincareLib.Topology.Manifold.Surgery.Event.Positive.PositiveCapAssembly
import PoincareLib.Topology.Manifold.Surgery.Event.Refined.RefinedPositiveCapReconstruction
import PoincareLib.Topology.Manifold.Surgery.Event.Zero.ZeroCapCanonical
import PoincareLib.Topology.Manifold.Surgery.Event.Classified.ClassifiedComponents

/-!
# Raw local surgery topology for every admissible flow

One threshold is chosen before the raw flow. Classified assembly of the
actual capped discarded carrier reconstructs each positive-cap event, while
the existing whole-component assemblies handle zero caps and whole-slice
vanishing. The witnesses retain actual cap correspondence and no survivors
in the vanishing branch.
Source: Morgan--Tian Proposition 15.3, printed pp. 357-358.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M38

/-- Given the supplied Appendix A theory, choose a positive bound uniformly
before the flow and construct the full raw event data for every admissible
flow below that bound. No event classification or reconstruction is assumed. -/
theorem exists_raw_local_surgery_topology_data
    (N : RepairedNeckCapTopologyTheory.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ N.epsilon₀ ∧
      ∀ F : SurgeryFlowData.{u}, SurgeryFlowAdmissible F →
        2 * F.parameters.epsilon ≤ epsilon0 →
        Nonempty (RawLocalSurgeryTopologyData F) := by
  classical
  obtain ⟨epsilon0, hpos, hbound, hassembly⟩ := exists_positiveCap_discarded_assembly N
  have hN : epsilon0 ≤ N.epsilon₀ := hbound.trans (min_le_left _ _)
  refine ⟨epsilon0, hpos, hN, ?_⟩
  intro F hF hepsilon
  have hsmall : F.parameters.epsilon ≤ epsilon0 := by
    linarith [F.parameters.epsilon_pos]
  refine ⟨{
    admissible := hF
    nonempty_reconstruction := ?_
    vanishing_reconstruction := ?_ }⟩
  · intro T hT _
    by_cases hcount : (F.event T hT).cap_count = 0
    · exact canonical_zero_cap_reconstruction N F hF T hT hcount (hepsilon.trans hN)
    · let P := fun i => Classical.choice (exists_event_cap_coordinates F T hT i)
      obtain ⟨n, D, hc, hn, hs, ⟨S⟩⟩ := hassembly F hF hsmall T hT P
      exact positive_cap_reconstruction_of_discarded_assembly F T hT P
        (Nat.pos_of_ne_zero hcount) D hc hn hs S
  · intro T hT _
    exact canonical_vanishing_reconstruction N F hF T hT (hepsilon.trans hN)

end PoincareMT.M38
