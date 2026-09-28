import PoincareConjecture.Proofs.M38.PositiveCapAssembly
import PoincareConjecture.Proofs.M38.RefinedPositiveCapReconstruction
import PoincareConjecture.Proofs.M38.ZeroCapCanonical
import PoincareConjecture.Proofs.M38.ClassifiedComponents

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

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

end PoincareConjecture.M38
