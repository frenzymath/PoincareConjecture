import PoincareConjecture.Proofs.M38.RefinedZeroCapReconstruction
import PoincareConjecture.Proofs.M38.UnattachedAssembly









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38




theorem canonical_zero_cap_reconstruction
    (N : RepairedNeckCapTopologyTheory.{u}) (F : SurgeryFlowData.{u})
    (hF : SurgeryFlowAdmissible F) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (hcount : (F.event T hT).cap_count = 0)
    (hepsilon : 2 * F.parameters.epsilon ≤ N.epsilon₀) :
    Nonempty (RawNonemptyTopologyWitness F T hT) := by
  classical
  let P := fun i => Classical.choice (exists_event_cap_coordinates F T hT i)
  obtain ⟨n, D, hc, hn, hs, ⟨S⟩⟩ :=
    exists_zeroCap_discarded_assembly F T hT P N hF hcount
      (epsilon_le_threshold N F hepsilon)
  exact zero_cap_reconstruction_of_discarded_assembly F T hT P hcount D hc hn hs S

end PoincareConjecture.M38
