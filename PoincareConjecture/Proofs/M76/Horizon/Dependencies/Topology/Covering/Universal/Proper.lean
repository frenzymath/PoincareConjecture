import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Maps.Proper.CompactlyGenerated









set_option autoImplicit false

open Set Function Topology

namespace Poincare.Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}


theorem isCoveringMap_of_proper_localHomeomorph [T2Space E]
    (hp : IsLocalHomeomorph p) (hproper : IsProperMap p) : IsCoveringMap p := by
  intro x
  have hcharts : ∀ e ∈ p ⁻¹' {x},
      ∃ φ : OpenPartialHomeomorph E X, e ∈ φ.source ∧ φ = p := by
    intro e _
    obtain ⟨φ, hφ, heq⟩ := hp e
    exact ⟨φ, hφ, heq.symm⟩
  exact hproper.isClosedMap.isEvenlyCovered_of_openPartialHomeomorph
    ((hproper.isCompact_preimage isCompact_singleton).finite
      (IsDiscrete.of_openPartialHomeomorph p subset_rfl hcharts)) hcharts



theorem injective_covering_of_simplyConnected [PreconnectedSpace E]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (hp : IsCoveringMap p) : Injective p := by
  intro a b hab
  obtain ⟨s, ⟨hsa, hs⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts ⟨id, continuous_id⟩ (p a) a rfl
  have hsp : (s : X → E) ∘ p = id := hp.eq_of_comp_eq
    (s.continuous.comp hp.continuous) continuous_id
    (by funext e; exact congr_fun hs (p e)) a hsa
  calc
    a = s (p a) := (congr_fun hsp a).symm
    _ = s (p b) := congr_arg s hab
    _ = b := congr_fun hsp b



theorem bijective_proper_localHomeomorph [T2Space E] [ConnectedSpace E]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (hp : IsLocalHomeomorph p) (hproper : IsProperMap p) : Bijective p := by
  have hcover := isCoveringMap_of_proper_localHomeomorph hp hproper
  refine ⟨injective_covering_of_simplyConnected hcover, ?_⟩
  rw [← range_eq_univ]
  exact (show IsClopen (range p) from
    ⟨hproper.isClosedMap.isClosed_range, hp.isOpenMap.isOpen_range⟩).eq_univ
      (range_nonempty p)

end Poincare.Topology
