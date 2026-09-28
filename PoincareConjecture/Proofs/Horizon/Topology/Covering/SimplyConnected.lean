import Mathlib.Topology.Homotopy.Lifting

noncomputable section

namespace Poincare.Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}

theorem bijective_of_isCoveringMap_of_simplyConnected
    [PreconnectedSpace E] [Nonempty E]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (hf : IsCoveringMap f) : Function.Bijective f := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  obtain ⟨s, ⟨hs0, hsp⟩, -⟩ :=
    hf.existsUnique_continuousMap_lifts (ContinuousMap.id X) (f e₀) e₀ rfl
  have hfs : Function.RightInverse s f := by
    intro x
    simpa using congrFun hsp x
  refine ⟨?_, hfs.surjective⟩
  have hsf : (⇑s ∘ f) = id := by
    refine hf.eq_of_comp_eq (g₁ := ⇑s ∘ f) (g₂ := id)
      (s.continuous.comp hf.continuous) continuous_id ?_ e₀ ?_
    · funext e
      simp [Function.comp, hfs (f e)]
    · simp [Function.comp, hs0]
  exact (show Function.LeftInverse s f from fun e => congrFun hsf e).injective

end Poincare.Topology
