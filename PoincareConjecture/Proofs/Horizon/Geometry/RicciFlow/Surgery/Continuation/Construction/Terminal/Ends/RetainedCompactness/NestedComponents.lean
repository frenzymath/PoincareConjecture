import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.RetainedCompactness.FiniteComponents








set_option autoImplicit false

open Set

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [LocallyConnectedSpace X] [PreconnectedSpace X]



theorem exists_nested_unbounded_component_traces (K : CompactExhaustion X)
    {A : Set X} (hA : ∀ L : Set X, IsCompact L → ¬ A ⊆ L) :
    ∃ p : ℕ → X, (∀ n, p n ∈ (K n)ᶜ) ∧
      Antitone (fun n => connectedComponentIn (K n)ᶜ (p n)) ∧
      ∀ n, ∀ L : Set X, IsCompact L →
        ¬ A ∩ connectedComponentIn (K n)ᶜ (p n) ⊆ L := by
  classical
  let State (n : ℕ) := {p : X // p ∈ (K n)ᶜ ∧
    ∀ L : Set X, IsCompact L → ¬ A ∩ connectedComponentIn (K n)ᶜ p ⊆ L}
  have hstep (n : ℕ) (p : State n) :
      ∃ q : State (n + 1), connectedComponentIn (K (n + 1))ᶜ q.val ⊆
        connectedComponentIn (K n)ᶜ p.val := by
    obtain ⟨q, hq, htrace⟩ := exists_unbounded_component_trace K p.property.2 (n + 1)
    have hne : ((A ∩ connectedComponentIn (K n)ᶜ p.val) ∩
        connectedComponentIn (K (n + 1))ᶜ q).Nonempty := by
      apply nonempty_iff_ne_empty.mpr
      intro heq
      exact htrace ∅ isCompact_empty (heq ▸ subset_rfl)
    obtain ⟨y, ⟨_, hyp⟩, hyq⟩ := hne
    have hmono : connectedComponentIn (K (n + 1))ᶜ q ⊆
        connectedComponentIn (K n)ᶜ q :=
      connectedComponentIn_mono q (compl_subset_compl.mpr (K.subset_succ n))
    have heq : connectedComponentIn (K n)ᶜ q = connectedComponentIn (K n)ᶜ p.val :=
      (connectedComponentIn_eq (hmono hyq)).trans (connectedComponentIn_eq hyp).symm
    have hsub : connectedComponentIn (K (n + 1))ᶜ q ⊆
        connectedComponentIn (K n)ᶜ p.val := heq ▸ hmono
    refine ⟨⟨q, hq, ?_⟩, hsub⟩
    intro L hL hAL
    exact htrace L hL (fun x hx => hAL ⟨hx.1.1, hx.2⟩)
  obtain ⟨p₀, hp₀, htrace₀⟩ := exists_unbounded_component_trace K hA 0
  let p : (n : ℕ) → State n := Nat.rec ⟨p₀, hp₀, htrace₀⟩
    (fun n prev => Classical.choose (hstep n prev))
  refine ⟨fun n => (p n).val, fun n => (p n).property.1, ?_,
    fun n => (p n).property.2⟩
  apply antitone_nat_of_succ_le
  intro n
  exact Classical.choose_spec (hstep n (p n))

end Poincare.Topology
