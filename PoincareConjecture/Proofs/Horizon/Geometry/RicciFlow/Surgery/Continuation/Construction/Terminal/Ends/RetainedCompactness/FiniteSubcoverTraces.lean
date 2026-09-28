import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.RetainedCompactness.FiniteComponents








set_option autoImplicit false

open Set

namespace Poincare.Topology

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  [LocallyConnectedSpace X] [PreconnectedSpace X]

theorem exists_component_trace_without_finite_cover (K : CompactExhaustion X)
    (V : ι → Set X) {A : Set X}
    (hA : ∀ (s : Finset ι) (L : Set X), IsCompact L →
      ¬ A ⊆ L ∪ ⋃ i ∈ s, V i) (n : ℕ) :
    ∃ p : X, p ∈ (K n)ᶜ ∧
      ∀ (s : Finset ι) (L : Set X), IsCompact L →
        ¬ A ∩ connectedComponentIn (K n)ᶜ p ⊆ L ∪ ⋃ i ∈ s, V i := by
  classical
  obtain ⟨points, hp, hcover⟩ := exists_finite_component_cover_outside_compact
    (K.isCompact n) (K.isCompact (n + 1)) (K.subset_interior_succ n)
  by_contra h
  push Not at h
  choose s L hL hsub using fun p : points => h p.val (hp p.val p.property)
  let all : Finset ι := Finset.univ.biUnion s
  let B : Set X := K (n + 1) ∪ ⋃ p : points, L p
  have hB : IsCompact B := (K.isCompact (n + 1)).union (isCompact_iUnion hL)
  apply hA all B hB
  intro x hx
  by_cases hxK : x ∈ K (n + 1)
  · exact Or.inl (Or.inl hxK)
  · obtain ⟨p, hp, hxp⟩ := hcover x hxK
    rcases hsub ⟨p, hp⟩ ⟨hx, hxp⟩ with hxL | hxV
    · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨⟨p, hp⟩, hxL⟩))
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxV
      exact Or.inr (mem_iUnion₂.mpr ⟨i,
        Finset.mem_biUnion.mpr ⟨⟨p, hp⟩, Finset.mem_univ _, hi⟩, hxi⟩)



theorem exists_nested_component_traces_without_finite_cover
    (K : CompactExhaustion X) (V : ι → Set X) {A : Set X}
    (hA : ∀ (s : Finset ι) (L : Set X), IsCompact L →
      ¬ A ⊆ L ∪ ⋃ i ∈ s, V i) :
    ∃ p : ℕ → X, (∀ n, p n ∈ (K n)ᶜ) ∧
      Antitone (fun n => connectedComponentIn (K n)ᶜ (p n)) ∧
      ∀ n (s : Finset ι) (L : Set X), IsCompact L →
        ¬ A ∩ connectedComponentIn (K n)ᶜ (p n) ⊆ L ∪ ⋃ i ∈ s, V i := by
  classical
  let State (n : ℕ) := {p : X // p ∈ (K n)ᶜ ∧
    ∀ (s : Finset ι) (L : Set X), IsCompact L →
      ¬ A ∩ connectedComponentIn (K n)ᶜ p ⊆ L ∪ ⋃ i ∈ s, V i}
  have hstep (n : ℕ) (p : State n) :
      ∃ q : State (n + 1), connectedComponentIn (K (n + 1))ᶜ q.val ⊆
        connectedComponentIn (K n)ᶜ p.val := by
    obtain ⟨q, hq, htrace⟩ :=
      exists_component_trace_without_finite_cover K V p.property.2 (n + 1)
    have hne : ((A ∩ connectedComponentIn (K n)ᶜ p.val) ∩
        connectedComponentIn (K (n + 1))ᶜ q).Nonempty := by
      apply nonempty_iff_ne_empty.mpr
      intro heq
      exact htrace ∅ ∅ isCompact_empty (by simp [heq])
    obtain ⟨y, ⟨_, hyp⟩, hyq⟩ := hne
    have hmono : connectedComponentIn (K (n + 1))ᶜ q ⊆
        connectedComponentIn (K n)ᶜ q :=
      connectedComponentIn_mono q (compl_subset_compl.mpr (K.subset_succ n))
    have heq : connectedComponentIn (K n)ᶜ q = connectedComponentIn (K n)ᶜ p.val :=
      (connectedComponentIn_eq (hmono hyq)).trans (connectedComponentIn_eq hyp).symm
    have hsub : connectedComponentIn (K (n + 1))ᶜ q ⊆
        connectedComponentIn (K n)ᶜ p.val := heq ▸ hmono
    refine ⟨⟨q, hq, ?_⟩, hsub⟩
    intro s L hL hAL
    exact htrace s L hL (fun x hx => hAL ⟨hx.1.1, hx.2⟩)
  obtain ⟨p₀, hp₀, htrace₀⟩ := exists_component_trace_without_finite_cover K V hA 0
  let p : (n : ℕ) → State n := Nat.rec ⟨p₀, hp₀, htrace₀⟩
    (fun n prev => Classical.choose (hstep n prev))
  refine ⟨fun n => (p n).val, fun n => (p n).property.1, ?_,
    fun n => (p n).property.2⟩
  apply antitone_nat_of_succ_le
  intro n
  exact Classical.choose_spec (hstep n (p n))

end Poincare.Topology
