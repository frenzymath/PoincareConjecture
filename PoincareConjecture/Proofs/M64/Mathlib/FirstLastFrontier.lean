import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence





noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set

namespace PoincareConjecture

private theorem mapsTo_of_no_frontier
    {X : Type*} [TopologicalSpace X] {K : Set X} {f : ℝ → X} {S : Set ℝ}
    (hc : ContinuousOn f S) (hS : IsPreconnected S)
    (havoid : ∀ t ∈ S, f t ∉ frontier K) {a : ℝ} (ha : a ∈ S) (hfa : f a ∈ K) :
    MapsTo f S K := by
  have hfront : Disjoint (f '' S) (frontier K) := by
    rw [disjoint_left]
    rintro z ⟨t, ht, rfl⟩ hz
    exact havoid t ht hz
  have hstart : f a ∈ interior K := by
    by_contra h
    exact havoid a ha ⟨subset_closure hfa, h⟩
  intro t ht
  exact interior_subset (Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
    (hS.image f hc) hfront ⟨f a, ⟨a, ha, rfl⟩, hstart⟩ ⟨t, ht, rfl⟩)




theorem m64_path_confined_or_first_last_frontier
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsClosed K)
    {f : ℝ → X} (hc : ContinuousOn f (Icc 0 1)) (h0 : f 0 ∈ K) (h1 : f 1 ∈ K) :
    MapsTo f (Icc 0 1) K ∨
      ∃ a b : ℝ, a ∈ Icc 0 1 ∧ b ∈ Icc 0 1 ∧ a ≤ b ∧
        f a ∈ frontier K ∧ f b ∈ frontier K ∧
        MapsTo f (Icc 0 a) K ∧ MapsTo f (Icc b 1) K := by
  let S := Icc (0 : ℝ) 1 ∩ f ⁻¹' frontier K
  by_cases hS : S.Nonempty
  · have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset
      (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_frontier) inter_subset_left
    obtain ⟨a, ha, hleast⟩ := hcompact.exists_isLeast hS
    obtain ⟨b, hb, hgreatest⟩ := hcompact.exists_isGreatest hS
    refine Or.inr ⟨a, b, ha.1, hb.1, hleast hb, ha.2, hb.2, ?_, ?_⟩
    · intro t ht
      rcases ht.2.eq_or_lt with rfl | hta
      · exact hK.frontier_subset ha.2
      · have hsub : Ico (0 : ℝ) a ⊆ Icc 0 1 :=
          fun s hs => ⟨hs.1, hs.2.le.trans ha.1.2⟩
        apply mapsTo_of_no_frontier (hc.mono hsub) isPreconnected_Ico
          (a := 0) (fun s hs hf => ?_) ⟨le_rfl, lt_of_le_of_lt ht.1 hta⟩ h0 ⟨ht.1, hta⟩
        exact (not_le_of_gt hs.2) (hleast ⟨hsub hs, hf⟩)
    · intro t ht
      rcases ht.1.eq_or_lt with rfl | hbt
      · exact hK.frontier_subset hb.2
      · have hsub : Ioc b (1 : ℝ) ⊆ Icc 0 1 :=
          fun s hs => ⟨hb.1.1.trans hs.1.le, hs.2⟩
        apply mapsTo_of_no_frontier (hc.mono hsub) isPreconnected_Ioc
          (a := 1) (fun s hs hf => ?_) ⟨lt_of_lt_of_le hbt ht.2, le_rfl⟩ h1 ⟨hbt, ht.2⟩
        exact (not_le_of_gt hs.1) (hgreatest ⟨hsub hs, hf⟩)
  · left
    apply mapsTo_of_no_frontier hc isPreconnected_Icc (a := 0) _ (by simp) h0
    intro t ht hf
    exact hS ⟨t, ht, hf⟩

end PoincareConjecture
