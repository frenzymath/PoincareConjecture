import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Piecewise
import Mathlib.Data.Set.Card

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

theorem exists_frontier_avoiding_replacement
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {D B : Set E} {Y F : Set X} {g : E → X}
    (hB : IsClosed B) (hBD : B ⊆ interior D)
    (hg : ContinuousOn g D) (hgY : MapsTo g D Y)
    (fill : C(B, Y))
    (hrim : ∀ (x : B), (x : E) ∈ frontier B → (fill x : X) = g x)
    (havoid : ∀ x : B, (fill x : X) ∉ F) :
    ∃ g' : E → X, ContinuousOn g' D ∧ MapsTo g' D Y ∧
      (∀ x : B, g' x = (fill x : X)) ∧ EqOn g' g Bᶜ ∧
      EqOn g' g (frontier D) ∧ D ∩ g' ⁻¹' F = (D ∩ g ⁻¹' F) \ B := by
  classical
  let f : E → X := fun x => if hx : x ∈ B then (fill ⟨x, hx⟩ : X) else g x
  have hf (x : B) : f x = (fill x : X) := by simp only [f, dif_pos x.property]
  have hfB : ContinuousOn f B := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : B.domRestrict f = fun x : B => (fill x : X) := funext hf
    rw [heq]
    exact continuous_subtype_val.comp fill.continuous
  let g' : E → X := B.piecewise f g
  have hval (x : B) : g' x = (fill x : X) := by
    rw [show g' x = f x from piecewise_eq_of_mem B f g x.property]
    exact hf x
  have hout : EqOn g' g Bᶜ := fun x hx => piecewise_eq_of_notMem B f g hx
  have hcont : ContinuousOn g' D := by
    apply ContinuousOn.piecewise
    · intro x hx
      exact (hf ⟨x, hB.frontier_subset hx.2⟩).trans
        (hrim ⟨x, hB.frontier_subset hx.2⟩ hx.2)
    · rw [hB.closure_eq]
      exact hfB.mono inter_subset_right
    · exact hg.mono inter_subset_left
  refine ⟨g', hcont, ?_, hval, hout, ?_, ?_⟩
  · intro x hx
    by_cases hxB : x ∈ B
    · rw [hval ⟨x, hxB⟩]
      exact (fill ⟨x, hxB⟩).property
    · rw [hout hxB]
      exact hgY hx
  · intro x hx
    apply hout
    intro hxB
    exact hx.2 (hBD hxB)
  · ext x
    by_cases hxB : x ∈ B
    · have hnot : g' x ∉ F := by rw [hval ⟨x, hxB⟩]; exact havoid ⟨x, hxB⟩
      simp only [mem_inter_iff, mem_preimage, mem_sdiff, hxB, hnot, and_false, not_true_eq_false]
    · simp only [mem_inter_iff, mem_preimage, mem_sdiff, hxB, not_false_eq_true,
        and_true, show g' x = g x from hout hxB]

theorem exists_frontier_avoiding_family_deletion
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {D B : Set E} {Y F : Set X} {g : E → X}
    (hB : IsClosed B) (hBD : B ⊆ interior D)
    (hg : ContinuousOn g D) (hgY : MapsTo g D Y)
    (fill : C(B, Y))
    (hrim : ∀ (x : B), (x : E) ∈ frontier B → (fill x : X) = g x)
    (havoid : ∀ x : B, (fill x : X) ∉ F)
    {S : Set (Set E)} (hS : S.Finite) (hdisj : S.PairwiseDisjoint id)
    {s : Set E} (hs : s ∈ S) (hinter : B ∩ (⋃ t ∈ S, t) = s)
    (hcover : D ∩ g ⁻¹' F = ⋃ t ∈ S, t) :
    ∃ g' : E → X, ContinuousOn g' D ∧ MapsTo g' D Y ∧
      (∀ x : B, g' x = (fill x : X)) ∧ EqOn g' g Bᶜ ∧
      EqOn g' g (frontier D) ∧ D ∩ g' ⁻¹' F = ⋃ t ∈ S \ {s}, t ∧
      (S \ {s}).Finite ∧ (S \ {s}).PairwiseDisjoint id ∧
      (S \ {s}).ncard = S.ncard - 1 ∧ (S \ {s}).ncard < S.ncard := by
  obtain ⟨g', hg', hg'Y, hfill, hout, hfront, hpreimage⟩ :=
    exists_frontier_avoiding_replacement hB hBD hg hgY fill hrim havoid
  have hunion : (⋃ t ∈ S, t) \ B = ⋃ t ∈ S \ {s}, t := by
    ext x
    constructor
    · rintro ⟨hx, hxB⟩
      obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
      refine mem_iUnion₂.mpr ⟨t, ⟨ht, ?_⟩, hxt⟩
      intro hts
      have hxs : x ∈ s := hts ▸ hxt
      exact hxB (hinter.superset hxs).1
    · intro hx
      obtain ⟨t, ⟨ht, hts⟩, hxt⟩ := mem_iUnion₂.mp hx
      have hxS : x ∈ ⋃ t ∈ S, t := mem_iUnion₂.mpr ⟨t, ht, hxt⟩
      refine ⟨hxS, fun hxB => ?_⟩
      have hxs := hinter.subset ⟨hxB, hxS⟩
      exact Set.disjoint_left.mp (hdisj ht hs (fun heq => hts heq)) hxt hxs
  refine ⟨g', hg', hg'Y, hfill, hout, hfront, ?_, hS.sdiff, ?_,
    ncard_sdiff_singleton_of_mem hs, ncard_sdiff_singleton_lt_of_mem hs hS⟩
  · rw [hpreimage, hcover, hunion]
  · intro t ht u hu htu
    exact hdisj ht.1 hu.1 htu

end PoincareConjecture.M76
