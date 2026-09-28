import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeVolume
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckPairCoreCapture










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.SourceTubeData

variable {epsilon C A D₀ D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
  {S : CounterexampleNeckSegment E}



def coreUnion (T : SourceTubeData S) (theta : ℝ) : Set (E.flow.slice E.time).carrier :=
  ⋃ i ∈ Finset.range T.list.nodes.length,
    (T.list.node (i : ℤ)).2.coordinate_map ''
      (univ ×ˢ Icc (-(theta * epsilon⁻¹)) (theta * epsilon⁻¹))



theorem coreUnion_compact_subset (T : SourceTubeData S) {theta : ℝ}
    (htheta : theta < 1) :
    IsCompact (T.coreUnion theta) ∧ T.coreUnion theta ⊆ T.carrierOpen := by
  have hA : 0 < epsilon⁻¹ := inv_pos.mpr (S.cover_epsilon ▸ S.cover.epsilon_pos)
  have hwidth : theta * epsilon⁻¹ < epsilon⁻¹ := by nlinarith only [htheta, hA]
  have hactive (i : ℕ) (hi : i ∈ Finset.range T.list.nodes.length) :
      (i : ℤ) ∈ T.list.active := by
    change 0 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
    have := Finset.mem_range.mp hi
    omega
  constructor
  · apply (Finset.range T.list.nodes.length).isCompact_biUnion
    intro i hi
    apply (T.list.node (i : ℤ)).2.isCompact_coordinate_slab_intrinsic
    · rw [T.list.node_epsilon (hactive i hi)]
      linarith only [hwidth]
    · rw [T.list.node_epsilon (hactive i hi)]
      exact hwidth
  · intro x hx
    obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
    have hxN : x ∈ (T.list.node (i : ℤ)).2.carrier := by
      apply (T.list.node (i : ℤ)).2.coordinate_slab_subset_carrier_m28 _ _ hx
      · rw [T.list.node_epsilon (hactive i hi)]
        linarith only [hwidth]
      · rw [T.list.node_epsilon (hactive i hi)]
        exact hwidth
    rw [T.carrier_eq_iUnion_nodes]
    exact mem_iUnion₂.mpr ⟨i, hi, hxN⟩





theorem subset_coreUnion_end_tails (T : SourceTubeData S)
    (hepsilon : epsilon ≤ (1 / 1000 : ℝ)) {theta : ℝ}
    (htheta : (3 / 4 : ℝ) ≤ theta) :
    (T.carrierOpen : Set _) ⊆ T.coreUnion theta ∪
      (T.list.node 0).2.region (-epsilon⁻¹) (-(theta * epsilon⁻¹)) ∪
      (T.list.node ((T.list.nodes.length - 1 : ℕ) : ℤ)).2.region
        (theta * epsilon⁻¹) epsilon⁻¹ := by
  have hA : 0 < epsilon⁻¹ := inv_pos.mpr (S.cover_epsilon ▸ S.cover.epsilon_pos)
  have hwidth : 3 * epsilon⁻¹ / 4 ≤ theta * epsilon⁻¹ := by
    nlinarith only [mul_le_mul_of_nonneg_right htheta hA.le]
  have hactive (i : ℕ) (hi : i < T.list.nodes.length) :
      (i : ℤ) ∈ T.list.active := by
    change 0 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
    omega
  have hcore (i : ℕ) (hi : i < T.list.nodes.length)
      {x : (E.flow.slice E.time).carrier} (hx : x ∈ (T.list.node (i : ℤ)).2.carrier)
      (hlo : -(theta * epsilon⁻¹) ≤ ((T.list.node (i : ℤ)).2.coordinate_inverse x).2)
      (hhi : ((T.list.node (i : ℤ)).2.coordinate_inverse x).2 ≤ theta * epsilon⁻¹) :
      x ∈ T.coreUnion theta :=
    mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr hi,
      (T.list.node (i : ℤ)).2.coordinate_inverse x, ⟨mem_univ _, hlo, hhi⟩,
      (T.list.node (i : ℤ)).2.coordinate_map_coordinate_inverse hx⟩
  intro x hx
  rw [T.carrier_eq_iUnion_nodes] at hx
  obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
  have hi' : i < T.list.nodes.length := Finset.mem_range.mp hi
  have heps := T.list.node_epsilon (hactive i hi')
  have hcoord := ((T.list.node (i : ℤ)).2.coordinate_inverse_mem x hx).2
  by_cases hlo : -(theta * epsilon⁻¹) ≤
      ((T.list.node (i : ℤ)).2.coordinate_inverse x).2
  · by_cases hhi : ((T.list.node (i : ℤ)).2.coordinate_inverse x).2 ≤ theta * epsilon⁻¹
    · exact Or.inl (Or.inl (hcore i hi' hx hlo hhi))
    · have hhigh := lt_of_not_ge hhi
      by_cases hlast : i = T.list.nodes.length - 1
      · apply Or.inr
        subst i
        exact ⟨hx, hhigh, by simpa only [heps] using hcoord.2⟩
      · have hnext : i + 1 < T.list.nodes.length := by omega
        have hindex : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by omega
        obtain ⟨_, _, Hedge, _⟩ := T.list.node_edge (hactive i hi')
          (by simpa only [hindex] using hactive (i + 1) hnext)
        have hsmall : (T.list.node (i : ℤ)).2.epsilon ≤ 1 / 1000 := by
          rw [heps]
          exact hepsilon
        have htail : x ∈ (T.list.node (i : ℤ)).2.region
            ((T.list.node (i : ℤ)).2.epsilon⁻¹ / 2)
            (T.list.node (i : ℤ)).2.epsilon⁻¹ := by
          refine ⟨hx, ?_, hcoord.2⟩
          rw [heps]
          linarith only [hhigh, hwidth, hA]
        have hcapture := Hedge.forward_core hsmall htail
        rw [← hindex] at hcapture
        have hepsNext := T.list.node_epsilon (hactive (i + 1) hnext)
        rw [hepsNext] at hcapture
        exact Or.inl (Or.inl (hcore (i + 1) hnext hcapture.1
          (by linarith only [hcapture.2.1, hwidth])
          (by linarith only [hcapture.2.2, hwidth])))
  · have hlow := lt_of_not_ge hlo
    by_cases hzero : i = 0
    · apply Or.inl ∘ Or.inr
      subst i
      have heps0 : (T.list.node 0).2.epsilon = epsilon := by
        simpa only [Nat.cast_zero] using heps
      exact ⟨hx, by simpa only [Nat.cast_zero, heps0] using hcoord.1, hlow⟩
    · have hprev : i - 1 < T.list.nodes.length := by omega
      have hindex : ((i - 1 : ℕ) : ℤ) + 1 = (i : ℤ) := by omega
      obtain ⟨_, _, Hedge, _⟩ := T.list.node_edge (hactive (i - 1) hprev)
        (by simpa only [hindex] using hactive i hi')
      rw [hindex] at Hedge
      have htail : x ∈ (T.list.node (i : ℤ)).2.region
          (-(T.list.node (i : ℤ)).2.epsilon⁻¹)
          (-(T.list.node (i : ℤ)).2.epsilon⁻¹ / 2) := by
        refine ⟨hx, hcoord.1, ?_⟩
        rw [heps]
        linarith only [hlow, hwidth, hA]
      have hcapture := Hedge.reciprocal_core htail
      rw [T.list.node_epsilon (hactive (i - 1) hprev)] at hcapture
      exact Or.inl (Or.inl (hcore (i - 1) hprev hcapture.1
        (by linarith only [hcapture.2.1, hwidth])
        (by linarith only [hcapture.2.2, hwidth])))




theorem frontier_subset_end_tail_closures (T : SourceTubeData S)
    (hepsilon : epsilon ≤ (1 / 1000 : ℝ)) {theta : ℝ}
    (htheta : (3 / 4 : ℝ) ≤ theta) (htheta' : theta < 1) :
    frontier (T.carrierOpen : Set _) ⊆
      closure ((T.list.node 0).2.region (-epsilon⁻¹) (-(theta * epsilon⁻¹))) ∪
      closure ((T.list.node ((T.list.nodes.length - 1 : ℕ) : ℤ)).2.region
        (theta * epsilon⁻¹) epsilon⁻¹) := by
  obtain ⟨hcompact, hsubset⟩ := T.coreUnion_compact_subset htheta'
  intro x hx
  have hclosure := closure_mono (T.subset_coreUnion_end_tails hepsilon htheta) hx.1
  rw [closure_union, closure_union, hcompact.isClosed.closure_eq] at hclosure
  have hout : x ∉ (T.carrierOpen : Set _) := by
    simpa only [T.carrierOpen.isOpen.interior_eq] using hx.2
  rcases hclosure with (hcore | hleft) | hright
  · exact False.elim (hout (hsubset hcore))
  · exact Or.inl hleft
  · exact Or.inr hright

end PoincareConjecture.M28.SourceTubeData
