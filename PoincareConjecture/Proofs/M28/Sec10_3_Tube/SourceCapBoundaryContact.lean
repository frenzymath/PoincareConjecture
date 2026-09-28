import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeData
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCapWholePathBarrier
import PoincareConjecture.Proofs.M28.Mathlib.FrontierCrossing

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

theorem SourceTubeData.carrier_subset_neckCarrierUnion
    {epsilon C A D₀ D : ℝ}
    {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
    {S : CounterexampleNeckSegment E} (T : SourceTubeData S) :
    (T.carrierOpen : Set _) ⊆ S.neckCarrierUnion := by
  intro x hx
  change x ∈ T.tube.carrier at hx
  rw [T.carrier_eq] at hx
  change x ∈ ⋃ i : {i // i ∈ T.chain.shape.active}, (T.chain.neck i.1).carrier at hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
  obtain ⟨N, hN, hsame⟩ := T.chain.selected i.1 i.2
  rw [T.source_eq] at hN
  exact ⟨N, hN, hsame.2.2.2.1 ▸ hxi⟩

theorem exists_source_cap_boundary_contact_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
        ∀ (T : SourceTubeData S) (K : CapCertificate (E.flow.metric E.time)),
          K.epsilon = epsilon → K.cap_constant ≤ C →
          ∀ x ∈ (T.carrierOpen : Set _), x ∈ K.closed_core →
            ((T.carrierOpen : Set _) ∩ K.boundary_sphere).Nonempty ∧
              Disjoint K.closed_core (S.path '' Icc (0 : ℝ) 1) := by
  obtain ⟨epsilon₀, hpos, hsmall, hbarrier⟩ :=
    exists_source_cap_whole_path_avoidance_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A D₀ D E S hQ hε T K hepsilon hKC x hxT hxcore
  have hxK : x ∈ K.carrier := by
    rw [K.closed_core_eq_complement_end] at hxcore
    exact hxcore.1
  obtain ⟨_, _, _, havoid⟩ := hbarrier E S hQ hε K hepsilon hKC x
    (T.carrier_subset_neckCarrierUnion hxT) hxK
  have hlowT : S.path S.lower ∈ (T.carrierOpen : Set _) :=
    T.path_mem (left_mem_Icc.mpr S.lower_lt_upper.le)
  have hlowout : S.path S.lower ∉ K.closed_core := by
    intro hlow
    apply disjoint_left.mp havoid hlow
    exact ⟨S.lower, ⟨S.lower_pos.le, (S.lower_lt_upper.trans S.upper_lt_one).le⟩, rfl⟩
  have hT : IsPreconnected T.tube.carrier := by
    apply isPreconnected_iff_preconnectedSpace.mpr
    exact T.preconnected
  obtain ⟨z, hzT, hzfront⟩ :=
    hT.exists_mem_frontier_of_mem_of_notMem hxT hxcore hlowT hlowout
  refine ⟨⟨z, hzT, ?_⟩, havoid⟩
  simpa only [K.core_frontier_eq_boundary] using hzfront

end PoincareConjecture.M28
