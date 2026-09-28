import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FiniteComponentExcision

set_option autoImplicit false
open Set

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X]

theorem sdiff_interior_eq_sdiff_of_disjoint_frontier {P D : Set X}
    (hD : IsClosed D) (hfront : Disjoint P (frontier D)) :
    P \ interior D = P \ D := by
  ext x
  constructor
  · rintro ⟨hxP, hxint⟩
    refine ⟨hxP, fun hxD => ?_⟩
    apply disjoint_left.mp hfront hxP
    rw [hD.frontier_eq]
    exact ⟨hxD, hxint⟩
  · exact fun hx => ⟨hx.1, fun hi => hx.2 (interior_subset hi)⟩

theorem connectedComponentIn_sdiff_of_disjoint_frontier {P D : Set X}
    (hD : IsClosed D) (hfront : Disjoint P (frontier D))
    {x : X} (hx : x ∈ P \ D) :
    connectedComponentIn (P \ D) x = connectedComponentIn P x := by
  have hsub := connectedComponentIn_subset P x
  have hxcomp : x ∈ connectedComponentIn P x := mem_connectedComponentIn hx.1
  have hout : Disjoint (connectedComponentIn P x) D := by
    rcases subset_interior_or_disjoint_of_disjoint_frontier
        isPreconnected_connectedComponentIn hD (hfront.mono_left hsub) with hin | hout
    · exact (hx.2 (interior_subset (hin hxcomp))).elim
    · exact hout
  apply Subset.antisymm (connectedComponentIn_mono x sdiff_subset)
  apply isPreconnected_connectedComponentIn.subset_connectedComponentIn hxcomp
  exact fun y hy => ⟨hsub hy, fun hyD => disjoint_left.mp hout hy hyD⟩

theorem exists_finite_component_decrease_of_sdiff
    {σ : Type*} [Fintype σ] (M : σ → Set X) {D : Set X}
    (hD : IsClosed D) (hconn : ∀ i, IsPreconnected (M i))
    (hfront : ∀ i, Disjoint (M i) (frontier D))
    (hcomp : ∀ i, ∀ x ∈ M i, connectedComponentIn (⋃ j, M j) x = M i)
    (hmeet : ((⋃ i, M i) ∩ D).Nonempty) :
    ∃ J : Finset σ,
      J.card < Fintype.card σ ∧
      (∀ i, i ∈ J ↔ Disjoint (M i) D) ∧
      (⋃ i, M i) \ D = ⋃ i ∈ J, M i ∧
      (∀ i ∈ J, ∀ x ∈ M i,
        connectedComponentIn ((⋃ j, M j) \ D) x = M i) ∧
      ∀ x ∈ (⋃ i, M i) \ D,
        connectedComponentIn ((⋃ i, M i) \ D) x = connectedComponentIn (⋃ i, M i) x := by
  have hfrontUnion : Disjoint (⋃ i, M i) (frontier D) := by
    apply disjoint_left.mpr
    intro x hx hxF
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact disjoint_left.mp (hfront i) hxi hxF
  have heq := sdiff_interior_eq_sdiff_of_disjoint_frontier hD hfrontUnion
  obtain ⟨J, hcard, hmem, hcover, hwhole⟩ :=
    exists_finite_component_excision M hD hconn hfront hcomp hmeet
  rw [heq] at hcover hwhole
  exact ⟨J, hcard, hmem, hcover, hwhole,
    fun _ hx => connectedComponentIn_sdiff_of_disjoint_frontier hD hfrontUnion hx⟩

theorem exists_marked_component_decrease_of_subset_interior
    {σ : Type*} [Fintype σ] [DecidableEq σ] (M : σ → Set X) {D : Set X}
    (hD : IsClosed D) (hconn : ∀ i, IsPreconnected (M i))
    (hfront : ∀ i, Disjoint (M i) (frontier D))
    (hcomp : ∀ i, ∀ x ∈ M i, connectedComponentIn (⋃ j, M j) x = M i)
    (marked : Finset σ) {i₀ : σ} (hi₀ : i₀ ∈ marked)
    (hne : (M i₀).Nonempty) (hinside : M i₀ ⊆ interior D) :
    ∃ J : Finset σ,
      J.card < Fintype.card σ ∧ (J ∩ marked).card < marked.card ∧
      (∀ i, i ∈ J ↔ Disjoint (M i) D) ∧
      (⋃ i, M i) \ D = ⋃ i ∈ J, M i ∧
      (∀ i ∈ J, ∀ x ∈ M i,
        connectedComponentIn ((⋃ j, M j) \ D) x = M i) ∧
      ∀ x ∈ (⋃ i, M i) \ D,
        connectedComponentIn ((⋃ i, M i) \ D) x = connectedComponentIn (⋃ i, M i) x := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨J, hcard, hmem, hcover, hwhole, hpoint⟩ :=
    exists_finite_component_decrease_of_sdiff M hD hconn hfront hcomp
      ⟨x, mem_iUnion.mpr ⟨i₀, hx⟩, interior_subset (hinside hx)⟩
  have hnot : i₀ ∉ J := fun hi =>
    disjoint_left.mp ((hmem i₀).mp hi) hx (interior_subset (hinside hx))
  have hproper : J ∩ marked ⊂ marked := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.inter_subset_right, fun heq =>
      hnot (Finset.mem_inter.mp (heq.symm ▸ hi₀)).1⟩
  exact ⟨J, hcard, Finset.card_lt_card hproper, hmem, hcover, hwhole, hpoint⟩

end Poincare.Topology
