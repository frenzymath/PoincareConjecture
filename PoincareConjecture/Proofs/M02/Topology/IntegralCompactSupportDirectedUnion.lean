import PoincareConjecture.Proofs.M02.Topology.IntegralDirectedUnionRepresentatives
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportRange



set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]

private theorem directedUnionOpenEmbedding
    {X : Type u} [TopologicalSpace X]
    {I : Type v} (U : I → Set X) (i : I)
    (hU : ∀ j, IsOpen (U j)) :
    _root_.Topology.IsOpenEmbedding (integralDirectedUnionInclusion U i) := by
  let B : Set X := ⋃ j, U j
  have hB : IsOpen B := isOpen_iUnion hU
  apply _root_.Topology.IsOpenEmbedding.of_comp
    (integralDirectedUnionInclusion U i)
    (hB.isOpenEmbedding_subtypeVal)
  change _root_.Topology.IsOpenEmbedding (integralOpenSubtypeVal (U i))
  exact (hU i).isOpenEmbedding_subtypeVal

private theorem directedUnionStage_subset_range
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {I : Type v} (U : I → Set X) (i : I)
    {K : Set (⋃ j, U j)}
    (hK : K ⊆ (Subtype.val : (⋃ j, U j) → X) ⁻¹' U i) :
    K ⊆ Set.range (integralDirectedUnionInclusion U i) := by
  intro x hx
  exact ⟨⟨x.1, hK hx⟩, rfl⟩

theorem exists_integralCompactSupportCohomology_directed_union_stage
    {I : Type v} [Nonempty I] (U : I → Set X)
    (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (fun A B : Set X => A ⊆ B) U)
    (q : Nat) (a : integralCompactSupportCohomology (⋃ i, U i) q) :
    ∃ i, ∃ b : integralCompactSupportCohomology (U i) q,
      (integralCompactSupportCohomologyOpenMap
        (integralDirectedUnionInclusion U i)
        (directedUnionOpenEmbedding U i hU) q) b = a := by
  let B : Set X := ⋃ i, U i
  obtain ⟨K, c, hc⟩ := exists_integralCompactSupportCohomology_representative q a
  let W : I → Set B := fun i => (Subtype.val : B → X) ⁻¹' U i
  have hW : ∀ i, IsOpen (W i) := by
    intro i
    exact (hU i).preimage continuous_subtype_val
  have hWcover : (K : Set B) ⊆ ⋃ i, W i := by
    intro x hx
    have hx' : (x : X) ∈ ⋃ i, U i := x.property
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx'
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨i, hKi⟩ := K.isCompact.elim_directed_cover W hW hWcover (by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, (fun x hx => hik hx), (fun x hx => hjk hx)⟩)
  have hKr : (K : Set B) ⊆
      Set.range (fun x => integralDirectedUnionInclusion U i x) :=
    directedUnionStage_subset_range U i hKi
  obtain ⟨S, d, hd⟩ :=
    integralCompactSupportCohomologyClass_of_compact_range
      (integralDirectedUnionInclusion U i) (directedUnionOpenEmbedding U i hU)
      K hKr q c
  refine ⟨i, integralCompactSupportCohomologyClass S q d, ?_⟩
  rw [← hc]
  exact hd

end PoincareConjecture.Proofs.M02.Topology
