import PoincareConjecture.Proofs.M28.Sec10_3_Tube.ChainEndBarrier
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalGraphRegions
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} {X : Set M}

theorem EpsilonTubeCertificate.closure_first_belowGraph
    (T : EpsilonTubeCertificate g X) {i : ℤ} (hi : IsLeast T.chain.shape.active i)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hdom : ∀ q, f q ∈ Ioo (-(T.chain.neck i).epsilon⁻¹) (T.chain.neck i).epsilon⁻¹)
    {c : ℝ} (hc : c < T.epsilon⁻¹) (hbound : ∀ q, f q ≤ c) :
    closure ((T.chain.neck i).belowGraph_m28 f) ∩ T.carrier =
      (T.chain.neck i).belowGraph_m28 f ∪
        range (fun q => (T.chain.neck i).coordinate_map (q, f q)) := by
  let N := T.chain.neck i
  have heps : N.epsilon = T.epsilon := T.chain.epsilon_eq i hi.1
  have hNT : N.carrier ⊆ T.carrier := by
    intro x hx
    rw [T.carrier_eq_chain_union]
    exact mem_iUnion.mpr ⟨⟨i, hi.1⟩, hx⟩
  have hregion : N.belowGraph_m28 f ⊆ N.region (-T.epsilon⁻¹) c := by
    intro x hx
    have hlo := (N.coordinate_inverse_mem x hx.1).2.1
    rw [heps] at hlo
    exact ⟨hx.1, hlo, hx.2.trans_le (hbound _)⟩
  ext x
  constructor
  · intro hx
    have hxtube : x ∈ ⋃ j : {j // j ∈ T.chain.shape.active},
        (T.chain.neck j.1).carrier := T.carrier_eq_chain_union ▸ hx.2
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxtube
    have hxN : x ∈ N.carrier :=
      T.chain.closure_region_inter_later_carrier_subset hi.1 j.2 (hi.2 j.2) hc
        ⟨closure_mono hregion hx.1, hxj⟩
    rcases lt_trichotomy (N.coordinate_inverse x).2 (f (N.coordinate_inverse x).1) with
      hneg | heq | hpos
    · exact Or.inl ⟨hxN, hneg⟩
    · exact Or.inr ((N.mem_coordinate_graph_iff_m28 f hdom).mpr ⟨hxN, heq⟩)
    · obtain ⟨y, hypos, hyneg⟩ := mem_closure_iff.mp hx.1
        (N.aboveGraph_m28 f) (N.isOpen_aboveGraph_m28 f hf) ⟨hxN, hpos⟩
      exact False.elim (not_lt_of_ge hyneg.2.le hypos.2)
  · rintro (hx | hx)
    · exact ⟨subset_closure hx, hNT hx.1⟩
    · obtain ⟨q, rfl⟩ := hx
      exact ⟨N.coordinate_graph_mem_closure_belowGraph_m28 f hdom q,
        hNT (N.coordinate_map_mem_of_axial _ (hdom q))⟩

theorem EpsilonTubeCertificate.frontier_first_belowGraph
    (T : EpsilonTubeCertificate g X) {i : ℤ} (hi : IsLeast T.chain.shape.active i)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hdom : ∀ q, f q ∈ Ioo (-(T.chain.neck i).epsilon⁻¹) (T.chain.neck i).epsilon⁻¹)
    {c : ℝ} (hc : c < T.epsilon⁻¹) (hbound : ∀ q, f q ≤ c) :
    frontier ((T.chain.neck i).belowGraph_m28 f) ∩ T.carrier =
      range (fun q => (T.chain.neck i).coordinate_map (q, f q)) := by
  let N := T.chain.neck i
  have hopen := N.isOpen_belowGraph_m28 f hf
  have hclosure := T.closure_first_belowGraph hi f hf hdom hc hbound
  ext x
  constructor
  · intro hx
    have hcl : x ∈ closure (N.belowGraph_m28 f) ∩ T.carrier :=
      ⟨frontier_subset_closure hx.1, hx.2⟩
    have hnot : x ∉ N.belowGraph_m28 f := (hopen.frontier_eq ▸ hx.1).2
    exact (hclosure ▸ hcl).resolve_left hnot
  · intro hx
    have hcl : x ∈ closure (N.belowGraph_m28 f) ∩ T.carrier :=
      hclosure.symm ▸ Or.inr hx
    have hnot : x ∉ N.belowGraph_m28 f := by
      intro hn
      have heq := ((N.mem_coordinate_graph_iff_m28 f hdom).mp hx).2
      exact (ne_of_lt hn.2) heq
    exact ⟨hopen.frontier_eq.symm ▸ And.intro hcl.1 hnot, hcl.2⟩

theorem EpsilonTubeCertificate.isClopen_first_belowGraph_complement
    (T : EpsilonTubeCertificate g X) {i : ℤ} (hi : IsLeast T.chain.shape.active i)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hdom : ∀ q, f q ∈ Ioo (-(T.chain.neck i).epsilon⁻¹) (T.chain.neck i).epsilon⁻¹)
    {c : ℝ} (hc : c < T.epsilon⁻¹) (hbound : ∀ q, f q ≤ c) :
    IsClopen ((Subtype.val :
      ↥(T.carrier \ range (fun q => (T.chain.neck i).coordinate_map (q, f q))) → M) ⁻¹'
        (T.chain.neck i).belowGraph_m28 f) := by
  let N := T.chain.neck i
  refine ⟨isClosed_of_closure_subset ?_,
    (N.isOpen_belowGraph_m28 f hf).preimage continuous_subtype_val⟩
  intro x hx
  have hxcl := continuous_subtype_val.closure_preimage_subset (N.belowGraph_m28 f) hx
  have hcl : (x : M) ∈ closure (N.belowGraph_m28 f) ∩ T.carrier := ⟨hxcl, x.property.1⟩
  have hmem := (T.closure_first_belowGraph hi f hf hdom hc hbound) ▸ hcl
  exact hmem.resolve_right x.property.2

theorem EpsilonTubeCertificate.connectedComponentIn_first_belowGraph
    (T : EpsilonTubeCertificate g X) {i : ℤ} (hi : IsLeast T.chain.shape.active i)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hdom : ∀ q, f q ∈ Ioo (-(T.chain.neck i).epsilon⁻¹) (T.chain.neck i).epsilon⁻¹)
    {c : ℝ} (hc : c < T.epsilon⁻¹) (hbound : ∀ q, f q ≤ c)
    {x : M} (hx : x ∈ (T.chain.neck i).belowGraph_m28 f) :
    connectedComponentIn
      (T.carrier \ range (fun q => (T.chain.neck i).coordinate_map (q, f q))) x =
        (T.chain.neck i).belowGraph_m28 f := by
  let N := T.chain.neck i
  let U := T.carrier \ range (fun q => N.coordinate_map (q, f q))
  have hFU : N.belowGraph_m28 f ⊆ U := by
    intro y hy
    have hcl : y ∈ closure (N.belowGraph_m28 f) ∩ T.carrier :=
      (T.closure_first_belowGraph hi f hf hdom hc hbound).symm ▸ Or.inl hy
    refine ⟨hcl.2, ?_⟩
    intro hgraph
    exact (ne_of_lt hy.2) ((N.mem_coordinate_graph_iff_m28 f hdom).mp hgraph).2
  have hclopen := T.isClopen_first_belowGraph_complement hi f hf hdom hc hbound
  apply Subset.antisymm
  · rw [connectedComponentIn_eq_image (hFU hx)]
    rintro y ⟨z, hz, rfl⟩
    exact hclopen.connectedComponent_subset hx hz
  · exact (N.isConnected_belowGraph_m28 f hf hdom).isPreconnected.subset_connectedComponentIn hx hFU

end PoincareConjecture
