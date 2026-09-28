import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFreshSphereIsotopy
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceInitialGraphIsotopy
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderMiddleCrossing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28

theorem exists_source_selected_crossing_height_accuracy :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A D0 D : ℝ}
        {E : SameTimeCounterexample.{u} epsilon C A D0 D}
        {S : CounterexampleNeckSegment E} (T : SourceTubeData S),
        epsilon ≤ epsilon0 → ∀ (f : UnitTwoSphere → ℝ),
          ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f →
          (∀ q, |f q| < epsilon⁻¹ / 32) →
          ∀ (N : EpsilonNeck (E.flow.metric E.time)), N.epsilon = epsilon →
            ∀ (hcenter : N.center ∈ (T.carrierOpen : Set _)),
              N.center ∉ (T.list.node 0).2.belowGraph_m28 f →
              Disjoint N.carrier
                (closure ((T.list.node ((T.list.nodes.length - 1 : ℕ) : ℤ)).2.carrier)) →
              Disjoint (range (fun q => (T.list.node 0).2.coordinate_map (q, f q)))
                N.central_sphere →
              ∀ (i : ℕ), i < T.list.nodes.length →
                Disjoint (T.list.node (i : ℤ)).2.carrier (T.list.node 0).2.carrier →
                Disjoint (T.list.node (i : ℤ)).2.carrier N.carrier →
                ∀ (b p : T.carrierOpen),
                  b.val ∈ range (fun q => (T.list.node 0).2.coordinate_map (q, f q)) →
                  p.val ∈ (T.list.node (i : ℤ)).2.carrier →
                  ∀ (K : Set T.carrierOpen), IsPreconnected K → b ∈ K →
                    (⟨N.center, hcenter⟩ : T.carrierOpen) ∈ K →
                    Disjoint (T.list.node (i : ℤ)).2.carrier
                      ((Subtype.val : T.carrierOpen → _) '' K) →
                    (∀ y ∈ N.central_sphere, y ∉ (T.list.node 0).2.belowGraph_m28 f) ∧
                    ∃ height : T.carrierOpen → ℝ, Continuous height ∧
                      (∀ y : T.carrierOpen, height y = 0 ↔ y.val ∈ N.central_sphere) ∧
                      height b < 0 ∧ 0 < height p := by
  obtain ⟨epsilon0, hpos, hsmall, hfresh⟩ :=
    exists_source_fresh_sphere_isotopy_accuracy.{u}
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro epsilon C A D0 D E S T hepsilon f hf hbound N heps hcenter hside
    hterminal hSC i hi hP0 hPN b p hb hp K hK hbK hqK hPK
  let P := (T.list.node (i : ℤ)).2
  let S0 := range (fun q => (T.list.node 0).2.coordinate_map (q, f q))
  let F := (T.list.node 0).2.belowGraph_m28 f
  have hactive : (i : ℤ) ∈ T.list.active := by
    change 0 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
    omega
  have hPT : P.carrier ⊆ (T.carrierOpen : Set _) := by
    intro x hx
    rw [T.carrier_eq_iUnion_nodes]
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr hi, hx⟩
  have hS : SmoothSphereIsotopicIn (T.carrierOpen : Set _) S0
      T.tube.cylinder.middleSphere := T.initial_graph_isotopic_middle f hf hbound
  have hC := hfresh T hepsilon f hbound N heps hcenter hside hterminal
  have hCU : N.central_sphere ⊆ (T.carrierOpen : Set _) := by
    obtain ⟨I, _, hI, hzero, _⟩ := hC
    rw [← hzero]
    exact (hI 0 (left_mem_Icc.mpr zero_le_one)).2
  have hH : SmoothSphereIsotopicIn (T.carrierOpen : Set _) P.central_sphere
      T.tube.cylinder.middleSphere := by
    change SmoothSphereIsotopicIn T.tube.carrier
      (T.list.node (i : ℤ)).2.central_sphere T.tube.cylinder.middleSphere
    have hiT : (i : ℤ) ∈ T.tube.chain.shape.active := by
      rw [T.tube_chain_readout.1]
      exact hactive
    have hh := T.tube.central_sphere_isotopy (i : ℤ) hiT
    simpa only [T.tube_chain_readout.2] using hh
  obtain ⟨hF, _, hcomponent⟩ := T.initial_graph_negative_region f hf.continuous hbound
  have hcomponent' : ∀ x ∈ F,
      connectedComponentIn ((T.carrierOpen : Set _) \ S0) x = F := hcomponent
  have hFU : F ⊆ (T.carrierOpen : Set _) \ S0 := by
    intro x hx
    have hh : connectedComponentIn ((T.carrierOpen : Set _) \ S0) x ⊆
        (T.carrierOpen : Set _) \ S0 := connectedComponentIn_subset _ _
    rw [hcomponent' x hx] at hh
    exact hh hx
  have hCsub : N.central_sphere ⊆ (T.carrierOpen : Set _) \ S0 := by
    intro y hy
    exact ⟨hCU hy, fun hyS => Set.disjoint_left.mp hSC hyS hy⟩
  have hsideAll : ∀ y ∈ N.central_sphere, y ∉ F := by
    intro y hy hyF
    have hh := N.isConnected_central_sphere.isPreconnected.subset_connectedComponentIn
      hy hCsub
    rw [hcomponent' y hyF] at hh
    exact hside (hh N.center_on_central_sphere)
  have heps0 : (T.list.node 0).2.epsilon = epsilon := by
    have hlen : 0 < T.list.nodes.length := List.length_pos_iff.mpr T.list.nonempty
    apply T.list.node_epsilon
    change 0 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
    constructor <;> omega
  have hA : 0 < epsilon⁻¹ := inv_pos.mpr (heps ▸ N.epsilon_pos)
  have hS0 : S0 ⊆ (T.list.node 0).2.carrier := by
    rintro _ ⟨z, rfl⟩
    apply (T.list.node 0).2.coordinate_map_mem_of_axial
    rw [heps0]
    have hh := abs_lt.mp (hbound z)
    constructor <;> linarith [hh.1, hh.2]
  have hCH : Disjoint N.central_sphere P.central_sphere := by
    apply Set.disjoint_left.mpr
    intro y hyN hyP
    exact Set.disjoint_left.mp hPN (P.central_sphere_subset hyP)
      (N.central_sphere_subset hyN)
  have hHoutside : ∀ y ∈ P.central_sphere, y ∉ S0 ∧ y ∉ F := by
    intro y hy
    have hnot : y ∉ (T.list.node 0).2.carrier :=
      fun hy0 => Set.disjoint_left.mp hP0 (P.central_sphere_subset hy) hy0
    exact ⟨fun hyS => hnot (hS0 hyS), fun hyF => hnot hyF.1⟩
  have hPrange : P.carrier ⊆ range (Subtype.val : T.carrierOpen → _) := by
    intro y hy
    exact ⟨⟨y, hPT hy⟩, rfl⟩
  have hPpre : IsPreconnected {y : T.carrierOpen | y.val ∈ P.carrier} :=
    P.isConnected_carrier.isPreconnected.preimage_of_isOpenMap Subtype.val_injective
      T.carrierOpen.isOpen.isOpenMap_subtype_val hPrange
  let q : T.carrierOpen := ⟨N.center, hcenter⟩
  let z : T.carrierOpen :=
    ⟨P.center, hPT (P.central_sphere_subset P.center_on_central_sphere)⟩
  refine ⟨hsideAll, ?_⟩
  exact T.tube.cylinder.exists_middle_sphere_crossing_height hS hC hH hF hFU hcomponent'
    hSC hCH hHoutside (b := b) (q := q) (z := z) (p := p)
    hb N.center_on_central_sphere hside P.center_on_central_sphere
    hK hbK hqK
    (fun y hy hyP => Set.disjoint_left.mp hPK (P.central_sphere_subset hyP)
      ⟨y, hy, rfl⟩)
    hPpre (P.central_sphere_subset P.center_on_central_sphere) hp
    (fun y hy hyN => Set.disjoint_left.mp hPN hy (N.central_sphere_subset hyN))

end PoincareConjecture.M28
