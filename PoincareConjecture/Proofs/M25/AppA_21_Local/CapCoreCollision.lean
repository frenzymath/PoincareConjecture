import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCommonSphereProducer
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCommonSphereComponent
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCoreContact
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapEndSeparation
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem CapCertificate.exists_two_cap_component_or_disjoint_cores :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (C0 C1 : CapCertificate g),
      C0.epsilon ≤ epsilon0 → C1.epsilon = C0.epsilon →
      (¬ (C0.carrier \ C0.end_neck.region
        (C0.epsilon⁻¹ / 2) C0.epsilon⁻¹ ⊆ C1.core)) →
      ∀ (V : Set M), IsPreconnected V → C0.carrier ⊆ V →
      ∀ y : M, y ∈ C1.core → y ∉ V →
      let W := V ∪ C1.carrier
      (W = C0.carrier ∪ C1.carrier ∧ IsCompact W ∧ IsClopen W ∧
        IsConnected W ∧ ∃ z : M, W = connectedComponent z) ∨
      Disjoint C0.closed_core C1.closed_core := by
  obtain ⟨epsilon0, hpos, hcap, hgraph⟩ :=
    CapCertificate.exists_common_outward_graph_of_finite_core_frontier.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g C0 C1 hsmall hepsilon hno V hV hC0V y hy hyV
  classical
  by_cases hdisjoint : Disjoint C0.closed_core C1.closed_core
  · exact Or.inr hdisjoint
  apply Or.inl
  obtain ⟨p, hp0, hp1⟩ := Set.not_disjoint_iff.mp hdisjoint
  have hpC : p ∈ C0.carrier := by
    rw [C0.closed_core_eq_complement_end] at hp0
    exact hp0.1
  have hpcl : p ∈ closure C1.core := C1.m25_closure_core_eq_closed_core.symm ▸ hp1
  obtain ⟨x, hxC, hxcore⟩ := mem_closure_iff.mp hpcl C0.carrier C0.carrier_open hpC
  have hL : 0 < C0.epsilon⁻¹ := inv_pos.mpr C0.epsilon_pos
  have hL1 : 0 < C1.epsilon⁻¹ := inv_pos.mpr C1.epsilon_pos
  obtain ⟨R, hR, heR, _, _, hRcore, _⟩ := C1.exists_outward_boundary_neck
  obtain ⟨hcoreA, _⟩ := C1.outward_graph_compact_side R hR hRcore
    (fun _ => 0) continuous_const (fun _ => ⟨le_rfl, hL1⟩)
  have himagecore : R.coordinate_map ''
      {z : RoundCylinderSpace | -C1.epsilon⁻¹ < z.2 ∧ z.2 < 0} ⊆ C1.core := by
    rintro w ⟨z, hz, rfl⟩
    have hzs : z ∈ R.cylinderDomain := by
      refine ⟨mem_univ _, ?_⟩
      simpa only [heR] using
        (show z.2 ∈ Ioo (-C1.epsilon⁻¹) C1.epsilon⁻¹ from
          ⟨hz.1, hz.2.trans hL1⟩)
    have hxreg : R.coordinate_map z ∈ R.region (-C1.epsilon⁻¹) 0 := by
      refine ⟨R.coordinate_map_mem hzs, ?_⟩
      rw [R.coordinate_inverse_coordinate_map hzs]
      exact hz
    exact (hRcore.symm ▸ hxreg).2
  have hcoreconn : IsPreconnected C1.core := by
    rw [union_eq_left.mpr himagecore] at hcoreA
    rw [hcoreA]
    exact isPreconnected_connectedComponentIn
  have hfrontmeet : (C1.core ∩ frontier C0.carrier).Nonempty := by
    by_contra hempty
    have hsub : C1.core ⊆ C0.carrier := by
      apply hcoreconn.subset_of_closure_inter_subset C0.carrier_open
        ⟨x, hxcore, hxC⟩
      intro z hz
      by_contra hzout
      apply hempty
      refine ⟨z, hz.2, ?_⟩
      rw [C0.carrier_open.frontier_eq]
      exact ⟨hz.1, hzout⟩
    exact hyV (hC0V (hsub hy))
  obtain ⟨y0, hy0, hy0front⟩ := hfrontmeet
  have hy0out : y0 ∉ C0.carrier := by
    rw [C0.carrier_open.frontier_eq] at hy0front
    exact hy0front.2
  have hy0cl : y0 ∈ closure C0.carrier := frontier_subset_closure hy0front
  have hy0tail : y0 ∈ closure (C0.end_neck.region 0 C0.epsilon⁻¹) :=
    (C0.end_neck_lower_cut_topology
      (show (0 : ℝ) ∈ Ioo (-C0.epsilon⁻¹) C0.epsilon⁻¹ from
        ⟨neg_lt_zero.mpr hL, hL⟩)).2.2.2.2.2.2 hy0front
  have hmeet : (C0.carrier ∩ C1.boundary_sphere).Nonempty := by
    by_contra hnone
    have havoid : Disjoint C0.carrier C1.boundary_sphere := by
      apply disjoint_left.mpr
      intro z hzC hzS
      exact hnone ⟨z, hzC, hzS⟩
    have hsub := C1.subset_core_of_avoids_boundary
      C0.m25_isConnected_carrier.isPreconnected havoid ⟨y0, hy0cl, hy0⟩
    exact hno (fun z hz => hsub hz.1)
  have hsingle {i : ℤ} (hi : i ∈ (ChainShape.finite 0 0).active)
      (hi1 : i + 1 ∈ (ChainShape.finite 0 0).active) : False := by
    change 0 ≤ i ∧ i ≤ 0 at hi
    change 0 ≤ i + 1 ∧ i + 1 ≤ 0 at hi1
    omega
  let D : BalancedNeckChain g C0.epsilon := {
    shape := .finite 0 0
    neck := fun _ => C0.end_neck
    source_necks := {C0.end_neck}
    selected := by
      intro _ _
      refine ⟨C0.end_neck, mem_singleton _, rfl, rfl, rfl, rfl, rfl,
        1, Or.inl rfl, ?_⟩
      intro z _
      simp only [one_mul]
    active_nonempty := ⟨0, le_rfl, le_rfl⟩
    epsilon_eq := fun _ _ => C0.end_neck_epsilon
    centers_distinct := by
      intro i hi j hj hij
      change 0 ≤ i ∧ i ≤ 0 at hi
      change 0 ≤ j ∧ j ≤ 0 at hj
      omega
    adjacent_overlap := fun _ hi hi1 => (hsingle hi hi1).elim
    overlap_contains_quarters := fun _ hi hi1 => (hsingle hi hi1).elim
    overlap_within_three_quarters := fun _ hi hi1 => (hsingle hi hi1).elim
    later_disjoint_negative_end := by
      intro i hi j hj hij
      change 0 ≤ i ∧ i ≤ 0 at hi
      change 0 ≤ j ∧ j ≤ 0 at hj
      omega
    balanced_center_distance := fun _ hi hi1 => (hsingle hi hi1).elim }
  let Vsingle : TopologicalSpace.Opens M :=
    ⟨C0.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier),
      C0.carrier_open.union
        (isOpen_iUnion fun i => isOpen_iUnion fun _ => (D.neck i).carrier_open)⟩
  have hVsingle : (Vsingle : Set M) = C0.carrier := by
    apply union_eq_left.mpr
    intro z hz
    obtain ⟨i, _, hi⟩ := mem_iUnion₂.mp hz
    exact C0.end_neck_subset hi
  have hy0single : y0 ∉ (Vsingle : Set M) := by simpa only [hVsingle] using hy0out
  have hmeetsingle : ((Vsingle : Set M) ∩ C1.boundary_sphere).Nonempty := by
    simpa only [hVsingle] using hmeet
  obtain ⟨d, _, _, hy0closure, R1, f, N, s, hR1, _, _, _, hR1core, _,
      hf, hfdom, hs, hlevel, hSV, _⟩ :=
    hgraph C0 C1 D hsmall hepsilon rfl rfl
      (fun _ _ => C0.end_neck_isSeparating)
      (by
        intro i hi hi0
        change 0 ≤ i ∧ i ≤ 0 at hi
        omega)
      (fun _ hi hi1 => (hsingle hi hi1).elim)
      hno y0 hy0 hy0tail hy0single hmeetsingle
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcompact, hclopen, hconnected, hcomponent⟩ :=
    C0.compact_union_component_of_common_outward_graph C1 Vsingle d.toHomeomorph
      R1 hR1 hR1core f hf.continuous hfdom N s hs hlevel hSV
      y0 hy0 hy0closure hy0single
  rw [hVsingle] at hcompact hclopen hconnected hcomponent
  have hVsub : V ⊆ C0.carrier ∪ C1.carrier := by
    obtain ⟨z, hz⟩ := C0.core_nonempty
    have hzC := C0.m25_core_subset_carrier hz
    exact hV.subset_isClopen hclopen ⟨z, hC0V hzC, Or.inl hzC⟩
  have hWeq : V ∪ C1.carrier = C0.carrier ∪ C1.carrier := by
    apply Subset.antisymm
    · exact union_subset hVsub subset_union_right
    · exact union_subset_union_left _ hC0V
  change V ∪ C1.carrier = C0.carrier ∪ C1.carrier ∧
    IsCompact (V ∪ C1.carrier) ∧ IsClopen (V ∪ C1.carrier) ∧
    IsConnected (V ∪ C1.carrier) ∧
    ∃ z : M, V ∪ C1.carrier = connectedComponent z
  rw [hWeq]
  exact ⟨rfl, hcompact, hclopen, hconnected, _, hcomponent⟩

end PoincareConjecture
