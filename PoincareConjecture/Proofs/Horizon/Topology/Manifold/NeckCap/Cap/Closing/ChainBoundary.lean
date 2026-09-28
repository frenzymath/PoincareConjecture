import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Chain.Frontier
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.MixedSlice
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Connected
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Connected
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.SliceIsotopy

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem boundary_inter_nonempty_of_frontier_core_contact (C D : CapCertificate g)
    {U : Set M} (hU : IsPreconnected U) (hC : C.carrier ⊆ U)
    (hdis : Disjoint D.closed_core C.carrier)
    (hcontact : (frontier U ∩ D.core).Nonempty) :
    (D.boundary_sphere ∩ U).Nonempty := by
  obtain ⟨x, hxfront, hxD⟩ := hcontact
  obtain ⟨y, hyD, hyU⟩ := mem_closure_iff.mp (frontier_subset_closure hxfront)
    D.core D.isOpen_core hxD
  obtain ⟨c, hc⟩ := C.isConnected_carrier.nonempty
  have hout : (U \ D.closed_core).Nonempty :=
    ⟨c, hC hc, fun h => disjoint_left.mp hdis h hc⟩
  have hmeet := D.boundary_inter_nonempty_of_crossing hU ⟨y, hyU, hyD⟩ hout
  rwa [inter_comm] at hmeet

theorem outgoing_chain_boundary_inter_nonempty (C D : CapCertificate g)
    (H : ConnectedNeckCapCover g) (T : BalancedNeckChain g C.epsilon)
    (hT : C.IsOutgoingChain H T) (hdis : Disjoint D.closed_core C.carrier)
    (hcontact : (frontier (C.carrier ∪ (T.unionOpen : Set M)) ∩ D.core).Nonempty) :
    (D.boundary_sphere ∩ (C.carrier ∪ (T.unionOpen : Set M))).Nonempty := by
  have hcenter : C.end_neck.center ∈ C.end_neck.carrier :=
    C.end_neck.central_sphere_subset C.end_neck.center_on_central_sphere
  have hmeet : (C.carrier ∩ (T.unionOpen : Set M)).Nonempty :=
    ⟨C.end_neck.center, C.end_neck_subset hcenter,
      mem_iUnion.mpr ⟨⟨0, hT.zero_active⟩, hT.first_neck.symm ▸ hcenter⟩⟩
  exact C.boundary_inter_nonempty_of_frontier_core_contact D
    (C.isConnected_carrier.union hmeet T.isConnected_union).isPreconnected
    subset_union_left hdis hcontact

private theorem frontier_inter_boundary_of_mixed_open (D : CapCertificate g)
    {U : Set M} (hU : IsOpen U) (hmeet : (D.boundary_sphere ∩ U).Nonempty)
    (hmiss : ¬ D.boundary_sphere ⊆ U) :
    (frontier U ∩ D.boundary_sphere).Nonempty := by
  by_contra h
  have hconn : IsConnected D.boundary_sphere :=
    D.boundary_eq_neck_sphere.symm ▸ D.boundary_neck.isConnected_central_sphere
  let : ConnectedSpace D.boundary_sphere := isConnected_iff_connectedSpace.mp hconn
  have hdis : Disjoint (frontier U) D.boundary_sphere :=
    disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h)
  have hclopen := isClopen_preimage_val hU hdis
  obtain ⟨x, hxD, hxU⟩ := hmeet
  have hfull := hclopen.eq_univ ⟨⟨x, hxD⟩, hxU⟩
  apply hmiss
  intro y hy
  have hmem : (⟨y, hy⟩ : D.boundary_sphere) ∈ Subtype.val ⁻¹' U := by
    rw [hfull]
    exact mem_univ _
  exact hmem

theorem exists_outgoing_chain_mixed_boundary_shifted_slice_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 10000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), C.epsilon ≤ ε₀ → D.epsilon = C.epsilon →
        ∀ (H : ConnectedNeckCapCover g) (T : BalancedNeckChain g C.epsilon),
          C.IsOutgoingChain H T → ∀ b : ℤ, T.shape = .finite 0 b →
          (D.boundary_sphere ∩ (C.carrier ∪ (T.unionOpen : Set M))).Nonempty →
          (¬ D.boundary_sphere ⊆ C.carrier ∪ (T.unionOpen : Set M)) →
          ∃ z : M, z ∈ frontier (C.carrier ∪ (T.unionOpen : Set M)) ∧
            z ∈ frontier (T.neck b).carrier ∧ z ∈ D.boundary_sphere ∧
            ∃ a : ℝ, |a| = (0.05 : ℝ) * C.epsilon⁻¹ ∧
              a ∈ Ioo (-D.boundary_neck.epsilon⁻¹) D.boundary_neck.epsilon⁻¹ ∧
              range (fun q : UnitTwoSphere => D.boundary_neck.coordinate_map (q, a)) ⊆
                (T.neck b).region ((0.9 : ℝ) * C.epsilon⁻¹) C.epsilon⁻¹ ∧
              SmoothSphereIsotopicIn D.boundary_neck.carrier D.boundary_sphere
                (range (fun q : UnitTwoSphere => D.boundary_neck.coordinate_map (q, a))) := by
  obtain ⟨ε₁, hε₁, -, hfrontier⟩ := exists_outgoing_chain_frontier_positive_end_threshold.{u}
  obtain ⟨ε₂, hε₂, hsmall, hslice⟩ :=
    EpsilonNeck.exists_shifted_slice_subset_positive_end_of_frontier_contact.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_right _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hε hDC H T hT b hshape hmeet hmiss
  obtain ⟨z, hzfront, hzD⟩ := frontier_inter_boundary_of_mixed_open D
    (C.carrier_open.union T.unionOpen.isOpen) hmeet hmiss
  obtain ⟨j, hj, hnext, hzquarter⟩ := hfrontier C (hε.trans (min_le_left _ _)) H T hT z hzfront
  have hjb : j = b := by
    have hj' : 0 ≤ j ∧ j ≤ b := by simpa only [hshape, ChainShape.active, mem_Icc] using hj
    have hn' : ¬ (0 ≤ j + 1 ∧ j + 1 ≤ b) := by
      simpa only [hshape, ChainShape.active, mem_Icc] using hnext
    omega
  subst j
  have hbε : (T.neck b).epsilon = C.epsilon := T.epsilon_eq b hj
  have hzN : z ∈ frontier (T.neck b).carrier := by
    rw [(T.neck b).carrier_open.frontier_eq]
    refine ⟨closure_mono ((T.neck b).region_subset_carrier _ _) hzquarter, ?_⟩
    intro hz
    exact ((C.carrier_open.union T.unionOpen.isOpen).frontier_eq ▸ hzfront).2
      (Or.inr (mem_iUnion.mpr ⟨⟨b, hj⟩, hz⟩))
  obtain ⟨σ, hσ, hsub⟩ := hslice (T.neck b) D.boundary_neck
    (hbε.trans_le (hε.trans (min_le_right _ _)))
    (D.boundary_neck_epsilon.trans (hDC.trans hbε.symm)) z hzN
    (by simpa only [hbε] using hzquarter) (D.boundary_eq_neck_sphere ▸ hzD)
  let a := σ * (0.05 : ℝ) * C.epsilon⁻¹
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  have hshift : 0 < (0.05 : ℝ) * C.epsilon⁻¹ := mul_pos (by norm_num) hR
  have ha : a ∈ Ioo (-D.boundary_neck.epsilon⁻¹) D.boundary_neck.epsilon⁻¹ := by
    rw [D.boundary_neck_epsilon, hDC]
    dsimp only [a]
    rcases hσ with rfl | rfl <;> constructor <;> nlinarith
  refine ⟨z, hzfront, hzN, hzD, a, ?_, ha, ?_, ?_⟩
  · dsimp only [a]
    rcases hσ with rfl | rfl
    · simp only [one_mul, abs_of_pos hshift]
    · rw [neg_one_mul, neg_mul, abs_neg, abs_of_pos hshift]
  · simpa only [hbε] using hsub
  · have hzero : (0 : ℝ) ∈
        Ioo (-D.boundary_neck.epsilon⁻¹) D.boundary_neck.epsilon⁻¹ :=
      ⟨neg_neg_of_pos (inv_pos.mpr D.boundary_neck.epsilon_pos),
        inv_pos.mpr D.boundary_neck.epsilon_pos⟩
    have hisotopy := D.boundary_neck.coordinate_graphs_isotopic
      (fun _ => 0) (fun _ => a) contMDiff_const contMDiff_const (fun _ => hzero) (fun _ => ha)
    rwa [D.boundary_neck.centralSphere_range, ← D.boundary_eq_neck_sphere] at hisotopy

end PoincareConjecture.CapCertificate
