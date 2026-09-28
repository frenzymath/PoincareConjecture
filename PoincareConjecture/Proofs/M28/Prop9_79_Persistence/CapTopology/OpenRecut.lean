import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.BoundaryCollar
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.PrecompactRecut










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}




theorem exists_boundary_collar_subset_recut (N : CapCertificate g) {q : ℝ}
    (hq : -N.epsilon⁻¹ < q) (hq' : q < N.epsilon⁻¹) :
    ∃ a b : ℝ, -N.epsilon⁻¹ < a ∧ a < 0 ∧ 0 < b ∧ b < N.epsilon⁻¹ ∧
      N.boundary_neck.region a b ⊆
        N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) q := by
  let T : Set M := N.end_neck.coordinate_map '' (univ ×ˢ Icc q q)
  have hTc : IsCompact T := N.end_neck.isCompact_coordinate_slab_intrinsic
    (by simpa only [N.end_neck_epsilon] using hq)
    (by simpa only [N.end_neck_epsilon] using hq')
  have hTE : T ⊆ N.end_neck.carrier := N.end_neck.coordinate_slab_subset_carrier_m28
    (by simpa only [N.end_neck_epsilon] using hq)
    (by simpa only [N.end_neck_epsilon] using hq')
  have hST : N.boundary_neck.central_sphere ⊆ Tᶜ := by
    intro x hxS hxT
    exact disjoint_left.mp N.boundary_disjoint_end
      (N.boundary_eq_neck_sphere.symm ▸ hxS) (hTE hxT)
  obtain ⟨a, b, ha, ha0, hb0, hb, hBT⟩ :=
    N.boundary_neck.exists_region_zero_subset hTc.isClosed.isOpen_compl hST
  rw [N.boundary_neck_epsilon] at ha hb
  have hconn := N.isPreconnected_boundary_region_inter_end ha.le ha0 hb0 hb.le
  have hf : ContinuousOn (fun x => (N.end_neck.coordinate_inverse x).2)
      (N.boundary_neck.region a b ∩ N.end_neck.carrier) :=
    (continuous_snd.comp_continuousOn
      N.end_neck.coordinate_inverse_smooth.continuousOn).mono inter_subset_right
  have hneq : ∀ x ∈ N.boundary_neck.region a b ∩ N.end_neck.carrier,
      (N.end_neck.coordinate_inverse x).2 ≠ q := by
    intro x hx heq
    apply hBT hx.1
    exact ⟨N.end_neck.coordinate_inverse x,
      ⟨mem_univ _, by rw [heq]; exact ⟨le_rfl, le_rfl⟩⟩,
      N.end_neck.coordinate_map_coordinate_inverse hx.2⟩
  have hzS : N.boundary_neck.center ∈ N.boundary_sphere :=
    N.boundary_eq_neck_sphere.symm ▸ N.boundary_neck.center_on_central_sphere
  have hzB := N.boundary_neck.central_sphere_subset_region ha0 hb0
    N.boundary_neck.center_on_central_sphere
  obtain ⟨y, hyB, hyE⟩ := mem_closure_iff.mp
    (N.boundary_subset_closure_inner_end hq hzS)
    (N.boundary_neck.region a b) (N.boundary_neck.region_open a b) hzB
  have hlt : ∀ x ∈ N.boundary_neck.region a b ∩ N.end_neck.carrier,
      (N.end_neck.coordinate_inverse x).2 < q :=
    fun _ hx => hconn.gt_of_ne hf hneq ⟨y, ⟨hyB, hyE.1⟩, hyE.2.2⟩ hx
  refine ⟨a, b, ha, ha0, hb0, hb, ?_⟩
  intro x hxB
  by_cases hxY : x ∈ N.closed_core
  · exact Or.inl hxY
  · have hxE : x ∈ N.end_neck.carrier := by
      by_contra hxE
      apply hxY
      rw [N.closed_core_eq_complement_end]
      exact ⟨N.boundary_neck_subset hxB.1, hxE⟩
    exact Or.inr ⟨hxE,
      by simpa only [N.end_neck_epsilon] using
        (N.end_neck.coordinate_inverse_mem x hxE).2.1,
      hlt x ⟨hxB, hxE⟩⟩



theorem isOpen_recut (N : CapCertificate g) {q : ℝ}
    (hq : -N.epsilon⁻¹ < q) (hq' : q < N.epsilon⁻¹) :
      IsOpen (N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) q) := by
  obtain ⟨a, b, _, ha0, hb0, _, hB⟩ := N.exists_boundary_collar_subset_recut hq hq'
  have hCoreOpen : IsOpen N.core := by
    rw [N.core_eq_interior_closed_core]
    exact isOpen_interior
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  rcases hx with hxY | hxE
  · by_cases hxC : x ∈ N.core
    · apply Filter.mem_of_superset (hCoreOpen.mem_nhds hxC)
      intro y hy
      exact Or.inl (interior_subset (N.core_eq_interior_closed_core ▸ hy))
    · have hxS : x ∈ N.boundary_sphere := by
        rw [← N.core_frontier_eq_boundary]
        apply (mem_frontier_iff_notMem_interior hxY).mpr
        simpa only [← N.core_eq_interior_closed_core] using hxC
      have hxB := N.boundary_neck.central_sphere_subset_region ha0 hb0
        (N.boundary_eq_neck_sphere ▸ hxS)
      exact Filter.mem_of_superset
        ((N.boundary_neck.region_open a b).mem_nhds hxB) hB
  · exact Filter.mem_of_superset
      ((N.end_neck.region_open (-N.epsilon⁻¹) q).mem_nhds hxE) subset_union_right




theorem open_precompact_recut (N : CapCertificate g) {q : ℝ}
    (hq : -N.epsilon⁻¹ < q) (hq' : q < N.epsilon⁻¹) :
    IsOpen (N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) q) ∧
      IsCompact (closure (N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) q)) ∧
      closure (N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) q) ⊆ N.carrier :=
  ⟨N.isOpen_recut hq hq', N.compact_closure_recut hq hq'⟩

end PoincareConjecture.CapCertificate
