import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Complement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Regions










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}



theorem lower_carrier_subset_transported_core (C : CapCertificate g) (e : M ≃ₜ M)
    (hretain : C.closed_core ⊆ e '' C.closed_core)
    (hboundary : e '' C.boundary_sphere ⊆
      C.end_neck.region ((0.9 : ℝ) * C.epsilon⁻¹) C.epsilon⁻¹) :
    C.carrier \ C.end_neck.region (C.epsilon⁻¹ / 2) C.epsilon⁻¹ ⊆ e '' C.core := by
  let N := C.end_neck
  let R := C.epsilon⁻¹
  let L := N.region (-R) ((0.75 : ℝ) * R)
  let U := N.region ((0.75 : ℝ) * R) R
  let K := C.closed_core ∪ closure L
  have hR : 0 < R := inv_pos.mpr C.epsilon_pos
  have hL : IsConnected L := by
    apply N.isConnected_region
    · rw [C.end_neck_epsilon]
    · rw [C.end_neck_epsilon]; change (0.75 : ℝ) * R ≤ R; linarith
    · linarith
  have hnegative : N.region (-R) (-R / 2) ⊆ L := by
    rintro x ⟨hx, hxlo, hxhi⟩
    exact ⟨hx, hxlo, hxhi.trans (by linarith)⟩
  have hmeet : (C.closed_core ∩ closure L).Nonempty := by
    have hp : C.boundary_neck.center ∈ C.boundary_sphere :=
      C.boundary_eq_neck_sphere.symm ▸ C.boundary_neck.center_on_central_sphere
    exact ⟨C.boundary_neck.center, C.boundary_subset_closed_core hp,
      closure_mono hnegative (C.boundary_subset_negative_end_closure hp)⟩
  have hK : IsConnected K := C.isConnected_closed_core.union hmeet hL.closure
  have hupper : e '' C.boundary_sphere ⊆ U := by
    intro x hx
    have h := hboundary hx
    exact ⟨h.1, (by have := h.2.1; dsimp [R] at *; linarith), h.2.2⟩
  have havoid : K ⊆ (e '' C.boundary_sphere)ᶜ := by
    intro x hx hxb
    have hxU := hupper hxb
    rcases hx with hxC | hxL
    · exact Set.disjoint_left.mp C.disjoint_closed_core_end hxC hxU.1
    · obtain ⟨y, hyU, hyL⟩ := mem_closure_iff.mp hxL U (N.isOpen_region _ _) hxU
      exact (not_lt_of_ge hyU.2.1.le) hyL.2.2
  obtain ⟨p, hp⟩ := C.isConnected_core.nonempty
  have hpK : p ∈ K := Or.inl (C.core_subset_closed_core hp)
  obtain ⟨q, hq, hqp⟩ := hretain (C.core_subset_closed_core hp)
  have hqcore : q ∈ C.core := by
    rw [C.closed_core_eq_core_union_boundary] at hq
    rcases hq with hq | hq
    · exact hq
    · exact False.elim (havoid hpK ⟨q, hq, hqp⟩)
  have hqavoid : q ∈ C.boundary_sphereᶜ := Set.disjoint_left.mp C.disjoint_core_boundary hqcore
  have heq : e '' C.core = connectedComponentIn (e '' C.boundary_sphere)ᶜ p := by
    rw [C.core_eq_connectedComponentIn hqcore, e.image_connectedComponentIn hqavoid,
      e.image_compl, hqp]
  have hsub : K ⊆ e '' C.core := by
    rw [heq]
    exact hK.isPreconnected.subset_connectedComponentIn hpK havoid
  rintro x ⟨hx, hxout⟩
  apply hsub
  rw [C.carrier_eq_closed_core_union_end] at hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · right
    apply subset_closure
    have hdom := C.end_neck.coordinate_inverse_mem x hx
    have hhi : (N.coordinate_inverse x).2 ≤ R / 2 := by
      by_contra h
      apply hxout
      exact ⟨hx, lt_of_not_ge h, by simpa only [C.end_neck_epsilon] using hdom.2.2⟩
    refine ⟨hx, ?_, hhi.trans_lt (by linarith)⟩
    simpa only [C.end_neck_epsilon] using hdom.2.1

end PoincareConjecture.CapCertificate
