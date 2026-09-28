import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Transport











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}



theorem closed_core_eq_or_compact_component_of_aligned_boundaries
    (C D : CapCertificate g) (e f : M ≃ₜ M)
    (hecarrier : e '' C.carrier = C.carrier)
    (hfcarrier : f '' D.carrier = D.carrier)
    (hboundary : e '' C.boundary_sphere = f '' D.boundary_sphere) :
    e '' C.closed_core = f '' D.closed_core ∨
      (C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center ∧
        IsCompact (C.carrier ∪ D.carrier)) := by
  let h := f.trans e.symm
  have hback (S : Set M) : e '' (h '' S) = f '' S := by
    simp only [image_image, h, Homeomorph.trans_apply, e.apply_symm_apply]
  have hboundary' : h '' D.boundary_sphere = C.boundary_sphere := by
    apply e.injective.image_injective
    rw [hback]
    exact hboundary.symm
  have hcenter : e C.boundary_neck.center ∈ C.carrier := by
    rw [← hecarrier]
    apply mem_image_of_mem
    apply C.boundary_subset
    rw [C.boundary_eq_neck_sphere]
    exact C.boundary_neck.center_on_central_sphere
  have hcomponent : e '' connectedComponent C.boundary_neck.center =
      connectedComponent C.boundary_neck.center := by
    have hi := e.image_connectedComponentIn (s := univ)
      (x := C.boundary_neck.center) (mem_univ _)
    simp only [image_univ, e.surjective.range_eq, connectedComponentIn_univ] at hi
    exact hi.trans (connectedComponent_eq (C.carrier_subset_boundary_component hcenter)).symm
  rcases C.image_core_eq_or_eq_exterior_of_boundary_transport D h hboundary' with
    hsame | hext
  · left
    have hclosed : h '' D.closed_core = C.closed_core := by
      rw [← D.closure_core_eq_closed_core, h.image_closure, hsame,
        C.closure_core_eq_closed_core]
    rw [← hclosed, hback]
  · right
    have hclosed : C.closed_core ∪ h '' D.closed_core =
        connectedComponent C.boundary_neck.center := by
      rw [← D.closure_core_eq_closed_core, h.image_closure, hext]
      exact C.closed_core_union_closure_exterior
    have hclosed' : e '' C.closed_core ∪ f '' D.closed_core =
        connectedComponent C.boundary_neck.center := by
      have hi := congrArg (fun S : Set M => e '' S) hclosed
      rwa [image_union, hback, hcomponent] at hi
    have hD : D.carrier ⊆ connectedComponent C.boundary_neck.center := by
      have hi : e '' (h '' D.carrier) ⊆ e '' connectedComponent C.boundary_neck.center :=
        image_mono (C.image_carrier_subset_component_of_boundary_transport D h hboundary')
      rwa [hback, hfcarrier, hcomponent] at hi
    have hunion : C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center := by
      apply Subset.antisymm (union_subset C.carrier_subset_boundary_component hD)
      rw [← hclosed', ← hecarrier, ← hfcarrier]
      exact union_subset_union (image_mono C.closed_core_subset_carrier)
        (image_mono D.closed_core_subset_carrier)
    refine ⟨hunion, ?_⟩
    rw [hunion, ← hclosed']
    exact (C.closed_core_compact.image e.continuous).union
      (D.closed_core_compact.image f.continuous)

end PoincareConjecture.CapCertificate
