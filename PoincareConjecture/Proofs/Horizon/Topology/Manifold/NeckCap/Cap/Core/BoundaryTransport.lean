import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Collar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.GraphTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.SliceProjection

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem exists_boundary_slice_in_end (C : CapCertificate g) :
    ∃ a : ℝ, a ∈ Ioo (-C.boundary_neck.epsilon⁻¹) C.boundary_neck.epsilon⁻¹ ∧
      ∀ q : UnitTwoSphere, C.boundary_neck.coordinate_map (q, a) ∈ C.end_neck.carrier := by
  let B := C.boundary_neck
  have he : 0 < B.epsilon⁻¹ := inv_pos.mpr B.epsilon_pos
  have hmem {a b t : ℝ} (ht : t ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹)
      (hab : t ∈ Ioo a b) (q : UnitTwoSphere) :
      B.coordinate_map (q, t) ∈ B.region a b := by
    refine ⟨B.coordinate_map_mem ⟨mem_univ _, ht⟩, ?_⟩
    rw [B.coordinate_inverse_coordinate_map ⟨mem_univ _, ht⟩]
    exact hab
  rcases C.boundary_neck_sides with ⟨_, hp⟩ | ⟨_, hn⟩
  · have ht : B.epsilon⁻¹ / 2 ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ := by
      constructor <;> linarith
    refine ⟨B.epsilon⁻¹ / 2, ht, fun q => hp (hmem ht ?_ q)⟩
    constructor <;> linarith
  · have ht : -B.epsilon⁻¹ / 2 ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ := by
      constructor <;> linarith
    refine ⟨-B.epsilon⁻¹ / 2, ht, fun q => hn (hmem ht ?_ q)⟩
    constructor <;> linarith

theorem exists_boundary_end_transport_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M}, ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∃ (e : M ≃ₜ M) (K : Set M), IsCompact K ∧ K ⊆ C.carrier ∧
          (∀ x, x ∉ K → e x = x) ∧
          e '' C.boundary_sphere = C.end_neck.central_sphere := by
  obtain ⟨ε₀, hε₀, hsmall, hgraph⟩ := EpsilonNeck.exists_contained_coordinate_slice_graph.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hC
  obtain ⟨a, ha, hslice⟩ := C.exists_boundary_slice_in_end
  obtain ⟨h, hh, hdom, heq⟩ := hgraph C.end_neck C.boundary_neck
    (C.end_neck_epsilon.trans_le hC) (C.boundary_neck_epsilon.trans_le hC) ha hslice
  obtain ⟨r, hr, hrN, hbound⟩ := C.end_neck.exists_graph_collar h hh hdom
  obtain ⟨s, hs, hsB, habound⟩ :=
    C.boundary_neck.exists_graph_collar (fun _ => a) continuous_const (fun _ => ha)
  let f := C.boundary_neck.graphTransport hs hsB (fun _ => a) continuous_const habound
  let k := C.end_neck.graphTransport hr hrN h hh hbound
  have hf (x : M) (hx : x ∉ C.boundary_neck.closedCollar s) : f x = x :=
    C.boundary_neck.graphTransport_fixed hs hsB _ continuous_const habound hx
  have hk (x : M) (hx : x ∉ C.end_neck.closedCollar r) : k.symm x = x := by
    apply k.injective
    rw [k.apply_symm_apply]
    exact (C.end_neck.graphTransport_fixed hr hrN h hh hbound hx).symm
  refine ⟨f.trans k.symm, C.boundary_neck.closedCollar s ∪ C.end_neck.closedCollar r,
    (C.boundary_neck.isCompact_closedCollar hsB).union (C.end_neck.isCompact_closedCollar hrN),
    union_subset ((C.boundary_neck.closedCollar_subset_carrier hsB).trans C.boundary_neck_subset)
      ((C.end_neck.closedCollar_subset_carrier hrN).trans C.end_neck_subset), ?_, ?_⟩
  · intro x hx
    change k.symm (f x) = x
    rw [hf x (fun h => hx (Or.inl h)), hk x (fun h => hx (Or.inr h))]
  · have hfimage : f '' C.boundary_sphere =
        range (fun q => C.boundary_neck.coordinate_map (q, a)) := by
      rw [C.boundary_eq_neck_sphere]
      exact C.boundary_neck.graphTransport_image_central_sphere hs hsB _ continuous_const habound
    have hkimage : k '' C.end_neck.central_sphere =
        range (fun q => C.end_neck.coordinate_map (q, h q)) :=
      C.end_neck.graphTransport_image_central_sphere hr hrN h hh hbound
    change (k.symm ∘ f) '' C.boundary_sphere = _
    rw [image_comp, hfimage, heq, ← hkimage]
    exact k.toEquiv.symm_image_image C.end_neck.central_sphere

end PoincareConjecture.CapCertificate
