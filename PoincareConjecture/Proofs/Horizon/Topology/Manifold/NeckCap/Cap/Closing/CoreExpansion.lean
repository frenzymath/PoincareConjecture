import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Complement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.GraphTransport











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}


theorem exists_core_point_outside_boundary_collar (C : CapCertificate g)
    {r : ℝ} (hr : 0 < r) (hrB : r < C.boundary_neck.epsilon⁻¹) :
    (C.core \ C.boundary_neck.closedCollar r).Nonempty := by
  let B := C.boundary_neck
  let t := (r + B.epsilon⁻¹) / 2
  have ht : r < t ∧ t < B.epsilon⁻¹ := by dsimp [t]; constructor <;> linarith
  have htpos : 0 < t := hr.trans ht.1
  have hmem {a b s : ℝ} (hs : s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹)
      (hab : s ∈ Ioo a b) (q : UnitTwoSphere) : B.coordinate_map (q, s) ∈ B.region a b := by
    refine ⟨B.coordinate_map_mem ⟨mem_univ _, hs⟩, ?_⟩
    rw [B.coordinate_inverse_coordinate_map ⟨mem_univ _, hs⟩]
    exact hab
  have hslice : ∃ a : ℝ, a ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ ∧ r < |a| ∧
      ∀ q : UnitTwoSphere, B.coordinate_map (q, a) ∈ C.core := by
    rcases C.boundary_neck_sides with ⟨hn, _⟩ | ⟨hp, _⟩
    · have ha : -t ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ := by constructor <;> linarith
      refine ⟨-t, ha, ?_, fun q => hn (hmem ha ?_ q)⟩
      · simpa only [abs_neg, abs_of_pos htpos] using ht.1
      · constructor <;> linarith
    · have ha : t ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ := by constructor <;> linarith
      refine ⟨t, ha, ?_, fun q => hp (hmem ha ?_ q)⟩
      · simpa only [abs_of_pos htpos] using ht.1
      · exact ⟨htpos, ht.2⟩
  obtain ⟨a, ha, har, hacore⟩ := hslice
  let q : UnitTwoSphere := Classical.choice inferInstance
  refine ⟨B.coordinate_map (q, a), hacore q, ?_⟩
  rintro ⟨⟨q', b⟩, ⟨_, hb⟩, heq⟩
  have hbdom : b ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ := by
    constructor <;> linarith [hb.1, hb.2]
  have hi := congrArg B.coordinate_inverse heq
  rw [B.coordinate_inverse_coordinate_map ⟨mem_univ _, hbdom⟩,
    B.coordinate_inverse_coordinate_map ⟨mem_univ _, ha⟩] at hi
  have hba : b = a := congrArg Prod.snd hi
  exact (not_lt_of_ge (abs_le.mpr (hba ▸ hb))) har



theorem closed_core_subset_graphTransport_of_graph_in_end (C : CapCertificate g)
    {r : ℝ} (hr : 0 < r) (hrB : r < C.boundary_neck.epsilon⁻¹)
    (h : UnitTwoSphere → ℝ) (hh : Continuous h) (hbound : ∀ q, |h q| < r)
    (hend : ∀ q, C.boundary_neck.coordinate_map (q, h q) ∈ C.end_neck.carrier) :
    C.closed_core ⊆
      C.boundary_neck.graphTransport hr hrB h hh hbound '' C.closed_core := by
  let e := C.boundary_neck.graphTransport hr hrB h hh hbound
  obtain ⟨p, hp, hpout⟩ := C.exists_core_point_outside_boundary_collar hr hrB
  have hfix : e p = p := C.boundary_neck.graphTransport_fixed hr hrB h hh hbound hpout
  have hboundary : e '' C.boundary_sphere =
      range (fun q => C.boundary_neck.coordinate_map (q, h q)) := by
    rw [C.boundary_eq_neck_sphere]
    exact C.boundary_neck.graphTransport_image_central_sphere hr hrB h hh hbound
  have havoid : C.core ⊆ (e '' C.boundary_sphere)ᶜ := by
    intro x hx hximage
    rw [hboundary] at hximage
    obtain ⟨q, rfl⟩ := hximage
    exact Set.disjoint_left.mp C.disjoint_closed_core_end (C.core_subset_closed_core hx) (hend q)
  have hpavoid : p ∈ C.boundary_sphereᶜ := Set.disjoint_left.mp C.disjoint_core_boundary hp
  have heq : e '' C.core = connectedComponentIn (e '' C.boundary_sphere)ᶜ p := by
    rw [C.core_eq_connectedComponentIn hp, e.image_connectedComponentIn hpavoid,
      e.image_compl, hfix]
  have hcore : C.core ⊆ e '' C.core := by
    rw [heq]
    exact C.isConnected_core.isPreconnected.subset_connectedComponentIn hp havoid
  simpa only [C.closure_core_eq_closed_core, ← e.image_closure] using closure_mono hcore

end PoincareConjecture.CapCertificate
