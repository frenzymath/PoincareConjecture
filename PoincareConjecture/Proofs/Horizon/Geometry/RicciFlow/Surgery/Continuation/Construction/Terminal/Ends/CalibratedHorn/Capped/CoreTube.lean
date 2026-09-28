import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Capped.CoreTube.Inward
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Capped.CoreTube.SphereCapture
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Cylinder.NonFilling
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Separation









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {X : Set M}



theorem closed_core_tube_noncontainment_of_epsilon_le
    (C : CapCertificate g) (tube : EpsilonTubeCertificate g X)
    (htube : tube.epsilon ≤ 1 / 200) : ¬ C.closed_core ⊆ tube.carrier := by
  intro hcoretube
  let B := tube.chain
  have hBU : (B.unionOpen : Set M) = tube.carrier := tube.carrier_eq_chain_union.symm
  have hneck (j : ℤ) (hj : j ∈ B.shape.active) : (B.neck j).carrier ⊆ B.unionOpen :=
    fun _ hx => mem_iUnion.mpr ⟨⟨j, hj⟩, hx⟩
  obtain ⟨p, hpcore, hcapture⟩ := C.exists_core_point_capturing_neck_spheres
  have hpU : p ∈ (B.unionOpen : Set M) :=
    hBU.symm ▸ hcoretube (C.core_subset_closed_core hpcore)
  obtain ⟨⟨i, hi⟩, hpi⟩ := mem_iUnion.mp hpU
  let N := B.neck i
  let s := (N.coordinate_inverse p).2
  have hN : N.epsilon ≤ 1 / 200 := (B.epsilon_eq i hi).trans_le htube
  have hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := (N.coordinate_inverse_mem p hpi).2
  have hslice := hcapture N hN hpi
  obtain ⟨h, hh, hdom, hgraph, _⟩ :=
    C.boundary_neck.sphereSlice_graph_and_isotopy_of_epsilon_le N
      (C.boundary_neck_epsilon.trans_le C.epsilon_le_threshold) hN hs
      (fun q => (hslice q).2)
  obtain ⟨D, L, hL, hLB, hDfix, _, hDsphere⟩ :=
    C.boundary_neck.exists_smooth_graph_transport h hh hdom
  have hDs : D '' C.boundary_sphere =
      range (fun q : UnitTwoSphere => N.coordinate_map (q, s)) := by
    rw [C.boundary_eq_neck_sphere, hDsphere, ← hgraph]
  have hDcore : D '' C.closed_core ⊆ C.closed_core := by
    apply C.image_closed_core_subset_of_boundary_image_subset_core D.toHomeomorph
      hL (hLB.trans C.boundary_neck_subset) hDfix
    change D '' C.boundary_sphere ⊆ C.core
    rw [hDs]
    rintro _ ⟨q, rfl⟩
    exact (hslice q).1
  obtain ⟨P, L', _, hL'N, hPfix, _, hPsphere⟩ :=
    N.exists_smooth_graph_transport (fun _ => s) contMDiff_const (fun _ => hs)
  let e := D.toHomeomorph.trans P.symm.toHomeomorph
  have heS : e '' C.boundary_neck.central_sphere = N.central_sphere := by
    change (P.symm ∘ D) '' C.boundary_neck.central_sphere = _
    rw [image_comp, ← C.boundary_eq_neck_sphere, hDs, ← hPsphere]
    exact P.toEquiv.symm_image_image _
  have hecore : e '' C.closed_core ⊆ (B.unionOpen : Set M) := by
    rintro x ⟨y, hy, rfl⟩
    have hDy : D y ∈ tube.carrier := hcoretube (hDcore (mem_image_of_mem D hy))
    change P.symm (D y) ∈ (B.unionOpen : Set M)
    by_contra hout
    have hfix := hPfix (P.symm (D y)) (fun h => hout (hneck i hi (hL'N h)))
    rw [P.apply_symm_apply] at hfix
    exact hout (hfix ▸ (hBU.symm ▸ hDy))
  have hecomp : e '' connectedComponent C.boundary_neck.center = connectedComponent N.center := by
    have h := e.image_connectedComponentIn (s := univ)
      (x := C.boundary_neck.center) (mem_univ _)
    simp only [image_univ, e.surjective.range_eq, connectedComponentIn_univ] at h
    apply h.trans
    symm
    apply connectedComponent_eq
    apply N.carrier_subset_connectedComponent
    apply N.central_sphere_subset
    rw [← heS]
    exact mem_image_of_mem e C.boundary_neck.center_on_central_sphere
  have hiSep : N.IsSeparating :=
    (C.boundary_neck.isSeparating_iff_of_homeomorph N e hecomp heS).mp
      C.boundary_neck_isSeparating
  have hsep (j : ℤ) (hj : j ∈ B.shape.active) : (B.neck j).IsSeparating := by
    obtain ⟨D', _, _, _, _, _, hfS⟩ :=
      B.central_sphere_smooth_transport_of_epsilon_le htube i hi j hj
    let f := D'.toHomeomorph
    change f '' N.central_sphere = (B.neck j).central_sphere at hfS
    have hfcomp : f '' connectedComponent N.center = connectedComponent (B.neck j).center := by
      have h := f.image_connectedComponentIn (s := univ) (x := N.center) (mem_univ _)
      simp only [image_univ, f.surjective.range_eq, connectedComponentIn_univ] at h
      apply h.trans
      symm
      apply connectedComponent_eq
      apply (B.neck j).carrier_subset_connectedComponent
      apply (B.neck j).central_sphere_subset
      rw [← hfS]
      exact mem_image_of_mem f N.center_on_central_sphere
    exact (N.isSeparating_iff_of_homeomorph (B.neck j) f hfcomp hfS).mp hiSep
  have hfront : frontier (e '' C.closed_core) = N.central_sphere := by
    rw [← e.image_frontier, C.core_frontier_eq_boundary, C.boundary_eq_neck_sphere, heS]
  have hint : (interior (e '' C.closed_core)).Nonempty := by
    rw [← e.image_interior, ← C.core_eq_interior_closed_core]
    exact C.core_nonempty.image e
  exact B.no_compact_filling_of_epsilon_le htube hsep i hi _ hecore hfront hint
    (C.closed_core_compact.image e.continuous)

end PoincareConjecture.CapCertificate
