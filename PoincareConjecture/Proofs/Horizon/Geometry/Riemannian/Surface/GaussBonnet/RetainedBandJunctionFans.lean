import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedBandJunctionGerms
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.ChainTopAngles

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

theorem core_germ_at_band_junction_of_band_germ
    (p : T.decomposition.IncidentEdgeIndex) (i j : Fin (T.graphs p).count)
    (hij : i.succ = j.castSucc) (A : Set Plane)
    (hband : (chartAt Plane (T.chart p.1.1 : S)) ''
      ((T.bands p i).faces.carrier ∪ (T.bands p j).faces.carrier)
      =ᶠ[𝓝 (T.bandJunctionPoint p i.succ)] A) :
    (T.refined.mesh p.1.1).toPlaneComplex.support =ᶠ[𝓝 (T.bandJunctionPoint p i.succ)]
      (interior A)ᶜ := by
  have hc := T.core_complement_germ_at_band_junction p i j hij
  have hi := support_eventuallyEq_interior hband
  filter_upwards [hc, hi] with z hcz hiz
  change (T.refined.mesh p.1.1).toPlaneComplex.support z = ¬interior A z
  change (T.refined.mesh p.1.1).toPlaneComplex.support z = ¬interior _ z at hcz
  rwa [hiz] at hcz

omit [T2Space S] in
theorem band_endpoint_top_mem_scaled_core_contacts
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (right : Bool) {r : ℝ} (hr : r ≠ 0) :
    ∃ l ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region p.1.1, ∃ a : ℝ, a ≠ 0 ∧
        r • (T.bands p i).ambientEndpointTop right = a • l := by
  obtain ⟨l, hl, a, ha, he⟩ := T.band_top_functional_mem_scaled_core_contacts p i
    (if right then (T.bands p i).faces.lastCell else (T.bands p i).faces.firstCell)
  exact ⟨l, hl, r * a, mul_ne_zero hr ha, by
    change r • (T.bands p i).ambientTopFunctional _ = _
    rw [he, smul_smul]⟩

set_option maxHeartbeats 2000000 in

theorem canonical_vertex_fan_at_upper_band_junction
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i j : Fin (T.graphs p).count) (hij : i.succ = j.castSucc)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 = (T.chains p).cutRay i.succ T.length) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  let C := (chartAt Plane (T.chart p.1.1 : S)).symm
  let B := T.bands p
  let z := T.bandJunctionPoint p i.succ
  let L : Plane →L[ℝ] Plane := mfderiv (𝓡 2) (𝓡 2) C z
  let v := (B i).chartTopVertex (B i).faces.lastCell.castSucc - z
  let w := (B j).chartTopVertex (B j).faces.firstCell.succ - z
  let u := (T.chains p).direction i.succ
  let outward := g.cornerAngle (C z) (L v) (L u) + g.cornerAngle (C z) (L w) (L u)
  let core := ∑ t : (T.refined.mesh p.1.1).Triangle,
    meshVertexAngleContribution g C (T.refinement.mesh (.inr (.inr ⟨p.1.1, t⟩))) (C z)
  have hqz : q.1 = C z := hq
  obtain ⟨c, α, β, hβ, hc0, hc1, hc2, he⟩ :=
    (T.chains p).exists_adjacent_top_coordinates B i j hij
  have hc0' : c 0 = z := by simpa only [z, bandJunctionPoint, C,
    OpenPartialHomeomorph.symm_symm] using hc0
  have hi : (B i).chartTopVertex (B i).faces.lastCell.succ = z := by
    have hlast : (B i).faces.lastCell.succ = Fin.last (B i).faces.interface.count := by
      apply Fin.ext
      dsimp [ObliqueBandFaces.lastCell]
      have hn := (B i).faces.interface.count_pos
      omega
    rw [hlast]
    exact (T.bandJunctionPoint_eq_last_top p i).symm
  have hj : (B j).chartTopVertex 0 = z := by
    rw [← T.bandJunctionPoint_eq_first_top p j, ← hij]
  have hsign := (T.chains p).adjacent_top_coordinate_ray_signs B i j hij c α β hβ hc1 hc2 he
  dsimp only at hsign
  rw [hi, hj] at hsign
  have hv1 : 0 < (c.coord 1).linear v := hsign.1.1
  have hv2 : (c.coord 2).linear v = 0 := hsign.1.2
  have hw1 : (c.coord 1).linear w < 0 := hsign.2.1.1
  have hw2 : (c.coord 2 + α • c.coord 1).linear w = 0 := hsign.2.1.2
  have hu1 : (c.coord 1).linear u = 0 := hsign.2.2.1
  have hu2 : 0 < (c.coord 2).linear u := hsign.2.2.2
  have hC := contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := (T.chart p.1.1 : S))
  have hCi := contMDiffOn_chart (I := 𝓡 2) (n := ∞) (x := (T.chart p.1.1 : S))
  have hu : L u ≠ 0 := by
    intro h
    have hD : C.MDifferentiable (𝓡 2) (𝓡 2) :=
      ⟨hC.mdifferentiableOn (by simp), hCi.mdifferentiableOn (by simp)⟩
    have hz : u = 0 := hD.mfderiv_injective (T.bandJunctionPoint_mem_source p i)
      (h.trans (map_zero _).symm)
    rw [hz, map_zero] at hu2
    exact lt_irrefl _ hu2
  have hband := (T.chains p).adjacent_top_carrier_coordinate_bend B i j hij c α β hβ hc0 hc1 hc2 he
  rw [hc0'] at hband
  have hnorm : c.coord 2 + α • c.coord 1 = β⁻¹ • (B j).ambientEndpointTop false := by
    rw [he, smul_smul, inv_mul_cancel₀ hβ.ne', one_smul]
  have hcore : core = outward := by
    rcases lt_trichotomy α 0 with hα | hα | hα
    · obtain ⟨d, hd0, hd1, hd2⟩ := exists_coordinate_bend_basis c hα.ne (σ := -1) (by norm_num)
      have hd1' : d.coord 1 = -c.coord 2 := by simpa only [neg_one_smul] using hd1
      have hd2' : d.coord 2 = -(c.coord 2 + α • c.coord 1) := by simpa only [neg_one_smul] using hd2
      have hd0' : d 0 = z := hd0.trans hc0'
      have hband' : C.symm '' ((B i).faces.carrier ∪ (B j).faces.carrier)
          =ᶠ[𝓝 z] {x | 0 ≤ d.coord 1 x ∧ 0 ≤ d.coord 2 x} := by
        filter_upwards [hband] with x hx
        apply propext
        have hh := propext_iff.mp hx
        change (_ ↔ if 0 ≤ α then _ else _) at hh
        rw [if_neg (not_le.mpr hα)] at hh
        rw [hd1', hd2']
        change (_ ↔ 0 ≤ -c.coord 2 x ∧ 0 ≤ -(c.coord 2 x + α * c.coord 1 x))
        simpa only [neg_nonneg] using hh
      have hlocal := T.core_germ_at_band_junction_of_band_germ p i j hij _ hband'
      change _ =ᶠ[𝓝 z] _ at hlocal
      rw [← hd0', compl_interior_convexSector] at hlocal
      have hm : d 0 ∈ (T.refined.mesh p.1.1).toPlaneComplex.support := by
        apply (propext_iff.mp hlocal.eq_of_nhds).mpr
        change d.coord 1 (d 0) ≤ 0 ∨ d.coord 2 (d 0) ≤ 0
        simp
      have hcont1 := T.band_endpoint_top_mem_scaled_core_contacts p i true (r := -1) (by norm_num)
      have hcont2 := T.band_endpoint_top_mem_scaled_core_contacts p j false
        (r := -β⁻¹) (neg_ne_zero.mpr (inv_ne_zero hβ.ne'))
      have he1 : d.coord 1 = (-1 : ℝ) • (B i).ambientEndpointTop true := by
        rw [hd1', hc2, neg_one_smul]
      have he2 : d.coord 2 = (-β⁻¹) • (B j).ambientEndpointTop false := by
        rw [hd2', hnorm, neg_smul]
      have hcon := T.core_contribution_at_reflex_sector g p.1.1 d
        (he1 ▸ hcont1) (he2 ▸ hcont2) hm (by rwa [compl_interior_convexSector])
      have hangle := coordinate_bend_outward_angle_neg g (C z) L c d hα hd1' hd2'
        v w u hv1 hv2 hw1 hw2 hu1 hu2 hu
      have ha := congrArg (fun z : Plane => g.cornerAngle (C z)
        ((mfderiv (𝓡 2) (𝓡 2) C z) (d 1 - d 0))
        ((mfderiv (𝓡 2) (𝓡 2) C z) (d 2 - d 0))) hd0'
      rw [ha] at hcon
      have hpoint := congrArg (fun x : S => ∑ t : (T.refined.mesh p.1.1).Triangle,
        meshVertexAngleContribution g C (T.refinement.mesh (.inr (.inr ⟨p.1.1, t⟩))) x)
        (congrArg C hd0')
      rw [hpoint] at hcon
      exact hcon.trans hangle.symm
    · subst α
      have hw2' : (c.coord 2).linear w = 0 := by simpa only [zero_smul, add_zero] using hw2
      have hangle := coordinate_bend_outward_angle_zero g (C z) L c v w u hv1 hv2 hw1 hw2'
      have hband' : C.symm '' ((B i).faces.carrier ∪ (B j).faces.carrier)
          =ᶠ[𝓝 z] {x | c.coord 2 x ≤ 0} := by
        simpa only [le_refl, ite_true, zero_mul, add_zero, or_self] using hband
      have hlocal := T.core_germ_at_band_junction_of_band_germ p i j hij _ hband'
      have hsurj : Function.Surjective (c.coord 2) := by
        rw [hc2]
        exact (B i).ambientTopFunctional_surjective (B i).faces.lastCell
      rw [interior_affine_halfspace_nonpos _ hsurj] at hlocal
      have hlocal' : (T.refined.mesh p.1.1).toPlaneComplex.support =ᶠ[𝓝 z]
          {x | 0 ≤ c.coord 2 x} := by
        filter_upwards [hlocal] with x hx
        exact propext ((propext_iff.mp hx).trans not_lt)
      have hz : c.coord 2 z = 0 := by rw [← hc0']; simp
      have hm : z ∈ (T.refined.mesh p.1.1).toPlaneComplex.support :=
        (propext_iff.mp hlocal'.eq_of_nhds).mpr (by change 0 ≤ c.coord 2 z; rw [hz])
      have hcont := T.band_endpoint_top_mem_scaled_core_contacts p i true (r := 1) one_ne_zero
      simp only [one_smul] at hcont
      have hcon := T.core_contribution_at_straight_canonical_vertex g p.1.1 q hqz.symm hm
        (c.coord 2) hsurj (by rw [hc2]; exact hcont) hz hlocal'
      rw [hqz] at hcon
      exact hcon.trans hangle.symm
    · obtain ⟨d, hd0, hd1, hd2⟩ := exists_coordinate_bend_basis c hα.ne' (σ := 1) one_ne_zero
      simp only [one_smul] at hd1 hd2
      have hd0' : d 0 = z := hd0.trans hc0'
      have hband' : C.symm '' ((B i).faces.carrier ∪ (B j).faces.carrier)
          =ᶠ[𝓝 z] {x | d.coord 1 x ≤ 0 ∨ d.coord 2 x ≤ 0} := by
        filter_upwards [hband] with x hx
        apply propext
        have hh := propext_iff.mp hx
        change (_ ↔ if 0 ≤ α then _ else _) at hh
        rw [if_pos hα.le] at hh
        rw [hd1, hd2]
        change (_ ↔ c.coord 2 x ≤ 0 ∨ c.coord 2 x + α * c.coord 1 x ≤ 0)
        exact hh
      have hlocal := T.core_germ_at_band_junction_of_band_germ p i j hij _ hband'
      change _ =ᶠ[𝓝 z] _ at hlocal
      rw [← hd0', compl_interior_reflexSector] at hlocal
      have hm : d 0 ∈ (T.refined.mesh p.1.1).toPlaneComplex.support := by
        apply (propext_iff.mp hlocal.eq_of_nhds).mpr
        change 0 ≤ d.coord 1 (d 0) ∧ 0 ≤ d.coord 2 (d 0)
        simp
      have hcont1 := T.band_endpoint_top_mem_scaled_core_contacts p i true (r := 1) one_ne_zero
      have hcont2 := T.band_endpoint_top_mem_scaled_core_contacts p j false
        (r := β⁻¹) (inv_ne_zero hβ.ne')
      simp only [one_smul] at hcont1
      have he2 : d.coord 2 = β⁻¹ • (B j).ambientEndpointTop false := hd2.trans hnorm
      have hcon := T.core_contribution_at_convex_sector g p.1.1 d
        (by rw [hd1, hc2]; exact hcont1) (he2 ▸ hcont2) hm hlocal
      have hangle := coordinate_bend_outward_angle_pos g (C z) L c d hα hd1 hd2
        v w u hv1 hv2 hw1 hw2 hu1 hu2 hu
      have ha := congrArg (fun z : Plane => g.cornerAngle (C z)
        ((mfderiv (𝓡 2) (𝓡 2) C z) (d 1 - d 0))
        ((mfderiv (𝓡 2) (𝓡 2) C z) (d 2 - d 0))) hd0'
      rw [ha] at hcon
      have hpoint := congrArg (fun x : S => ∑ t : (T.refined.mesh p.1.1).Triangle,
        meshVertexAngleContribution g C (T.refinement.mesh (.inr (.inr ⟨p.1.1, t⟩))) x)
        (congrArg C hd0')
      rw [hpoint] at hcon
      exact hcon.trans hangle.symm
  have hp := (T.chains p).adjacent_top_refined_fan_add_outward_angles B g hC hCi i j hij
    (fun a => (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).refinement_lines)
    (fun a => (T.refinement.subdivision (.inr (.inl ⟨⟨p, j⟩, a⟩))).refinement_lines)
  have hmesh (k : Fin (T.graphs p).count) (a : Fin (B k).faces.interface.count × Bool) :
      T.refinement.mesh (.inr (.inl ⟨⟨p, k⟩, a⟩)) =
        (TriangleMesh.single ((B k).faces.faceBasis a) ((B k).faces.faceBasis a).ind).refineByLines
          (T.refinement.subdivision (.inr (.inl ⟨⟨p, k⟩, a⟩))).refinement_lines :=
    (T.refinement.subdivision (.inr (.inl ⟨⟨p, k⟩, a⟩))).mesh_eq_refineByLines
  have hwhole := T.vertex_contribution_eq_band_pair_add_core_at_junction g p i j hij
  dsimp only at hwhole hp
  rw [hqz, hwhole]
  change _ + core = _
  rw [hcore]
  simp_rw [hmesh]
  exact hp

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
