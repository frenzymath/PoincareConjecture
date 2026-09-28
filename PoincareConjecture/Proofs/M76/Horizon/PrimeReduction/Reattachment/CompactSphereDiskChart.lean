import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CirclePlanarNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalDiskBicollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.MarkedProductInteriorChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "Square" => closedBall (0 : P2) 1
local notation "Cube" => Set.prod (Set.prod (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1)) (Icc (-1 : ℝ) 1)
local notation "OpenCube" => Set.prod (Set.prod (Ioo (-1 : ℝ) 1) (Ioo (-1 : ℝ) 1)) (Ioo (-1 : ℝ) 1)

theorem ChartwisePLSphere.exists_compact_flattening_chart_with_target
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S K : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hK : IsCompact K) (hKS : K ⊆ S)
    (p : X) (hpS : p ∈ S) (hpK : p ∉ K) :
    ∃ Q : OpenPartialHomeomorph X V3,
      K ⊆ Q.source ∧ Q.source ⊆ interior R ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ x ∈ Q.source, x ∈ S ↔ Q x 2 = 0) ∧
      Q.target = ball (0 : V3) 1 := by
  classical
  let A0 := (Subtype.val : S → X) ⁻¹' K
  have hA0 : IsCompact A0 := Topology.IsInducing.subtypeVal.isCompact_preimage'
    hK (by simpa only [Subtype.range_coe] using hKS)
  let A1 := (Subtype.val : Sphere → V3) '' (s.parametrization.symm '' A0)
  have hA1 : IsCompact A1 := (hA0.image s.parametrization.symm.continuous).image
    continuous_subtype_val
  have hA1S : A1 ⊆ Sphere := by rintro _ ⟨x, _, rfl⟩; exact x.property
  let pole := s.parametrization.symm ⟨p, hpS⟩
  have hpole : (pole : V3) ∉ A1 := by
    rintro ⟨x, ⟨y, hy, hyx⟩, hx⟩
    have hxp : x = pole := Subtype.ext hx
    have hyp : y = (⟨p, hpS⟩ : S) := s.parametrization.symm.injective (hyx.trans hxp)
    apply hpK
    simpa only [A0, hyp, mem_preimage, Subtype.coe_mk] using hy
  obtain ⟨C, hC, hCs⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hsphere : Sphere = frontier (closedBall (0 : V3) 1) := by
    rw [frontier_closedBall _ one_ne_zero]
  obtain ⟨A, q, hA, hAS, hA1A, _, _⟩ :=
    C.exists_convex_frontier_disk_of_compact_with_open_interior hC
      (isCompact_closedBall (0 : V3) 1) (convex_closedBall (0 : V3) 1)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
      (hCs.trans hsphere) (F := P2) (by simp [Module.finrank_prod])
      ⟨pole, hsphere.subset pole.property⟩ hA1 (hA1S.trans hsphere.subset) hpole
  rw [← hsphere] at hAS
  have hSquare : IsFinitePLBallPair P2 Square (sphere (0 : P2) 1) := by
    have h := CoordinateHalfBoxes.base_ballPair (show (0 : ℝ) < 1 by norm_num)
    have hbase : CoordinateHalfBoxes.base 1 = Square := by
      ext x
      simp only [CoordinateHalfBoxes.base, mem_prod, mem_Icc, mem_closedBall,
        dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_le_iff, abs_le]
    have hfront := h.frontier_eq_of_finrank_eq rfl
    rw [hbase, frontier_closedBall _ one_ne_zero] at hfront
    rwa [hbase, ← hfront] at h
  obtain ⟨H, hH, hHrim⟩ := hSquare.exists_homeomorph hA
  obtain ⟨g, hg, hHg⟩ := hH
  have hgA : MapsTo g Square A := by
    intro x hx
    rw [← hHg ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  have hgi : InjOn g Square := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hHg ⟨x, hx⟩).trans (hxy.trans (hHg ⟨y, hy⟩).symm))))
  let j := s.map ∘ g
  have hj : PolyhedralPLInCharts e j Square := by
    obtain ⟨L, hL, hLs, hfaces⟩ := hg
    rw [← hLs]
    exact s.piecewiseAffine.comp_finitePiecewiseAffineOn L hL
      ⟨L, hL, rfl, hfaces⟩ (fun x hx => hAS (hgA (hLs.subset hx)))
  have hsmi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (s.parametrization.injective
      (Subtype.ext ((s.map_eq ⟨x, hx⟩).symm.trans
        (hxy.trans (s.map_eq ⟨y, hy⟩)))))
  have hjS : MapsTo j Square S := by
    intro x hx
    change s.map (g x) ∈ S
    rw [s.map_eq ⟨g x, hAS (hgA hx)⟩]
    exact (s.parametrization _).property
  obtain ⟨b, hb, hbi, hbR, hb0, hbS, _, hbint⟩ :=
    s.exists_original_disk_bicollar hR he hSR isOpen_univ (subset_univ S)
      j hj (hsmi.comp hgi (fun _ hx => hAS (hgA hx))) hjS
  have hsquare : Square = Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    ext x
    simp only [mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
      max_le_iff, abs_le, mem_prod, mem_Icc]
  have hopenSquare : ball (0 : P2) 1 = Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1 := by
    rw [← interior_closedBall _ one_ne_zero, hsquare, interior_prod_eq, interior_Icc]
  rw [hsquare] at hb hbi hbR hb0 hbS hbint
  rw [hopenSquare] at hbint
  change interior (b '' Cube) = b '' OpenCube at hbint
  have hBclosed : IsClosed (b '' Cube) :=
    (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).image_of_continuousOn
      hb.continuousOn).isClosed
  have hCubeClosed : IsClosed Cube := (isClosed_Icc.prod isClosed_Icc).prod isClosed_Icc
  have hCubeInterior : interior Cube = OpenCube := by
    change interior ((Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ Icc (-1 : ℝ) 1) = _
    simp only [interior_prod_eq, interior_Icc]
    rfl
  have hboundary (z) (hz : z ∈ Cube) : b z ∈ frontier (b '' Cube) ↔ z ∈ frontier Cube := by
    rw [frontier, hBclosed.closure_eq, hbint, frontier,
      hCubeClosed.closure_eq, hCubeInterior]
    simp only [mem_sdiff, mem_image_of_mem b hz,
      hz, true_and]
    exact not_congr (hbi.mem_image_iff
      (by exact prod_mono (prod_mono Ioo_subset_Icc_self
        Ioo_subset_Icc_self) Ioo_subset_Icc_self) hz)
  obtain ⟨Q, hQs, hQt, hQinv, hQ⟩ := exists_marked_product_interior_chart
    he.compatible b hb hbi rfl hboundary
  refine ⟨Q, ?_, ?_, hQ, ?_, hQt.trans markedProductCoordinates_preimage_openCube⟩
  · intro x hx
    let u := s.parametrization.symm ⟨x, hKS hx⟩
    have huA : (u : V3) ∈ A \ q := hA1A ⟨u, ⟨⟨x, hKS hx⟩, hx, rfl⟩, rfl⟩
    let v := H.symm ⟨u, huA.1⟩
    have hvint : (v : P2) ∈ ball (0 : P2) 1 := by
      rw [← interior_closedBall _ one_ne_zero, hSquare.interior_eq_sdiff_of_finrank_eq rfl]
      refine ⟨v.property, fun hv => huA.2 ?_⟩
      have h := (hHrim v).mp hv
      simpa only [v, H.apply_symm_apply] using h
    have hgv : g v = (u : V3) := (hHg v).symm.trans
      (congrArg Subtype.val (H.apply_symm_apply ⟨u, huA.1⟩))
    rw [hQs, hbint]
    refine ⟨((v : P2), 0), ⟨hopenSquare.subset hvint, by norm_num⟩, ?_⟩
    rw [hb0 v (hsquare.subset v.property)]
    change s.map (g v) = x
    rw [hgv, s.map_eq u]
    exact congrArg Subtype.val (s.parametrization.apply_symm_apply ⟨x, hKS hx⟩)
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := interior_subset (hQs.subset hx)
    exact (hbR hz).2
  · intro x hx
    have hyt := Q.map_source hx
    rw [hQt] at hyt
    have hy : markedProductCoordinates (Q x) ∈ Cube :=
      prod_mono (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
        Ioo_subset_Icc_self hyt
    have hval : b (markedProductCoordinates (Q x)) = x :=
      (hQinv (Q x)).symm.trans (Q.left_inv hx)
    exact (show x ∈ S ↔ b (markedProductCoordinates (Q x)) ∈ S by rw [hval]).trans
      ((hbS _ hy).trans Iff.rfl)

theorem ChartwisePLSphere.exists_compact_flattening_chart
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S K : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hK : IsCompact K) (hKS : K ⊆ S)
    (p : X) (hpS : p ∈ S) (hpK : p ∉ K) :
    ∃ Q : OpenPartialHomeomorph X V3,
      K ⊆ Q.source ∧ Q.source ⊆ interior R ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      ∀ x ∈ Q.source, x ∈ S ↔ Q x 2 = 0 := by
  obtain ⟨Q, hKQ, hQR, hQ, hQS, _⟩ :=
    s.exists_compact_flattening_chart_with_target hR he hSR hK hKS p hpS hpK
  exact ⟨Q, hKQ, hQR, hQ, hQS⟩

end PoincareConjecture.M76
