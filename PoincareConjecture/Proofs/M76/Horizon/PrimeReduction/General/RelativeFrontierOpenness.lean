import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

private theorem relative_halfspace_neighborhood {R B Z : Set X}
    (hBreg : closure (interior B) = B) (hBR : B ⊆ R) (hZ : IsClosed Z)
    (hfront : frontier B ⊆ frontier R ∪ Z)
    {x : X} (hxB : x ∈ B) (hxZ : x ∉ Z)
    (H : OpenPartialHomeomorph X V3) (hxH : x ∈ H.source)
    (ell : V3 →ᴬ[ℝ] ℝ) (hell : ell.toAffineMap.linear ≠ 0)
    (hhalf : ∀ y ∈ H.source, y ∈ R ↔ 0 ≤ ell (H y)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ∩ R ⊆ B \ Z := by
  let V := H.target ∩ H.symm ⁻¹' Zᶜ
  have hV : IsOpen V := H.isOpen_inter_preimage_symm hZ.isOpen_compl
  have hxV : H x ∈ V := ⟨H.map_source hxH, by
    change H.symm (H x) ∉ Z
    rwa [H.left_inv hxH]⟩
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV (H x) hxV
  let U := H.source ∩ H ⁻¹' ball (H x) r
  have hU : IsOpen U := H.isOpen_inter_preimage isOpen_ball
  have hxU : x ∈ U := ⟨hxH, mem_ball_self hr⟩
  have hUZ (y : X) (hy : y ∈ U) : y ∉ Z := by
    have h := (hrV hy.2).2
    change H.symm (H y) ∉ Z at h
    rwa [H.left_inv hy.1] at h
  have hRfront := H.isImage_frontier_of_affine_nonneg ell hell hhalf
  let P := ball (H x) r ∩ {z | 0 < ell z}
  have hPcv : Convex ℝ P := (convex_ball _ _).inter
    ((convex_Ioi (0 : ℝ)).affine_preimage ell.toAffineMap)
  have hPtarget : P ⊆ H.target := fun _ hz => (hrV hz.1).1
  have hpre : IsPreconnected (H.symm '' P) := hPcv.isPreconnected.image H.symm
    (H.continuousOn_invFun.mono hPtarget)
  have havoid : Disjoint (frontier (interior B)) (H.symm '' P) := by
    apply disjoint_left.mpr
    rintro y hy ⟨z, hz, rfl⟩
    have hzT := hPtarget hz
    have hzU : H.symm z ∈ U := ⟨H.map_target hzT, by
      change H (H.symm z) ∈ ball (H x) r
      rw [H.right_inv hzT]
      exact hz.1⟩
    have hyR : H.symm z ∈ frontier R := by
      rcases hfront (frontier_interior_subset hy) with h | h
      · exact h
      · exact False.elim (hUZ _ hzU h)
    have hzero := (hRfront.apply_mem_iff (H.map_target hzT)).mpr hyR
    rw [H.right_inv hzT] at hzero
    exact (ne_of_gt hz.2) hzero
  have hxcl : x ∈ closure (interior B) := hBreg.symm.subset hxB
  obtain ⟨z, hzU, hzB⟩ := mem_closure_iff.mp hxcl U hU hxU
  have hzR : z ∈ interior R := interior_mono hBR hzB
  have hzpos : 0 < ell (H z) := by
    have hle := (hhalf z hzU.1).mp (interior_subset hzR)
    have hne : ell (H z) ≠ 0 := fun h =>
      ((hRfront.apply_mem_iff hzU.1).mp h).2 hzR
    exact lt_of_le_of_ne hle (Ne.symm hne)
  have hmeet : ((H.symm '' P) ∩ interior B).Nonempty :=
    ⟨z, ⟨H z, ⟨hzU.2, hzpos⟩, H.left_inv hzU.1⟩, hzB⟩
  have hsub := hpre.m76_subset_of_disjoint_frontier isOpen_interior havoid hmeet
  have hellopen : IsOpenMap (ell : V3 → ℝ) :=
    ell.toAffineMap.isOpenMap ell.continuous
      (ell.toAffineMap.linear_surjective_iff.mp (LinearMap.surjective hell))
  have hposcl : closure {z : V3 | 0 < ell z} = {z : V3 | 0 ≤ ell z} := by
    change closure ((ell : V3 → ℝ) ⁻¹' Ioi 0) = (ell : V3 → ℝ) ⁻¹' Ici 0
    rw [← hellopen.preimage_closure_eq_closure_preimage ell.continuous, closure_Ioi]
  refine ⟨U, hU, hxU, ?_⟩
  rintro y ⟨hyU, hyR⟩
  have hycl : H y ∈ closure P := isOpen_ball.inter_closure
    ⟨hyU.2, hposcl.symm.subset ((hhalf y hyU.1).mp hyR)⟩
  have hyimage : H.symm (H y) ∈ closure (H.symm '' P) :=
    mem_closure_image
      (H.continuousOn_invFun.continuousAt (H.open_target.mem_nhds (H.map_source hyU.1)))
      hycl
  rw [H.left_inv hyU.1] at hyimage
  exact ⟨hBreg.subset (closure_mono hsub hyimage), hUZ y hyU⟩

theorem PLDomain.isOpen_relative_sdiff_of_frontier_subset {R B Z : Set X}
    (hR : PLDomain e R)
    (hBreg : closure (interior B) = B) (hBR : B ⊆ R) (hZ : IsClosed Z)
    (hfront : frontier B ⊆ frontier R ∪ Z) :
    IsOpen ((Subtype.val : R → X) ⁻¹' (B \ Z)) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  change (x : X) ∈ B \ Z at hx
  by_cases hxf : (x : X) ∈ frontier R
  · obtain ⟨ell, v, H, hv, hxH, _, _, hhalf⟩ := hR.halfspace x hxf
    have hell : ell.toAffineMap.linear ≠ 0 := by
      intro he
      have hv' : ell.toAffineMap.linear v = 1 := hv
      rw [he] at hv'
      norm_num at hv'
    obtain ⟨U, hU, hxU, hUR⟩ :=
      relative_halfspace_neighborhood hBreg hBR hZ hfront hx.1 hx.2 H hxH ell hell hhalf
    apply Filter.mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds hxU)
    intro y hy
    exact hUR ⟨hy, y.property⟩
  · have hxint : (x : X) ∈ interior B := by
      by_contra hn
      rcases hfront ⟨subset_closure hx.1, hn⟩ with h | h
      · exact hxf h
      · exact hx.2 h
    have hU : IsOpen (interior B \ Z) := isOpen_interior.sdiff hZ
    apply Filter.mem_of_superset
      ((hU.preimage continuous_subtype_val).mem_nhds ⟨hxint, hx.2⟩)
    intro y hy
    exact ⟨interior_subset hy.1, hy.2⟩

end PoincareConjecture.M76
