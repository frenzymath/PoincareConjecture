import PoincareConjecture.Proofs.M76.Triangulation.HamiltonWallComplementBall
import Mathlib.Analysis.Convex.Topology








set_option autoImplicit false
open Set Metric
open scoped Topology
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

private theorem PLDomain.exists_connected_interior_nhds
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (he : PLDomain e R)
    {x : X} (hx : x ∈ R) {N : Set X} (hN : IsOpen N) (hxN : x ∈ N) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ N ∧ IsPreconnected (U ∩ interior R) := by
  have hchart : ∃ (H : OpenPartialHomeomorph X V3) (A : Set V3),
      x ∈ H.source ∧ Convex ℝ A ∧ H.IsImage (interior R) A := by
    by_cases hxi : x ∈ interior R
    · obtain ⟨i, hi⟩ := he.cover x
      let H := (e i).restrOpen (interior R) isOpen_interior
      refine ⟨H, univ, ⟨hi,hxi⟩, convex_univ, ?_⟩
      intro y hy
      exact iff_of_true (mem_univ _) hy.2
    · obtain ⟨ell,v,H,hv,hxH,_,_,hhalf⟩ := he.halfspace x
        ⟨he.closed.closure_eq.symm ▸ hx,hxi⟩
      have hn : ell.toAffineMap.linear ≠ 0 := by
        intro hz
        have hv' : ell.toAffineMap.linear v = 1 := hv
        rw [hz] at hv'
        norm_num at hv'
      have ho : IsOpenMap (ell : V3 → ℝ) := ell.toAffineMap.isOpenMap ell.continuous
        (ell.toAffineMap.linear_surjective_iff.mp (LinearMap.surjective hn))
      have hi : interior {z | 0 ≤ ell z} = {z | 0 < ell z} := by
        change interior ((ell : V3 → ℝ) ⁻¹' Ici 0) = (ell : V3 → ℝ) ⁻¹' Ioi 0
        rw [← ho.preimage_interior_eq_interior_preimage ell.continuous, interior_Ici]
      have him : H.IsImage R {z | 0 ≤ ell z} := fun {y} hy => (hhalf y hy).symm
      refine ⟨H, {z | 0 < ell z}, hxH,
        Convex.affine_preimage ell.toAffineMap (convex_Ioi (0 : ℝ)), ?_⟩
      rw [←hi]
      exact him.interior
  obtain ⟨H,A,hxH,hA,him⟩ := hchart
  have hop := H.isOpen_inter_preimage_symm hN
  have hmem : H x ∈ H.target ∩ H.symm ⁻¹' N :=
    ⟨H.map_source hxH, by simpa only [mem_preimage,H.left_inv hxH] using hxN⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hop (H x) hmem
  let U := H.source ∩ H ⁻¹' ball (H x) r
  have hUt : ball (H x) r ∩ A ⊆ H.target := fun _ hy => (hball hy.1).1
  have hEq : U ∩ interior R = H.symm '' (ball (H x) r ∩ A) := by
    apply Subset.antisymm
    · rintro y ⟨⟨hyH,hyball⟩,hyR⟩
      exact ⟨H y,⟨hyball,(him.apply_mem_iff hyH).mpr hyR⟩,H.left_inv hyH⟩
    · rintro _ ⟨y,hy,rfl⟩
      have hyH := hUt hy
      refine ⟨⟨H.map_target hyH,?_⟩,?_⟩
      · simpa only [mem_preimage,H.right_inv hyH] using hy.1
      · exact (him.symm.apply_mem_iff hyH).mpr hy.2
  refine ⟨U,H.isOpen_inter_preimage isOpen_ball,⟨hxH,mem_ball_self hr⟩,?_,?_⟩
  · intro y hy
    have hn := (hball hy.2).2
    simpa only [mem_preimage,H.left_inv hy.1] using hn
  · rw [hEq]
    exact ((convex_ball (H x) r).inter hA).isPreconnected.image H.symm
      (H.symm.continuousOn.mono hUt)

theorem PLDomain.closure_sdiff_eq_closure_interior_sdiff
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R D : Set X}
    (he : PLDomain e R) (hD : IsClosed D) :
    closure (R \ D) = closure (interior R \ D) := by
  have hout : R \ D ⊆ closure (interior R \ D) := by
    intro x hx
    have hxR : x ∈ closure (interior R) := he.closure_interior.symm ▸ hx.1
    have h := hD.isOpen_compl.inter_closure ⟨hx.2,hxR⟩
    exact closure_mono (fun y hy => show y ∈ interior R \ D from ⟨hy.2,hy.1⟩) h
  exact Subset.antisymm (closure_minimal hout isClosed_closure)
    (closure_mono (sdiff_subset_sdiff_left interior_subset))

theorem PLDomain.closed_complement_contact
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R D : Set X}
    (he : PLDomain e R) (hD : IsClosed D) (hDR : D ⊆ R)
    (hreg : closure (interior D) = D) :
    closure (R \ D) ∩ D = closure (frontier D ∩ interior R) := by
  rw [he.closure_sdiff_eq_closure_interior_sdiff hD]
  apply Subset.antisymm
  · intro x hx
    by_contra hn
    obtain ⟨U,hU,hxU,hUN,hconn⟩ := he.exists_connected_interior_nhds (hDR hx.2)
      isClosed_closure.isOpen_compl hn
    have havoid : Disjoint (frontier (interior D)) (U ∩ interior R) := by
      apply disjoint_left.mpr
      intro y hy hyU
      exact hUN hyU.1 (subset_closure ⟨frontier_interior_subset hy,hyU.2⟩)
    obtain ⟨y,hyU,hyD⟩ := mem_closure_iff.mp (hreg.symm ▸ hx.2) U hU hxU
    have hin := hconn.m76_subset_of_disjoint_frontier isOpen_interior havoid
      ⟨y,⟨hyU,interior_mono hDR hyD⟩,hyD⟩
    obtain ⟨z,hzU,hz⟩ := mem_closure_iff.mp hx.1 U hU hxU
    exact hz.2 (interior_subset (hin ⟨hzU,hz.1⟩))
  · apply closure_minimal _ (isClosed_closure.inter hD)
    intro x hx
    refine ⟨?_,hD.frontier_subset hx.1⟩
    have hc : x ∈ closure Dᶜ := by rw [closure_compl]; exact hx.1.2
    exact isOpen_interior.inter_closure ⟨hx.2,hc⟩


end PoincareConjecture.M76

