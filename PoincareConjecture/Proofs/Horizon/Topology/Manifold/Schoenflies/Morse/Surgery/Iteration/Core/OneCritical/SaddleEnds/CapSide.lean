import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.CapHeight
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.DomainIdentification



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private instance : ConnectedSpace S1 :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) zero_le_one)

variable {v : E3} {g : S2 → E3} {B : Set Real}




theorem upper_annular_strip_subset_open_disk_of_scale_pos
    (D : SphereSurgeryCoreCap v g B) (hs : 0 < D.scale)
    {h : S2 → Real} (hh : Continuous h)
    (F : OpenPartialHomeomorph (S1 × Real) S2) {l u : Real}
    (hFs : F.source = univ ×ˢ Ioo l u)
    (hheight : ∀ q t, t ∈ Ioo l u → h (F (q, t)) = t)
    (hc : D.center ∈ Ioo l u)
    (hboundary : ∀ p ∈ D.chart '' sphere (0 : E2) 1, h p = D.center)
    {p : S2} (hp : p ∈ D.chart '' sphere (0 : E2) 1)
    (hpF : p ∈ F.target)
    (hgerm : h =ᶠ[𝓝 p] (fun q => inner Real v (g q))) :
    F '' (univ ×ˢ Ioo D.center u) ⊆ D.chart '' ball 0 1 := by
  let V := F '' (univ ×ˢ Ioo D.center u)
  have hsub : univ ×ˢ Ioo D.center u ⊆ F.source := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    exact hFs ▸ ⟨mem_univ _, hc.1.trans ht.1, ht.2⟩
  have hV : IsPreconnected V :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image _
      (F.continuousOn.mono hsub)
  have hfront : Disjoint V (frontier (D.chart '' ball 0 1)) := by
    rw [ParallelDisks.frontier_image_ball zero_lt_one D.chart D.source D.smooth D.symm_smooth]
    apply Set.disjoint_left.mpr
    rintro z ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩ hz
    have heq := hboundary _ hz
    rw [hheight q t ⟨hc.1.trans ht.1, ht.2⟩] at heq
    exact (ne_of_gt ht.1) heq
  have hpcl : p ∈ closure (D.chart '' ball 0 1) := by
    rw [ParallelDisks.closure_image_ball zero_lt_one D.chart D.source]
    exact image_mono sphere_subset_closedBall hp
  have hpnhds : F.target ∩ h ⁻¹' Iio u ∩
      {q | h q = inner Real v (g q)} ∈ 𝓝 p := by
    apply Filter.inter_mem
    · apply Filter.inter_mem (F.open_target.mem_nhds hpF)
      exact (hh.isOpen_preimage _ isOpen_Iio).mem_nhds (by
        change h p < u
        rw [hboundary p hp]
        exact hc.2)
    · exact hgerm
  obtain ⟨W, hWsub, hWopen, hpW⟩ := _root_.mem_nhds_iff.mp hpnhds
  obtain ⟨z, hzW, hzD⟩ := mem_closure_iff.mp hpcl W hWopen hpW
  have hz := hWsub hzW
  have hzpos := mul_pos (D.normalized_height_pos_on_open_disk hzD) hs
  rw [div_mul_cancel₀ _ D.scale_ne_zero, ← hz.2] at hzpos
  have hzabove : D.center < h z := by linarith
  have hzcoord := F.map_target hz.1.1
  have hzt := hheight (F.symm z).1 (F.symm z).2 (hFs ▸ hzcoord).2
  rw [F.right_inv hz.1.1] at hzt
  have hzV : z ∈ V := by
    refine ⟨F.symm z, ⟨mem_univ _, ?_⟩, F.right_inv hz.1.1⟩
    rw [← hzt]
    exact ⟨hzabove, hz.1.2⟩
  exact Poincare.Topology.subset_of_isPreconnected_of_disjoint_frontier
    (D.chart.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans D.source)) hV hfront ⟨z, hzV, hzD⟩


theorem lower_annular_strip_subset_open_disk_of_scale_neg
    (D : SphereSurgeryCoreCap v g B) (hs : D.scale < 0)
    {h : S2 → Real} (hh : Continuous h)
    (F : OpenPartialHomeomorph (S1 × Real) S2) {l u : Real}
    (hFs : F.source = univ ×ˢ Ioo l u)
    (hheight : ∀ q t, t ∈ Ioo l u → h (F (q, t)) = t)
    (hc : D.center ∈ Ioo l u)
    (hboundary : ∀ p ∈ D.chart '' sphere (0 : E2) 1, h p = D.center)
    {p : S2} (hp : p ∈ D.chart '' sphere (0 : E2) 1)
    (hpF : p ∈ F.target)
    (hgerm : h =ᶠ[𝓝 p] (fun q => inner Real v (g q))) :
    F '' (univ ×ˢ Ioo l D.center) ⊆ D.chart '' ball 0 1 := by
  let V := F '' (univ ×ˢ Ioo l D.center)
  have hsub : univ ×ˢ Ioo l D.center ⊆ F.source := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    exact hFs ▸ ⟨mem_univ _, ht.1, ht.2.trans hc.2⟩
  have hV : IsPreconnected V :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image _
      (F.continuousOn.mono hsub)
  have hfront : Disjoint V (frontier (D.chart '' ball 0 1)) := by
    rw [ParallelDisks.frontier_image_ball zero_lt_one D.chart D.source D.smooth D.symm_smooth]
    apply Set.disjoint_left.mpr
    rintro z ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩ hz
    have heq := hboundary _ hz
    rw [hheight q t ⟨ht.1, ht.2.trans hc.2⟩] at heq
    exact (ne_of_lt ht.2) heq
  have hpcl : p ∈ closure (D.chart '' ball 0 1) := by
    rw [ParallelDisks.closure_image_ball zero_lt_one D.chart D.source]
    exact image_mono sphere_subset_closedBall hp
  have hpnhds : F.target ∩ h ⁻¹' Ioi l ∩
      {q | h q = inner Real v (g q)} ∈ 𝓝 p := by
    apply Filter.inter_mem
    · apply Filter.inter_mem (F.open_target.mem_nhds hpF)
      exact (hh.isOpen_preimage _ isOpen_Ioi).mem_nhds (by
        change l < h p
        rw [hboundary p hp]
        exact hc.1)
    · exact hgerm
  obtain ⟨W, hWsub, hWopen, hpW⟩ := _root_.mem_nhds_iff.mp hpnhds
  obtain ⟨z, hzW, hzD⟩ := mem_closure_iff.mp hpcl W hWopen hpW
  have hz := hWsub hzW
  have hzneg := mul_neg_of_pos_of_neg (D.normalized_height_pos_on_open_disk hzD) hs
  rw [div_mul_cancel₀ _ D.scale_ne_zero, ← hz.2] at hzneg
  have hzbelow : h z < D.center := by linarith
  have hzcoord := F.map_target hz.1.1
  have hzt := hheight (F.symm z).1 (F.symm z).2 (hFs ▸ hzcoord).2
  rw [F.right_inv hz.1.1] at hzt
  have hzV : z ∈ V := by
    refine ⟨F.symm z, ⟨mem_univ _, ?_⟩, F.right_inv hz.1.1⟩
    rw [← hzt]
    exact ⟨hz.1.2, hzbelow⟩
  exact Poincare.Topology.subset_of_isPreconnected_of_disjoint_frontier
    (D.chart.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans D.source)) hV hfront ⟨z, hzV, hzD⟩

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap
