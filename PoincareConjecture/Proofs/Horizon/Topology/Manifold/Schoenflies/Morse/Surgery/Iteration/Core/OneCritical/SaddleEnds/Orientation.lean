import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.AnnularRegion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.CapSide
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Boundary



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

variable {v : E3} {g : S2 → E3} {B : Set Real}



theorem scale_neg_of_lower_annulus
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    {C : Set S2} (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hC : IsPreconnected C)
    {h : S2 → Real} (hh : Continuous h)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q)))
    (F : OpenPartialHomeomorph (S1 × Real) S2) {a l u : Real}
    (hla : l < a) (hFs : F.source = univ ×ˢ Ioo l u)
    (hheight : ∀ q t, t ∈ Ioo l u → h (F (q, t)) = t)
    (hlower : ∀ p ∈ C, a ≤ h p)
    (D : SphereSurgeryCoreCap v g B) (hD : D ∈ L)
    (hc : D.center ∈ Ioo l u)
    {p : S2} (hp : p ∈ D.chart '' sphere (0 : E2) 1)
    (hpF : p ∈ F.target)
    (hgreater : ∃ q ∈ C, D.center < h q) : D.scale < 0 := by
  have hboundary : D.chart '' sphere (0 : E2) 1 ⊆ C := fun z hz =>
    ((core_inter_closed_disk L hpair hcore D hD).superset hz).1
  have hDheight : ∀ z ∈ D.chart '' sphere (0 : E2) 1, h z = D.center :=
    fun z hz => ((hgerm z (hboundary hz)).eq_of_nhds).trans
      (D.height_eq_on_boundary z hz)
  by_contra hnot
  have hs : 0 < D.scale := lt_of_le_of_ne (le_of_not_gt hnot) D.scale_ne_zero.symm
  have hupper := D.upper_annular_strip_subset_open_disk_of_scale_pos hs hh F hFs
    hheight hc hDheight hp hpF (hgerm p (hboundary hp))
  have hwindow : ∀ z ∈ C ∩ F.target, h z ∈ Icc a D.center := by
    intro z hz
    refine ⟨hlower z hz.1, ?_⟩
    by_contra hnotle
    have hzt := hheight (F.symm z).1 (F.symm z).2 (hFs ▸ F.map_target hz.2).2
    rw [F.right_inv hz.2] at hzt
    have hzD := hupper (show z ∈ F '' (univ ×ˢ Ioo D.center u) from
      ⟨F.symm z, ⟨mem_univ _, hzt ▸ lt_of_not_ge hnotle,
        (hFs ▸ F.map_target hz.2).2.2⟩, F.right_inv hz.2⟩)
    exact (hcore ▸ hz.1) (mem_iUnion_of_mem D (mem_iUnion_of_mem hD hzD))
  have hmeet : (C ∩ F '' (univ ×ˢ Icc a D.center)).Nonempty := by
    have ht := hheight (F.symm p).1 (F.symm p).2 (hFs ▸ F.map_target hpF).2
    rw [F.right_inv hpF, hDheight p hp] at ht
    refine ⟨p, hboundary hp, F.symm p, ⟨mem_univ _, ?_⟩, F.right_inv hpF⟩
    rw [← ht]
    exact ⟨by rw [← hDheight p hp]; exact hlower p (hboundary hp), le_rfl⟩
  have hcover := subset_annular_strip_of_isPreconnected F hla hc.2 hFs hheight
    hC hwindow hmeet
  obtain ⟨q, hqC, hqheight⟩ := hgreater
  obtain ⟨⟨z, t⟩, ⟨_, ht⟩, rfl⟩ := hcover hqC
  rw [hheight z t ⟨hla.trans_le ht.1, ht.2.trans_lt hc.2⟩] at hqheight
  exact (not_lt_of_ge ht.2) hqheight


theorem scale_pos_of_upper_annulus
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    {C : Set S2} (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hC : IsPreconnected C)
    {h : S2 → Real} (hh : Continuous h)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q)))
    (F : OpenPartialHomeomorph (S1 × Real) S2) {b l u : Real}
    (hbu : b < u) (hFs : F.source = univ ×ˢ Ioo l u)
    (hheight : ∀ q t, t ∈ Ioo l u → h (F (q, t)) = t)
    (hupper : ∀ p ∈ C, h p ≤ b)
    (D : SphereSurgeryCoreCap v g B) (hD : D ∈ L)
    (hc : D.center ∈ Ioo l u)
    {p : S2} (hp : p ∈ D.chart '' sphere (0 : E2) 1)
    (hpF : p ∈ F.target)
    (hless : ∃ q ∈ C, h q < D.center) : 0 < D.scale := by
  have hboundary : D.chart '' sphere (0 : E2) 1 ⊆ C := fun z hz =>
    ((core_inter_closed_disk L hpair hcore D hD).superset hz).1
  have hDheight : ∀ z ∈ D.chart '' sphere (0 : E2) 1, h z = D.center :=
    fun z hz => ((hgerm z (hboundary hz)).eq_of_nhds).trans
      (D.height_eq_on_boundary z hz)
  by_contra hnot
  have hs : D.scale < 0 := lt_of_le_of_ne (le_of_not_gt hnot) D.scale_ne_zero
  have hlower := D.lower_annular_strip_subset_open_disk_of_scale_neg hs hh F hFs
    hheight hc hDheight hp hpF (hgerm p (hboundary hp))
  have hwindow : ∀ z ∈ C ∩ F.target, h z ∈ Icc D.center b := by
    intro z hz
    refine ⟨?_, hupper z hz.1⟩
    by_contra hnotle
    have hzt := hheight (F.symm z).1 (F.symm z).2 (hFs ▸ F.map_target hz.2).2
    rw [F.right_inv hz.2] at hzt
    have hzD := hlower (show z ∈ F '' (univ ×ˢ Ioo l D.center) from
      ⟨F.symm z, ⟨mem_univ _, (hFs ▸ F.map_target hz.2).2.1,
        hzt ▸ lt_of_not_ge hnotle⟩, F.right_inv hz.2⟩)
    exact (hcore ▸ hz.1) (mem_iUnion_of_mem D (mem_iUnion_of_mem hD hzD))
  have hmeet : (C ∩ F '' (univ ×ˢ Icc D.center b)).Nonempty := by
    have ht := hheight (F.symm p).1 (F.symm p).2 (hFs ▸ F.map_target hpF).2
    rw [F.right_inv hpF, hDheight p hp] at ht
    refine ⟨p, hboundary hp, F.symm p, ⟨mem_univ _, ?_⟩, F.right_inv hpF⟩
    rw [← ht]
    exact ⟨le_rfl, by rw [← hDheight p hp]; exact hupper p (hboundary hp)⟩
  have hcover := subset_annular_strip_of_isPreconnected F hc.1 hbu hFs hheight
    hC hwindow hmeet
  obtain ⟨q, hqC, hqheight⟩ := hless
  obtain ⟨⟨z, t⟩, ⟨_, ht⟩, rfl⟩ := hcover hqC
  rw [hheight z t ⟨hc.1.trans_le ht.1, ht.2.trans_lt hbu⟩] at hqheight
  exact (not_lt_of_ge ht.1) hqheight

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap
