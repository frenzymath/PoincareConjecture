import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CommonCornerCaps
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Gluing













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture

private theorem signed_quadrant_interior_disjoint {i j : Bool × Bool} (hij : i ≠ j) :
    Disjoint (interior ((sectorParameterEquiv 0 i) ''
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
      ((sectorParameterEquiv 0 j) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) := by
  rw [← (sectorParameterEquiv 0 i).image_interior]
  have hquad : interior {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} =
      Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    change interior (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)) = _
    rw [interior_prod_eq, interior_Ici]
  rw [hquad]
  apply disjoint_left.mpr
  rintro z ⟨p, hp, rfl⟩ ⟨q, hq, heq⟩
  change 0 < p.1 ∧ 0 < p.2 at hp
  change 0 ≤ q.1 ∧ 0 ≤ q.2 at hq
  have heq1 := congrArg Prod.fst heq
  have heq2 := congrArg Prod.snd heq
  rcases i with ⟨i, i'⟩
  rcases j with ⟨j, j'⟩
  cases i <;> cases i' <;> cases j <;> cases j' <;>
    simp [sectorParameterEquiv_apply] at hij heq1 heq2 <;>
    linarith [hp.1, hp.2, hq.1, hq.2]





theorem m64Intrinsic_corner_carriers_inter_subset_frontier
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    {A B : Set AnnulusCoordinates} (hA : IsClosed A) {i j : Bool × Bool} (hij : i ≠ j)
    (hsubA : A ⊆ H '' (H.source ∩
      (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (hsubB : B ⊆ H '' (H.source ∩
      (sectorParameterEquiv 0 j) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2})) :
    A ∩ B ⊆ frontier A := by
  intro z hz
  refine ⟨by simpa only [hA.closure_eq] using hz.1, ?_⟩
  intro hzint
  obtain ⟨q, ⟨hq, hqj⟩, rfl⟩ := hsubB hz.2
  have hpre : H.source ∩ H ⁻¹' A ⊆
      (sectorParameterEquiv 0 i) '' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} := by
    intro p hp
    obtain ⟨w, ⟨hw, hwi⟩, heq⟩ := hsubA hp.2
    exact (H.injOn hw hp.1 heq) ▸ hwi
  have hqint : q ∈ interior (H.source ∩ H ⁻¹' A) := by
    rw [interior_inter, H.open_source.interior_eq]
    have hmem : q ∈ H.source ∩ H ⁻¹' interior A := ⟨hq, hzint⟩
    rw [H.preimage_interior] at hmem
    exact hmem
  exact disjoint_left.mp (signed_quadrant_interior_disjoint hij)
    (interior_mono hpre hqint) hqj





theorem m64Intrinsic_corner_shared_edge_mem_interior
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (f g : SmoothFace AnnulusCoordinates)
    (C D : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b c : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hb : convexHull ℝ (range b) ⊆ C.source)
    (hc : convexHull ℝ (range c) ⊆ D.source)
    (hfcarrier : f.carrier = C '' convexHull ℝ (range b))
    (hgcarrier : g.carrier = D '' convexHull ℝ (range c))
    (hfboundary : ∀ k, (f.boundary k).map = C ∘
      affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1)))
    (hgboundary : ∀ k, (g.boundary k).map = D ∘
      affineChartSegment (c (k.succAbove 0)) (c (k.succAbove 1)))
    {i j : Bool × Bool} (hij : i ≠ j)
    (hsubf : f.carrier ⊆ H '' (H.source ∩
      (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (hsubg : g.carrier ⊆ H '' (H.source ∩
      (sectorParameterEquiv 0 j) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (k l : Fin 3)
    (hagreement : EqOn (f.boundary k).map (g.boundary l).map (Icc (0 : ℝ) 1))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (f.boundary k).map t ∈ interior (f.carrier ∪ g.carrier) := by
  have hinter := m64Intrinsic_corner_carriers_inter_subset_frontier H
    f.isClosed_carrier hij hsubf hsubg
  apply mem_interior_union_of_coordinate_triangles_shared_edge f g C D b c
    hb hc hfcarrier hgcarrier hfboundary hgboundary hinter k l ?_ hagreement ht
  rw [hfboundary]
  have hsrc (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1)) s ∈ C.source := by
    apply hb
    apply segment_subset_convexHull (mem_range_self (k.succAbove 0))
      (mem_range_self (k.succAbove 1))
    rw [segment_eq_image_lineMap]
    refine ⟨s, hs, ?_⟩
    simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]
  intro s hs v hv heq
  have he := C.injOn (hsrc s hs) (hsrc v hv) heq
  have hne : b (k.succAbove 0) ≠ b (k.succAbove 1) := by
    intro h
    have h01 : (0 : Fin 2) = 1 := Fin.succAbove_right_injective (b.ind.injective h)
    norm_num at h01
  apply AffineMap.lineMap_injective ℝ hne
  simpa [affineChartSegment, AffineMap.lineMap_apply, add_comm] using he

end PoincareConjecture
