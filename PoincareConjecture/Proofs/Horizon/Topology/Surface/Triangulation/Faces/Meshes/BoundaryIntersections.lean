


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes.BoundarySubdivision








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

private theorem boundaryIntersections_segment_eq_lineMap (a b : Plane) (t : ℝ) :
    affineChartSegment a b t = AffineMap.lineMap a b t := by
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]

private theorem boundaryIntersections_segment_image (a b : Plane) :
    affineChartSegment a b '' Icc (0 : ℝ) 1 = affineSegment ℝ a b := by
  unfold affineSegment
  congr 1
  funext t
  exact boundaryIntersections_segment_eq_lineMap a b t

private theorem boundaryIntersections_edge_subset (b : AffineBasis (Fin 3) ℝ Plane)
    (i : Fin 3) : affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) ⊆
      convexHull ℝ (range b) := by
  rw [affineSegment_eq_segment]
  exact segment_subset_convexHull (mem_range_self _) (mem_range_self _)

private theorem boundaryIntersections_coord_nonneg (b : AffineBasis (Fin 3) ℝ Plane)
    {z : Plane} (hz : z ∈ convexHull ℝ (range b)) (i : Fin 3) : 0 ≤ b.coord i z := by
  have h : ∀ j, 0 ≤ b.coord j z := by
    simpa only [b.convexHull_eq_nonneg_coord, mem_ofPred_eq] using hz
  exact h i

private theorem boundaryIntersections_parent_edge (b : AffineBasis (Fin 3) ℝ Plane)
    (i : Fin 3) :
    convexHull ℝ (range b) ∩ {z | b.coord i z = 0} =
      affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) := by
  rw [convexHull_inter_affine_zero_of_nonneg_set (range b) (b.coord i)
    (by rintro z ⟨j, rfl⟩; rw [b.coord_apply]; split_ifs <;> norm_num)]
  rw [affineSegment_eq_segment, ← convexHull_pair]
  congr 1
  ext z
  constructor
  · rintro ⟨⟨j, rfl⟩, hj⟩
    have hji : j ≠ i := by intro h; subst j; simp at hj
    fin_cases i <;> fin_cases j <;> simp_all [Fin.succAbove, Fin.lt_def, Fin.ext_iff]
  · rintro (rfl | rfl)
    · refine ⟨mem_range_self _, ?_⟩
      fin_cases i <;> simp [Fin.succAbove, Fin.lt_def, Fin.ext_iff]
    · refine ⟨mem_range_self _, ?_⟩
      fin_cases i <;> simp [Fin.succAbove, Fin.lt_def, Fin.ext_iff]

private theorem boundaryIntersections_planar
    (b c : AffineBasis (Fin 3) ℝ Plane)
    (hc : convexHull ℝ (range c) ⊆ convexHull ℝ (range b)) (i : Fin 3) :
    (∃ k : Fin 3,
      convexHull ℝ (range c) ∩ affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) =
        affineSegment ℝ (c (k.succAbove 0)) (c (k.succAbove 1))) ∨
    ∃ j : Fin 3,
      convexHull ℝ (range c) ∩ affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) ⊆
        {c j} := by
  classical
  let U : Finset (Fin 3) := Finset.univ.filter fun j => b.coord i (c j) = 0
  have hnonneg (z : Plane) (hz : z ∈ range c) : 0 ≤ b.coord i z :=
    boundaryIntersections_coord_nonneg b (hc (subset_convexHull ℝ _ hz)) i
  have hinter : convexHull ℝ (range c) ∩
      affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) =
      convexHull ℝ (c '' (U : Set (Fin 3))) := by
    rw [← boundaryIntersections_parent_edge]
    have hreduce : convexHull ℝ (range c) ∩
        (convexHull ℝ (range b) ∩ {z | b.coord i z = 0}) =
        convexHull ℝ (range c) ∩ {z | b.coord i z = 0} := by
      ext z
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hc h.1, h.2⟩⟩
    rw [hreduce, convexHull_inter_affine_zero_of_nonneg_set (range c) (b.coord i) hnonneg]
    congr 1
    ext z
    simp only [mem_inter_iff, mem_range, mem_ofPred_eq, mem_image, Finset.mem_coe,
      U, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j, rfl⟩, hj⟩
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, hj⟩
  have hnotall : U ≠ Finset.univ := by
    intro hall
    have hzero (j : Fin 3) : b.coord i (c j) = 0 := by
      have hj : j ∈ U := hall ▸ Finset.mem_univ j
      exact (Finset.mem_filter.mp hj).2
    have hzeroAt : b.coord i (b i) = 0 := by
      rw [← c.affineCombination_coord_eq_self (b i),
        Finset.univ.map_affineCombination c (fun j => c.coord j (b i))
          (c.sum_coord_apply_eq_one (b i)) (b.coord i),
        Finset.univ.affineCombination_eq_linear_combination _ _ (c.sum_coord_apply_eq_one (b i))]
      simp only [Function.comp_apply, hzero, smul_zero, Finset.sum_const_zero]
    simp at hzeroAt
  have hcard : U.card < 3 := by
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ U, hnotall⟩)
    simpa using hlt
  have hcases : U.card = 0 ∨ U.card = 1 ∨ U.card = 2 := by omega
  rw [hinter]
  rcases hcases with hzero | hone | htwo
  · right
    exact ⟨0, by simp [Finset.card_eq_zero.mp hzero]⟩
  · right
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hone
    exact ⟨j, by simp [hj]⟩
  · left
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show U.card < (Finset.univ : Finset (Fin 3)).card by simpa using hcard)
    have hU : U = Finset.univ.erase k := Finset.eq_of_subset_of_card_le
      (fun j hj => Finset.mem_erase.mpr ⟨by intro heq; subst j; exact hk hj, Finset.mem_univ j⟩)
      (by simp [htwo])
    have hpair : (Finset.univ.erase k : Finset (Fin 3)) = {k.succAbove 0, k.succAbove 1} := by
      fin_cases k <;> decide
    exact ⟨k, by simp only [hU, hpair, Finset.coe_insert, Finset.coe_singleton,
      image_insert_eq, image_singleton, affineSegment_eq_segment, convexHull_pair]⟩

private theorem boundaryIntersections_interval (a b c d : ℝ)
    (hc : c ∉ Ioo a b) (hd : d ∉ Ioo a b) :
    Icc a b ⊆ Icc c d ∨ (Icc a b ∩ Icc c d ⊆ {a}) ∨
      (Icc a b ∩ Icc c d ⊆ {b}) := by
  by_cases hca : c ≤ a
  · by_cases hbd : b ≤ d
    · exact Or.inl (fun _ hx => ⟨hca.trans hx.1, hx.2.trans hbd⟩)
    · have hda : d ≤ a := le_of_not_gt (fun had => hd ⟨had, lt_of_not_ge hbd⟩)
      right
      left
      intro x hx
      exact mem_singleton_iff.mpr (le_antisymm (hx.2.2.trans hda) hx.1.1)
  · have hbc : b ≤ c := le_of_not_gt (fun hcb => hc ⟨lt_of_not_ge hca, hcb⟩)
    right
    right
    intro x hx
    exact mem_singleton_iff.mpr (le_antisymm hx.1.2 (hbc.trans hx.2.1))

private theorem boundaryIntersections_uIcc_subset {a c : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1) :
    uIcc a c ⊆ Icc (0 : ℝ) 1 :=
  fun _ hx => ⟨(le_min ha.1 hc.1).trans hx.1, hx.2.trans (max_le ha.2 hc.2)⟩

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M]
  {F : OpenPartialHomeomorph Plane M} {b : AffineBasis (Fin 3) ℝ Plane} {S : Finset M}

namespace SmoothTriangleBoundarySubdivision

variable (D : SmoothTriangleBoundarySubdivision F b S)

include D in
omit [T2Space M] in
theorem parent_source_subset : convexHull ℝ (range b) ⊆ F.source := by
  rw [← D.support, ← meshTriangleBasis_sources_cover]
  intro z hz
  obtain ⟨t, ht⟩ := mem_iUnion.mp hz
  exact D.source_subset t ht

omit [T2Space M] in


theorem carrier_inter_parent_edge (t : D.mesh.Triangle) (i : Fin 3) :
    (∃ k : Fin 3,
      (D.face t).carrier ∩ (F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1))) =
        ((D.face t).boundary k).map '' Icc (0 : ℝ) 1) ∨
    ∃ j : Fin 3,
      (D.face t).carrier ∩ (F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1))) ⊆
        {F (meshTriangleBasis D.mesh t j)} := by
  have hc : convexHull ℝ (range (meshTriangleBasis D.mesh t)) ⊆ convexHull ℝ (range b) := by
    rw [← D.support]
    exact meshTriangleBasis_subset_support D.mesh t
  rw [D.carrier_eq, ← F.injOn.image_inter (D.source_subset t)
    ((boundaryIntersections_edge_subset b i).trans D.parent_source_subset)]
  rcases boundaryIntersections_planar b (meshTriangleBasis D.mesh t) hc i with
    ⟨k, hk⟩ | ⟨j, hj⟩
  · left
    refine ⟨k, ?_⟩
    rw [hk, D.boundary_map, image_comp, boundaryIntersections_segment_image]
  · right
    refine ⟨j, ?_⟩
    rintro q ⟨z, hz, rfl⟩
    rw [mem_singleton_iff.mp (hj hz)]
    exact mem_singleton _

include D in
omit [T2Space M] in
theorem parent_edge_injective (i : Fin 3) :
    InjOn (F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1))) (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  have hsrc (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) v ∈ F.source := by
    apply D.parent_source_subset
    apply boundaryIntersections_edge_subset b i
    rw [← boundaryIntersections_segment_image]
    exact mem_image_of_mem _ hv
  have heq := F.injOn (hsrc s hs) (hsrc t ht) hst
  simp only [boundaryIntersections_segment_eq_lineMap] at heq
  apply AffineMap.lineMap_injective ℝ ?_ heq
  intro h
  have h01 : (0 : Fin 2) = 1 := Fin.succAbove_right_injective (b.ind.injective h)
  norm_num at h01

omit [T2Space M] in


theorem boundary_parameters_of_subset_parent_edge (t : D.mesh.Triangle) (k i : Fin 3)
    (hsub : ((D.face t).boundary k).map '' Icc (0 : ℝ) 1 ⊆
      F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1))) :
    ∃ a c : ℝ, a ∈ Icc (0 : ℝ) 1 ∧ c ∈ Icc (0 : ℝ) 1 ∧ a ≠ c ∧
      (∀ v : ℝ, ((D.face t).boundary k).map v =
        F (affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) (a + v * (c - a)))) ∧
      ((D.face t).boundary k).map 0 ∈ S ∧ ((D.face t).boundary k).map 1 ∈ S := by
  let B := meshTriangleBasis D.mesh t
  have hzero : ((D.face t).boundary k).map 0 = F (B (k.succAbove 0)) := by
    simp [D.boundary_map, affineChartSegment, B]
  have hone : ((D.face t).boundary k).map 1 = F (B (k.succAbove 1)) := by
    simp [D.boundary_map, affineChartSegment, B]
  have hzeroIn := hsub ⟨0, by simp, rfl⟩
  have honeIn := hsub ⟨1, by simp, rfl⟩
  rw [hzero, ← boundaryIntersections_segment_image, image_image] at hzeroIn
  rw [hone, ← boundaryIntersections_segment_image, image_image] at honeIn
  obtain ⟨a, ha, hfa⟩ := hzeroIn
  obtain ⟨c, hc, hfc⟩ := honeIn
  have hsrc (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) v ∈ F.source := by
    apply D.parent_source_subset
    apply boundaryIntersections_edge_subset b i
    rw [← boundaryIntersections_segment_image]
    exact mem_image_of_mem _ hv
  have hea := F.injOn (hsrc a ha)
    (D.source_subset t (subset_convexHull ℝ _ (mem_range_self (k.succAbove 0)))) hfa
  have hec := F.injOn (hsrc c hc)
    (D.source_subset t (subset_convexHull ℝ _ (mem_range_self (k.succAbove 1)))) hfc
  have hfront : affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) ⊆
      frontier (convexHull ℝ (range b)) := by
    rw [frontier_convexHull_affineBasis_fin3_segments]
    intro q hq
    exact mem_iUnion.mpr ⟨i, hq⟩
  obtain ⟨_, _, _, _, _, _, _, hmark0, hmark1⟩ :=
    D.boundary_subsegment t k (hsub.trans (image_mono hfront))
  refine ⟨a, c, ha, hc, ?_, ?_, hmark0, hmark1⟩
  · intro hac
    have heq : B (k.succAbove 0) = B (k.succAbove 1) := hea.symm.trans (hac ▸ hec)
    have h01 : (0 : Fin 2) = 1 := Fin.succAbove_right_injective (B.ind.injective heq)
    norm_num at h01
  · intro v
    rw [D.boundary_map]
    change F (affineChartSegment (B (k.succAbove 0)) (B (k.succAbove 1)) v) = _
    rw [← hea, ← hec]
    congr 1
    simp only [affineChartSegment]
    module




theorem carrier_inter_marked_parent_subsegment (t : D.mesh.Triangle) (i : Fin 3)
    (a c : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1)
    (hmarka : F (affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) a) ∈ S)
    (hmarkc : F (affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) c) ∈ S) :
    (∃ k : Fin 3,
      (D.face t).carrier ∩
        ((F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1))) '' uIcc a c) =
        ((D.face t).boundary k).map '' Icc (0 : ℝ) 1) ∨
    ∃ j : Fin 3,
      (D.face t).carrier ∩
        ((F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1))) '' uIcc a c) ⊆
        {F (meshTriangleBasis D.mesh t j)} := by
  let e : ℝ → M := F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1))
  change (∃ k : Fin 3, (D.face t).carrier ∩ (e '' uIcc a c) =
      ((D.face t).boundary k).map '' Icc (0 : ℝ) 1) ∨
    ∃ j : Fin 3, (D.face t).carrier ∩ (e '' uIcc a c) ⊆
      {F (meshTriangleBasis D.mesh t j)}
  have hparent : F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) =
      e '' Icc (0 : ℝ) 1 := by
    rw [← boundaryIntersections_segment_image, image_image]
    rfl
  have hsmall : e '' uIcc a c ⊆
      F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) := by
    rw [hparent]
    exact image_mono (boundaryIntersections_uIcc_subset ha hc)
  rcases D.carrier_inter_parent_edge t i with ⟨k, hk⟩ | ⟨j, hj⟩
  · have hedgeparent : ((D.face t).boundary k).map '' Icc (0 : ℝ) 1 ⊆
        F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) := by
      rw [← hk]
      exact inter_subset_right
    obtain ⟨s, u, hs, hu, hsu, hparam, _, _⟩ :=
      D.boundary_parameters_of_subset_parent_edge t k i hedgeparent
    have hfun : ((D.face t).boundary k).map = e ∘ (AffineMap.lineMap s u) := by
      funext v
      rw [hparam]
      simp only [e, Function.comp_apply, AffineMap.lineMap_apply_ring']
      congr 2
      ring
    have hedge : ((D.face t).boundary k).map '' Icc (0 : ℝ) 1 = e '' uIcc s u := by
      rw [hfun, image_comp, ← segment_eq_image_lineMap, segment_eq_uIcc]
    have hopen : ((D.face t).boundary k).map '' Ioo (0 : ℝ) 1 =
        e '' Ioo (min s u) (max s u) := by
      rw [hfun, image_comp, ← openSegment_eq_image_lineMap, openSegment_eq_Ioo' hsu]
    have houtside (v : ℝ) (hvS : e v ∈ S) : v ∉ Ioo (min s u) (max s u) := by
      intro hv
      have hd := D.open_boundary_avoids_marks t k
      rw [disjoint_left] at hd
      apply hd ?_ hvS
      rw [hopen]
      exact mem_image_of_mem e hv
    have hmina : min a c ∉ Ioo (min s u) (max s u) := by
      by_cases hac : a ≤ c
      · simpa only [min_eq_left hac] using houtside a hmarka
      · simpa only [min_eq_right (le_of_not_ge hac)] using houtside c hmarkc
    have hmaxa : max a c ∉ Ioo (min s u) (max s u) := by
      by_cases hac : a ≤ c
      · simpa only [max_eq_right hac] using houtside c hmarkc
      · simpa only [max_eq_left (le_of_not_ge hac)] using houtside a hmarka
    have hinter : (D.face t).carrier ∩ (e '' uIcc a c) =
        e '' (uIcc s u ∩ uIcc a c) := by
      calc
        _ = ((D.face t).carrier ∩
            (F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)))) ∩
            (e '' uIcc a c) := by
          ext q
          exact ⟨fun h => ⟨⟨h.1, hsmall h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
        _ = e '' (uIcc s u ∩ uIcc a c) := by
          rw [hk, hedge, ← (D.parent_edge_injective i).image_inter
            (boundaryIntersections_uIcc_subset hs hu) (boundaryIntersections_uIcc_subset ha hc)]
    have hstart : e s = F (meshTriangleBasis D.mesh t (k.succAbove 0)) := by
      have heq : ((D.face t).boundary k).map 0 = e s := by simpa [e] using hparam 0
      rw [← heq]
      simp [D.boundary_map, affineChartSegment]
    have hend : e u = F (meshTriangleBasis D.mesh t (k.succAbove 1)) := by
      have heq : ((D.face t).boundary k).map 1 = e u := by simpa [e] using hparam 1
      rw [← heq]
      simp [D.boundary_map, affineChartSegment]
    have hpoint (v : ℝ) (hv : v = s ∨ v = u)
        (hvinter : uIcc s u ∩ uIcc a c ⊆ {v}) :
        ∃ j : Fin 3, (D.face t).carrier ∩ (e '' uIcc a c) ⊆
          {F (meshTriangleBasis D.mesh t j)} := by
      rcases hv with rfl | rfl
      · refine ⟨k.succAbove 0, ?_⟩
        rw [hinter]
        rintro q ⟨w, hw, rfl⟩
        rw [mem_singleton_iff.mp (hvinter hw), hstart]
        exact mem_singleton _
      · refine ⟨k.succAbove 1, ?_⟩
        rw [hinter]
        rintro q ⟨w, hw, rfl⟩
        rw [mem_singleton_iff.mp (hvinter hw), hend]
        exact mem_singleton _
    rcases boundaryIntersections_interval (min s u) (max s u) (min a c) (max a c)
      hmina hmaxa with hwhole | hleft | hright
    · left
      refine ⟨k, ?_⟩
      change uIcc s u ⊆ uIcc a c at hwhole
      rw [hinter, hedge, inter_eq_left.mpr hwhole]
    · exact Or.inr (hpoint (min s u) (by by_cases h : s ≤ u <;> simp [min_def, h]) hleft)
    · exact Or.inr (hpoint (max s u) (by by_cases h : s ≤ u <;> simp [max_def, h]) hright)
  · right
    exact ⟨j, fun q hq => hj ⟨hq.1, hsmall hq.2⟩⟩

end SmoothTriangleBoundarySubdivision
end PoincareConjecture.Topology.Surface
