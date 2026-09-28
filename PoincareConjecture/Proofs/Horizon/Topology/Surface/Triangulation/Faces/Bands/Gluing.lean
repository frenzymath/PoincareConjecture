import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.ObliqueFrontier
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Gluing.Frontier

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

omit [T2Space M] in

theorem SmoothEdge.mem_interior_union_of_local_frontiers
    (e : SmoothEdge M) (p : M)
    (hinj : InjOn e.map (Icc (0 : ℝ) 1))
    (hchart : e.map '' Icc (0 : ℝ) 1 ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source)
    (hthin : interior (e.map '' Icc (0 : ℝ) 1) = ∅)
    {A B N : Set M} {t : ℝ}
    (hA : IsClosed A) (hB : IsClosed B)
    (hAregular : closure (interior A) = A) (hBregular : closure (interior B) = B)
    (hdisjoint : Disjoint (interior A) (interior B))
    (ht : t ∈ Ioo (0 : ℝ) 1) (htA : e.map t ∈ A) (htB : e.map t ∈ B)
    (hN : N ∈ 𝓝 (e.map t))
    (hfrontA : N ∩ frontier A ⊆ e.map '' Icc (0 : ℝ) 1)
    (hfrontB : N ∩ frontier B ⊆ e.map '' Icc (0 : ℝ) 1) :
    e.map t ∈ interior (A ∪ B) := by
  obtain ⟨W, U, V, hWopen, htW, hWsub, _, _, hU, hV, _, hpartition, _⟩ :=
    e.exists_two_sided_neighborhood p hinj hchart ht hN
  have hdense : Dense (e.map '' Icc (0 : ℝ) 1)ᶜ :=
    interior_eq_empty_iff_dense_compl.mp hthin
  have hWdense : W ⊆ closure (U ∪ V) := by
    rw [← hpartition]
    intro q hq
    apply mem_closure_iff.mpr
    intro O hO hqO
    obtain ⟨z, ⟨hzO, hzW⟩, hzK⟩ :=
      hdense.inter_open_nonempty (O ∩ W) (hO.inter hWopen) ⟨q, hqO, hq⟩
    exact ⟨z, hzO, hzW, hzK⟩
  have hcover := Poincare.Topology.subset_union_of_two_sided_neighborhood
    hA hB hAregular hBregular hdisjoint htA htB (hWopen.mem_nhds htW)
    hpartition hU.isConnected.isPreconnected hV.isConnected.isPreconnected
    hU.nonempty hV.nonempty hWdense
    (fun _ hq => hfrontA ⟨hWsub hq.1, hq.2⟩)
    (fun _ hq => hfrontB ⟨hWsub hq.1, hq.2⟩)
  exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (hWopen.mem_nhds htW) hcover)

namespace ObliqueBandFaces

variable {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

theorem closure_interior_carrier : closure (interior B.carrier) = B.carrier := by
  apply subset_antisymm (closure_minimal interior_subset B.isClosed_carrier)
  let S : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1
  let T : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let H : ℝ × ℝ → EuclideanSpace ℝ (Fin 2) :=
    fun q => collarParameterEquiv.symm (q.1, q.2 * B.height q.1)
  have hclosure : closure S = T := by
    simp only [S, T, closure_prod_eq, closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]
  have hH : ContinuousOn H T := collarParameterEquiv.symm.continuous.continuousOn.comp
    (continuousOn_fst.prodMk (continuousOn_snd.mul
      (B.continuousOn_height.comp continuousOn_fst (fun _ hq => hq.1)))) (fun _ _ => mem_univ _)
  have hHT : MapsTo H T B.band := by
    intro q hq
    rw [B.band_eq_subgraph]
    simp only [H, mem_ofPred_eq, collarParameterEquiv.apply_symm_apply]
    exact ⟨hq.1, mul_nonneg hq.2.1 (B.height_pos hq.1).le,
      (mul_le_mul_of_nonneg_right hq.2.2 (B.height_pos hq.1).le).trans_eq (one_mul _)⟩
  have hHS : MapsTo H S B.openBand := by
    intro q hq
    have ht : q.1 ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hq.1
    exact ⟨hq.1, mul_pos hq.2.1 (B.height_pos ht),
      (mul_lt_mul_of_pos_right hq.2.2 (B.height_pos ht)).trans_eq (one_mul _)⟩
  have hmap : ContinuousOn (B.coordinates ∘ H) T :=
    B.coordinates.continuousOn.comp hH (fun _ hq => B.band_subset_source (hHT hq))
  have hmapS : (B.coordinates ∘ H) '' S ⊆ interior B.carrier := by
    rintro z ⟨q, hq, rfl⟩
    exact B.openBand_image_subset_interior ⟨H q, hHS hq, rfl⟩
  intro z hz
  rw [B.carrier_eq_image] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  have hq' := hq
  rw [B.band_eq_subgraph] at hq'
  let w : ℝ × ℝ := ((collarParameterEquiv q).1,
    (collarParameterEquiv q).2 / B.height (collarParameterEquiv q).1)
  have hw : w ∈ T := ⟨hq'.1,
    div_nonneg hq'.2.1 (B.height_pos hq'.1).le,
    (div_le_one (B.height_pos hq'.1)).mpr hq'.2.2⟩
  have hHw : H w = q := by
    change collarParameterEquiv.symm ((collarParameterEquiv q).1,
      (collarParameterEquiv q).2 / B.height (collarParameterEquiv q).1 *
        B.height (collarParameterEquiv q).1) = q
    rw [div_mul_cancel₀ _ (B.height_pos hq'.1).ne']
    exact collarParameterEquiv.symm_apply_apply q
  have hz : B.coordinates q ∈ (B.coordinates ∘ H) '' closure S :=
    ⟨w, hclosure.symm ▸ hw, by simp only [Function.comp_apply, hHw]⟩
  exact closure_mono hmapS ((hclosure ▸ hmap).image_closure hz)

noncomputable def endpointEdge (right : Bool) : SmoothEdge M :=
  if right then (B.pair B.lastCell).lower.boundary 0
  else (B.pair B.firstCell).upper.boundary 2

private def endpoint (right : Bool) : ℝ := if right then 1 else 0

private theorem endpoint_mem (right : Bool) : endpoint right ∈ Icc (0 : ℝ) 1 := by
  cases right <;> simp [endpoint]

omit [T2Space M] in
theorem endpointEdge_map (right : Bool) (t : ℝ) :
    (B.endpointEdge right).map t = B.coordinates
      (collarParameterEquiv.symm (endpoint right, t * B.height (endpoint right))) := by
  cases right
  · change ((B.pair B.firstCell).upper.boundary 2).map t = _
    rw [(B.pair B.firstCell).left_edge]
    have hfirst : B.firstCell.castSucc = 0 := rfl
    have hh := (B.upperGraph_endpoints B.firstCell).1
    rw [hfirst, B.cut_first, B.interface.height_first] at hh
    change B.coordinates (collarParameterEquiv.symm
      (B.cut B.firstCell.castSucc, 0 + t * (B.upperGraph B.firstCell
        (B.cut B.firstCell.castSucc) - 0))) = _
    simp only [hfirst, B.cut_first, hh, endpoint, Bool.false_eq_true, ↓reduceIte,
      B.height_zero, sub_zero, zero_add]
  · change ((B.pair B.lastCell).lower.boundary 0).map t = _
    rw [(B.pair B.lastCell).right_edge]
    have hlast : B.lastCell.succ = Fin.last B.interface.count := by
      apply Fin.ext
      dsimp [lastCell]
      have hn := B.interface.count_pos
      omega
    have hh := (B.upperGraph_endpoints B.lastCell).2
    rw [hlast, B.cut_last, B.interface.height_last] at hh
    change B.coordinates (collarParameterEquiv.symm
      (B.cut B.lastCell.succ, 0 + t * (B.upperGraph B.lastCell
        (B.cut B.lastCell.succ) - 0))) = _
    simp only [hlast, B.cut_last, hh, endpoint, ↓reduceIte,
      B.height_one, sub_zero, zero_add]

omit [T2Space M] in
private theorem height_point_mem_band {x z : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hz : z ∈ Icc (0 : ℝ) (B.height x)) :
    collarParameterEquiv.symm (x, z) ∈ B.band := by
  rw [B.band_eq_subgraph]
  simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply, mem_Icc] using And.intro hx hz

omit [T2Space M] in
private theorem scaled_endpoint_mem_band (right : Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    collarParameterEquiv.symm (endpoint right, t * B.height (endpoint right)) ∈ B.band :=
  B.height_point_mem_band (endpoint_mem right)
    ⟨mul_nonneg ht.1 (B.height_pos (endpoint_mem right)).le,
      (mul_le_mul_of_nonneg_right ht.2 (B.height_pos (endpoint_mem right)).le).trans_eq (one_mul _)⟩

omit [T2Space M] in
theorem endpointEdge_injective (right : Bool) :
    InjOn (B.endpointEdge right).map (Icc (0 : ℝ) 1) := by
  intro t ht s hs heq
  rw [B.endpointEdge_map, B.endpointEdge_map] at heq
  have hq := B.coordinates.injOn (B.band_subset_source (B.scaled_endpoint_mem_band right ht))
    (B.band_subset_source (B.scaled_endpoint_mem_band right hs)) heq
  have hm := congrArg (fun q => (collarParameterEquiv q).2) hq
  simp only [collarParameterEquiv.apply_symm_apply] at hm
  exact (mul_left_inj' (B.height_pos (endpoint_mem right)).ne').mp hm

omit [T2Space M] in
theorem endpointEdge_image (right : Bool) :
    (B.endpointEdge right).map '' Icc (0 : ℝ) 1 =
      if right then B.rightCut else B.leftCut := by
  cases right
  · exact B.left_edge_image
  · exact B.right_edge_image

omit [T2Space M] in
theorem endpointEdge_subset_frontier (right : Bool) :
    (B.endpointEdge right).map '' Icc (0 : ℝ) 1 ⊆ frontier B.carrier := by
  rw [B.endpointEdge_image]
  cases right
  · exact fun _ h => B.outer_boundaries_subset_frontier (Or.inl (Or.inr h))
  · exact fun _ h => B.outer_boundaries_subset_frontier (Or.inr h)

omit [T2Space M] in
theorem isCompact_lowerArc : IsCompact B.lowerArc := by
  rw [lowerArc, ← B.lower_edges_image]
  exact isCompact_iUnion fun i => isCompact_Icc.image_of_continuousOn
    ((B.pair i).lower.boundary 2).smooth.continuousOn

omit [T2Space M] in
theorem isCompact_polygonalTop : IsCompact B.polygonalTop := by
  apply isCompact_iUnion
  intro i
  rw [← B.upper_edge_image]
  exact isCompact_Icc.image_of_continuousOn ((B.pair i).upper.boundary 0).smooth.continuousOn

omit [T2Space M] in
private theorem bottom_image :
    (fun t => B.coordinates (collarParameterEquiv.symm (t, 0))) '' Icc (0 : ℝ) 1 =
      B.lowerArc := by
  have hab : a ≤ b := by
    simpa only [B.cuts.A_zero, B.cuts.B_zero] using (B.cuts.separated 0
      ⟨by linarith [B.cuts.radius_pos], B.cuts.radius_pos⟩).le
  have hi : (fun t : ℝ => a + t * (b - a)) '' Icc (0 : ℝ) 1 = Icc a b := by
    simpa using
      ((continuous_const : Continuous (fun _ : ℝ => a)).add
        (continuous_id.mul_const (b - a))).continuousOn.image_Icc_of_monotoneOn
        (zero_le_one : (0 : ℝ) ≤ 1) (fun x _ y _ hxy =>
          add_le_add_right (mul_le_mul_of_nonneg_right hxy (sub_nonneg.mpr hab)) a)
  rw [lowerArc, ← hi, image_image]
  exact image_congr (fun t _ => B.coordinates_bottom t)

omit [T2Space M] in
private theorem endpointEdge_avoids_other_boundaries (right : Bool) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (B.endpointEdge right).map t ∉ B.lowerArc ∪ B.polygonalTop ∪
      ((B.endpointEdge (!right)).map '' Icc (0 : ℝ) 1) := by
  have hsource := B.band_subset_source (B.scaled_endpoint_mem_band right (Ioo_subset_Icc_self ht))
  have hcoord {x z : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
      (hz : z ∈ Icc (0 : ℝ) (B.height x))
      (heq : B.coordinates (collarParameterEquiv.symm (x, z)) = (B.endpointEdge right).map t) :
      x = endpoint right ∧ z = t * B.height (endpoint right) := by
    rw [B.endpointEdge_map] at heq
    have hq := B.coordinates.injOn (B.band_subset_source (B.height_point_mem_band hx hz))
      hsource heq
    have hpair := congrArg collarParameterEquiv hq
    simp only [collarParameterEquiv.apply_symm_apply, Prod.mk.injEq] at hpair
    exact hpair
  rintro ((hlower | hupper) | hother)
  · rw [← B.bottom_image] at hlower
    obtain ⟨x, hx, heq⟩ := hlower
    have h := (hcoord hx ⟨le_rfl, (B.height_pos hx).le⟩ heq).2
    exact (mul_pos ht.1 (B.height_pos (endpoint_mem right))).ne h
  · rw [← B.height_graph_image] at hupper
    obtain ⟨x, hx, heq⟩ := hupper
    obtain ⟨hxend, hz⟩ := hcoord hx ⟨(B.height_pos hx).le, le_rfl⟩ heq
    rw [hxend] at hz
    have hlt := mul_lt_mul_of_pos_right ht.2 (B.height_pos (endpoint_mem right))
    rw [one_mul, ← hz] at hlt
    exact hlt.false
  · obtain ⟨s, hs, heq⟩ := hother
    rw [B.endpointEdge_map] at heq
    have hband := B.scaled_endpoint_mem_band (!right) hs
    have hq := B.coordinates.injOn (B.band_subset_source hband) hsource
      (heq.trans (B.endpointEdge_map right t))
    have hx := congrArg (fun q => (collarParameterEquiv q).1) hq
    cases right <;> norm_num [endpoint] at hx

theorem exists_endpoint_frontier_neighborhood (right : Bool) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ N : Set M, IsOpen N ∧ (B.endpointEdge right).map t ∈ N ∧
      N ∩ frontier B.carrier ⊆ (B.endpointEdge right).map '' Icc (0 : ℝ) 1 := by
  let K := B.lowerArc ∪ B.polygonalTop ∪
    ((B.endpointEdge (!right)).map '' Icc (0 : ℝ) 1)
  have hK : IsCompact K := (B.isCompact_lowerArc.union B.isCompact_polygonalTop).union
    (isCompact_Icc.image_of_continuousOn (B.endpointEdge (!right)).smooth.continuousOn)
  refine ⟨Kᶜ, hK.isClosed.isOpen_compl, B.endpointEdge_avoids_other_boundaries right ht, ?_⟩
  rintro q ⟨hq, hfront⟩
  rw [B.frontier_carrier] at hfront
  rw [B.endpointEdge_image]
  have hnot := hq
  change q ∉ B.lowerArc ∪ B.polygonalTop ∪
    ((B.endpointEdge (!right)).map '' Icc (0 : ℝ) 1) at hnot
  rw [B.endpointEdge_image] at hnot
  cases right <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, mem_union] at hnot hfront ⊢ <;> tauto

theorem endpointEdge_interior_empty (right : Bool) :
    interior ((B.endpointEdge right).map '' Icc (0 : ℝ) 1) = ∅ := by
  apply subset_empty_iff.mp
  rw [← interior_frontier B.isClosed_carrier]
  exact interior_mono (B.endpointEdge_subset_frontier right)

theorem endpointEdge_chart (right : Bool) :
    ∃ p : M, (B.endpointEdge right).map '' Icc (0 : ℝ) 1 ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).source := by
  cases right
  · refine ⟨(B.pair B.firstCell).upper.chart, ?_⟩
    exact ((B.pair B.firstCell).upper.boundary_image_subset_frontier 2).trans
      ((B.pair B.firstCell).upper.isClosed_carrier.frontier_subset.trans
        (B.pair B.firstCell).upper.carrier_subset_chart)
  · refine ⟨(B.pair B.lastCell).lower.chart, ?_⟩
    exact ((B.pair B.lastCell).lower.boundary_image_subset_frontier 0).trans
      ((B.pair B.lastCell).lower.isClosed_carrier.frontier_subset.trans
        (B.pair B.lastCell).lower.carrier_subset_chart)

variable {F' : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo' : ℝ → ℝ} {a' b' ua' wa' ub' wb' ra' rb' : ℝ}
  (B' : ObliqueBandFaces F' lo' a' b' ua' wa' ub' wb' ra' rb')

theorem mem_interior_union_of_shared_endpointCut (right right' : Bool)
    {t s : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hpoint : (B.endpointEdge right).map t = (B'.endpointEdge right').map s)
    (hshared : (B.endpointEdge right).map '' Icc (0 : ℝ) 1 =
      (B'.endpointEdge right').map '' Icc (0 : ℝ) 1)
    (hinter : B.carrier ∩ B'.carrier ⊆ frontier B.carrier) :
    (B.endpointEdge right).map t ∈ interior (B.carrier ∪ B'.carrier) := by
  obtain ⟨N, hN, htN, hfrontN⟩ := B.exists_endpoint_frontier_neighborhood right ht
  obtain ⟨N', hN', hsN', hfrontN'⟩ := B'.exists_endpoint_frontier_neighborhood right' hs
  obtain ⟨p, hchart⟩ := B.endpointEdge_chart right
  have hdisjoint : Disjoint (interior B.carrier) (interior B'.carrier) := by
    apply disjoint_left.mpr
    intro q hq hq'
    exact disjoint_left.mp disjoint_interior_frontier hq
      (hinter ⟨interior_subset hq, interior_subset hq'⟩)
  apply (B.endpointEdge right).mem_interior_union_of_local_frontiers p
    (B.endpointEdge_injective right) hchart (B.endpointEdge_interior_empty right)
    B.isClosed_carrier B'.isClosed_carrier B.closure_interior_carrier B'.closure_interior_carrier
    hdisjoint ht
    (B.isClosed_carrier.frontier_subset (B.endpointEdge_subset_frontier right
      ⟨t, Ioo_subset_Icc_self ht, rfl⟩))
    (hpoint ▸ B'.isClosed_carrier.frontier_subset (B'.endpointEdge_subset_frontier right'
      ⟨s, Ioo_subset_Icc_self hs, rfl⟩))
    ((hN.inter hN').mem_nhds ⟨htN, hpoint ▸ hsN'⟩)
  · exact fun _ hq => hfrontN ⟨hq.1.1, hq.2⟩
  · intro q hq
    rw [hshared]
    exact hfrontN' ⟨hq.1.2, hq.2⟩

theorem shared_endpointCut_subset_interior_union (right right' : Bool)
    (hshared : (B.endpointEdge right).map '' Icc (0 : ℝ) 1 =
      (B'.endpointEdge right').map '' Icc (0 : ℝ) 1)
    (hinter : B.carrier ∩ B'.carrier ⊆ frontier B.carrier) :
    ((B.endpointEdge right).map '' Ioo (0 : ℝ) 1) ∩
      ((B'.endpointEdge right').map '' Ioo (0 : ℝ) 1) ⊆
        interior (B.carrier ∪ B'.carrier) := by
  rintro q ⟨⟨t, ht, rfl⟩, s, hs, heq⟩
  exact B.mem_interior_union_of_shared_endpointCut B' right right' ht hs heq.symm hshared hinter

end ObliqueBandFaces
end PoincareConjecture.Topology.Surface
