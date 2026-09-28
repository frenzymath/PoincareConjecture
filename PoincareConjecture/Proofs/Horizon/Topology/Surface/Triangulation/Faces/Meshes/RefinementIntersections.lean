


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes.BoundaryIntersections
import Mathlib.Topology.Order.IntermediateValue








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

private theorem refinement_segment_image (a b : Plane) :
    affineChartSegment a b '' Icc (0 : ℝ) 1 = affineSegment ℝ a b := by
  unfold affineSegment
  congr 1
  funext t
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]

private theorem refinement_uIcc_subset {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    uIcc a b ⊆ Icc (0 : ℝ) 1 :=
  fun _ hx => ⟨(le_min ha.1 hb.1).trans hx.1, hx.2.trans (max_le ha.2 hb.2)⟩

private theorem refinement_interval_cases (a b c d : ℝ)
    (hc : c ∉ Ioo a b) (hd : d ∉ Ioo a b) :
    Icc a b ⊆ Icc c d ∨ (Icc a b ∩ Icc c d ⊆ {a}) ∨
      (Icc a b ∩ Icc c d ⊆ {b}) := by
  by_cases hca : c ≤ a
  · by_cases hbd : b ≤ d
    · exact Or.inl (fun _ hx => ⟨hca.trans hx.1, hx.2.trans hbd⟩)
    · have hda : d ≤ a := le_of_not_gt (fun had => hd ⟨had, lt_of_not_ge hbd⟩)
      exact Or.inr (Or.inl (fun _ hx => mem_singleton_iff.mpr
        (le_antisymm (hx.2.2.trans hda) hx.1.1)))
  · have hbc : b ≤ c := le_of_not_gt (fun hcb => hc ⟨lt_of_not_ge hca, hcb⟩)
    exact Or.inr (Or.inr (fun _ hx => mem_singleton_iff.mpr
      (le_antisymm hx.1.2 (hbc.trans hx.2.1))))

private theorem refinement_interval_compatible {a b c d : ℝ} (hab : a ≠ b)
    (hca : c ∉ Ioo (min a b) (max a b)) (hda : d ∉ Ioo (min a b) (max a b))
    (hac : a ∉ Ioo (min c d) (max c d)) (hbc : b ∉ Ioo (min c d) (max c d)) :
    uIcc a b = uIcc c d ∨
      (uIcc a b ∩ uIcc c d ⊆ {a}) ∨ (uIcc a b ∩ uIcc c d ⊆ {b}) := by
  have hmin {x y l r : ℝ} (hx : x ∉ Ioo l r) (hy : y ∉ Ioo l r) :
      min x y ∉ Ioo l r := by
    by_cases h : x ≤ y
    · simpa only [min_eq_left h] using hx
    · simpa only [min_eq_right (le_of_not_ge h)] using hy
  have hmax {x y l r : ℝ} (hx : x ∉ Ioo l r) (hy : y ∉ Ioo l r) :
      max x y ∉ Ioo l r := by
    by_cases h : x ≤ y
    · simpa only [max_eq_right h] using hy
    · simpa only [max_eq_left (le_of_not_ge h)] using hx
  rcases refinement_interval_cases (min a b) (max a b) (min c d) (max c d)
      (hmin hca hda) (hmax hca hda) with hsub | hleft | hright
  · change uIcc a b ⊆ uIcc c d at hsub
    rcases refinement_interval_cases (min c d) (max c d) (min a b) (max a b)
        (hmin hac hbc) (hmax hac hbc) with hrev | hleft | hright
    · exact Or.inl (subset_antisymm hsub hrev)
    · have ha := mem_singleton_iff.mp (hleft ⟨hsub left_mem_uIcc, left_mem_uIcc⟩)
      have hb := mem_singleton_iff.mp (hleft ⟨hsub right_mem_uIcc, right_mem_uIcc⟩)
      exact False.elim (hab (ha.trans hb.symm))
    · have ha := mem_singleton_iff.mp (hright ⟨hsub left_mem_uIcc, left_mem_uIcc⟩)
      have hb := mem_singleton_iff.mp (hright ⟨hsub right_mem_uIcc, right_mem_uIcc⟩)
      exact False.elim (hab (ha.trans hb.symm))
  · by_cases h : a ≤ b
    · change uIcc a b ∩ uIcc c d ⊆ {min a b} at hleft
      exact Or.inr (Or.inl (by simpa only [min_eq_left h] using hleft))
    · change uIcc a b ∩ uIcc c d ⊆ {min a b} at hleft
      exact Or.inr (Or.inr (by simpa only [min_eq_right (le_of_not_ge h)] using hleft))
  · by_cases h : a ≤ b
    · change uIcc a b ∩ uIcc c d ⊆ {max a b} at hright
      exact Or.inr (Or.inr (by simpa only [max_eq_right h] using hright))
    · change uIcc a b ∩ uIcc c d ⊆ {max a b} at hright
      exact Or.inr (Or.inl (by simpa only [max_eq_left (le_of_not_ge h)] using hright))

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M]
  {F G : OpenPartialHomeomorph Plane M} {b c : AffineBasis (Fin 3) ℝ Plane}
  {S T : Finset M}

namespace SmoothTriangleBoundarySubdivision

variable (R : SmoothTriangleBoundarySubdivision F b S)

omit [T2Space M] in
theorem carrier_subset_parent (t : R.mesh.Triangle) :
    (R.face t).carrier ⊆ F '' convexHull ℝ (range b) := by
  rw [R.carrier_eq, ← R.support]
  exact image_mono (meshTriangleBasis_subset_support R.mesh t)

omit [T2Space M] in
theorem child_vertex_mem_frontier (t : R.mesh.Triangle) (j : Fin 3) :
    F (meshTriangleBasis R.mesh t j) ∈ frontier (R.face t).carrier := by
  rw [(R.face t).boundary_carrier]
  fin_cases j
  · refine mem_iUnion.mpr ⟨1, 0, by simp, ?_⟩
    simp [R.boundary_map, affineChartSegment]
  · refine mem_iUnion.mpr ⟨0, 0, by simp, ?_⟩
    simp [R.boundary_map, affineChartSegment]
  · refine mem_iUnion.mpr ⟨0, 1, by simp, ?_⟩
    simp [R.boundary_map, affineChartSegment]

omit [T2Space M] in
theorem marked_point_mem_child_frontier {q : M} (hq : q ∈ S) (t : R.mesh.Triangle)
    (hqt : q ∈ (R.face t).carrier) : q ∈ frontier (R.face t).carrier := by
  obtain ⟨z, ⟨j, rfl⟩, rfl⟩ := R.mark_vertex q hq t hqt
  exact R.child_vertex_mem_frontier t j

omit [T2Space M] in
theorem child_inter_parent_edge_subset_frontier (t : R.mesh.Triangle) (i : Fin 3) :
    (R.face t).carrier ∩ (F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1))) ⊆
      frontier (R.face t).carrier := by
  rcases R.carrier_inter_parent_edge t i with ⟨k, hk⟩ | ⟨j, hj⟩
  · rw [hk]
    exact (R.face t).boundary_image_subset_frontier k
  · intro q hq
    rw [mem_singleton_iff.mp (hj hq)]
    exact R.child_vertex_mem_frontier t j

include R in
omit [T2Space M] in


theorem edge_interval_of_subset_parent_edge (i : Fin 3) (edge : SmoothEdge M)
    (hinj : InjOn edge.map (Icc (0 : ℝ) 1))
    (hsub : edge.map '' Icc (0 : ℝ) 1 ⊆
      F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1))) :
    ∃ a d : ℝ, a ∈ Icc (0 : ℝ) 1 ∧ d ∈ Icc (0 : ℝ) 1 ∧ a ≠ d ∧
      F (affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) a) = edge.map 0 ∧
      F (affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) d) = edge.map 1 ∧
      edge.map '' Icc (0 : ℝ) 1 =
        (F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1))) '' uIcc a d ∧
      edge.map '' Ioo (0 : ℝ) 1 =
        (F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1))) ''
          Ioo (min a d) (max a d) := by
  let e : ℝ → M := F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1))
  let param : M → ℝ := fun q => b.coord (i.succAbove 1) (F.symm q)
  have hsrc (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) v ∈ F.source := by
    apply R.parent_source_subset
    apply segment_subset_convexHull (mem_range_self (i.succAbove 0))
      (mem_range_self (i.succAbove 1))
    rw [← affineSegment_eq_segment, ← refinement_segment_image]
    exact mem_image_of_mem _ hv
  have hparam (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : param (e v) = v := by
    dsimp only [param, e, Function.comp_apply]
    rw [F.left_inv (hsrc v hv)]
    have hline : affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) v =
        AffineMap.lineMap (b (i.succAbove 0)) (b (i.succAbove 1)) v := by
      simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]
    have hne : i.succAbove 1 ≠ i.succAbove 0 := by
      intro h
      have h10 : (1 : Fin 2) = 0 := Fin.succAbove_right_injective h
      norm_num at h10
    rw [hline, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring,
      b.coord_apply_ne hne, b.coord_apply_eq]
    ring
  have hsub' : edge.map '' Icc (0 : ℝ) 1 ⊆ e '' Icc (0 : ℝ) 1 := by
    intro q hq
    obtain ⟨z, hz, hzq⟩ := hsub hq
    rw [← refinement_segment_image] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact ⟨v, hv, hzq⟩
  let f : ℝ → ℝ := param ∘ edge.map
  have hf (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      f v ∈ Icc (0 : ℝ) 1 ∧ e (f v) = edge.map v := by
    obtain ⟨w, hw, heq⟩ := hsub' (mem_image_of_mem _ hv)
    have hfw : f v = w := by change param (edge.map v) = w; rw [← heq, hparam w hw]
    exact ⟨hfw ▸ hw, by rw [hfw, heq]⟩
  have htarget (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : edge.map v ∈ F.target := by
    rw [← (hf v hv).2]
    exact F.map_source (hsrc (f v) (hf v hv).1)
  have hcont : ContinuousOn f (Icc (0 : ℝ) 1) :=
    (continuous_barycentric_coord b (i.succAbove 1)).comp_continuousOn
      (F.symm.continuousOn.comp edge.smooth.continuousOn htarget)
  have hfi : InjOn f (Icc (0 : ℝ) 1) := by
    intro s hs t ht heq
    apply hinj hs ht
    rw [← (hf s hs).2, ← (hf t ht).2, heq]
  have hne : f 0 ≠ f 1 := by
    intro heq
    have h01 := hfi (by simp : (0 : ℝ) ∈ Icc 0 1) (by simp : (1 : ℝ) ∈ Icc 0 1) heq
    norm_num at h01
  have hclosed : f '' Icc (0 : ℝ) 1 = uIcc (f 0) (f 1) := by
    rcases hcont.strictMonoOn_of_injOn_Icc' (by norm_num) hfi with hmono | hanti
    · have hle := (hmono (by simp) (by simp) (by norm_num : (0 : ℝ) < 1)).le
      rw [hcont.image_Icc_of_monotoneOn (by norm_num) hmono.monotoneOn, uIcc_of_le hle]
    · have hle := (hanti (by simp) (by simp) (by norm_num : (0 : ℝ) < 1)).le
      rw [hcont.image_Icc_of_antitoneOn (by norm_num) hanti.antitoneOn, uIcc_of_ge hle]
  have hopen : f '' Ioo (0 : ℝ) 1 = Ioo (min (f 0) (f 1)) (max (f 0) (f 1)) := by
    rcases hcont.strictMonoOn_of_injOn_Icc' (by norm_num) hfi with hmono | hanti
    · have hle := (hmono (by simp) (by simp) (by norm_num : (0 : ℝ) < 1)).le
      rw [hcont.image_Ioo_of_strictMonoOn (by norm_num) hmono, min_eq_left hle, max_eq_right hle]
    · have hle := (hanti (by simp) (by simp) (by norm_num : (0 : ℝ) < 1)).le
      rw [hcont.image_Ioo_of_strictAntiOn (by norm_num) hanti, min_eq_right hle, max_eq_left hle]
  refine ⟨f 0, f 1, (hf 0 (by simp)).1, (hf 1 (by simp)).1, hne,
    (hf 0 (by simp)).2, (hf 1 (by simp)).2, ?_, ?_⟩
  · calc
      edge.map '' Icc (0 : ℝ) 1 = (e ∘ f) '' Icc (0 : ℝ) 1 :=
        image_congr (fun v hv => (hf v hv).2.symm)
      _ = e '' uIcc (f 0) (f 1) := by rw [image_comp, hclosed]
  · calc
      edge.map '' Ioo (0 : ℝ) 1 = (e ∘ f) '' Ioo (0 : ℝ) 1 :=
        image_congr (fun v hv => (hf v ⟨hv.1.le, hv.2.le⟩).2.symm)
      _ = e '' Ioo (min (f 0) (f 1)) (max (f 0) (f 1)) := by rw [image_comp, hopen]

omit [T2Space M] in
private theorem vertex_of_subsingleton_marked_set (t : R.mesh.Triangle) {A : Set M}
    (hA : A.Subsingleton) (hsub : A ⊆ (R.face t).carrier) (hmarks : A ⊆ (S : Set M)) :
    ∃ j : Fin 3, A ⊆ {F (meshTriangleBasis R.mesh t j)} := by
  by_cases hne : A.Nonempty
  · obtain ⟨q, hq⟩ := hne
    obtain ⟨z, ⟨j, rfl⟩, hj⟩ := R.mark_vertex q (hmarks hq) t (hsub hq)
    exact ⟨j, fun x hx => mem_singleton_iff.mpr ((hA hx hq).trans hj.symm)⟩
  · exact ⟨0, by simp [not_nonempty_iff_eq_empty.mp hne]⟩

variable (Q : SmoothTriangleBoundarySubdivision G c T)



theorem boundary_intersections_of_common_parent_edge
    (t : R.mesh.Triangle) (u : Q.mesh.Triangle) (k l i : Fin 3)
    (hR : ((R.face t).boundary k).map '' Icc (0 : ℝ) 1 ⊆
      F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)))
    (hQ : ((Q.face u).boundary l).map '' Icc (0 : ℝ) 1 ⊆
      F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)))
    (hR0 : ((R.face t).boundary k).map 0 ∈ T) (hR1 : ((R.face t).boundary k).map 1 ∈ T)
    (hQ0 : ((Q.face u).boundary l).map 0 ∈ S) (hQ1 : ((Q.face u).boundary l).map 1 ∈ S) :
    ((R.face t).boundary k).map '' Icc (0 : ℝ) 1 =
        ((Q.face u).boundary l).map '' Icc (0 : ℝ) 1 ∨
      ((((R.face t).boundary k).map '' Icc (0 : ℝ) 1) ∩
        (((Q.face u).boundary l).map '' Icc (0 : ℝ) 1) ⊆
          {F (meshTriangleBasis R.mesh t (k.succAbove 0))}) ∨
      ((((R.face t).boundary k).map '' Icc (0 : ℝ) 1) ∩
        (((Q.face u).boundary l).map '' Icc (0 : ℝ) 1) ⊆
          {F (meshTriangleBasis R.mesh t (k.succAbove 1))}) := by
  let e : ℝ → M := F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1))
  obtain ⟨a, d, ha, hd, had, ha0, hd1, hRclosed, hRopen⟩ :=
    R.edge_interval_of_subset_parent_edge i ((R.face t).boundary k) (R.boundary_injective t k) hR
  obtain ⟨a', d', ha', hd', _, ha0', hd1', hQclosed, hQopen⟩ :=
    R.edge_interval_of_subset_parent_edge i ((Q.face u).boundary l) (Q.boundary_injective u l) hQ
  change e a = _ at ha0
  change e d = _ at hd1
  change e a' = _ at ha0'
  change e d' = _ at hd1'
  have outsideR (v : ℝ) (hvS : e v ∈ S) : v ∉ Ioo (min a d) (max a d) := by
    intro hv
    have hmem : e v ∈ ((R.face t).boundary k).map '' Ioo (0 : ℝ) 1 := by
      rw [hRopen]
      exact mem_image_of_mem e hv
    exact disjoint_left.mp (R.open_boundary_avoids_marks t k) hmem hvS
  have outsideQ (v : ℝ) (hvT : e v ∈ T) : v ∉ Ioo (min a' d') (max a' d') := by
    intro hv
    have hmem : e v ∈ ((Q.face u).boundary l).map '' Ioo (0 : ℝ) 1 := by
      rw [hQopen]
      exact mem_image_of_mem e hv
    exact disjoint_left.mp (Q.open_boundary_avoids_marks u l) hmem hvT
  have hcases := refinement_interval_compatible had
    (outsideR a' (ha0' ▸ hQ0)) (outsideR d' (hd1' ▸ hQ1))
    (outsideQ a (ha0 ▸ hR0)) (outsideQ d (hd1 ▸ hR1))
  have hinter : (((R.face t).boundary k).map '' Icc (0 : ℝ) 1) ∩
      (((Q.face u).boundary l).map '' Icc (0 : ℝ) 1) =
      e '' (uIcc a d ∩ uIcc a' d') := by
    rw [hRclosed, hQclosed, ← (R.parent_edge_injective i).image_inter
      (refinement_uIcc_subset ha hd) (refinement_uIcc_subset ha' hd')]
  rcases hcases with heq | hleft | hright
  · exact Or.inl (by rw [hRclosed, hQclosed, heq])
  · right
    left
    rw [hinter]
    rintro q ⟨v, hv, rfl⟩
    rw [mem_singleton_iff.mp (hleft hv), ha0]
    simp [R.boundary_map, affineChartSegment]
  · right
    right
    rw [hinter]
    rintro q ⟨v, hv, rfl⟩
    rw [mem_singleton_iff.mp (hright hv), hd1]
    simp [R.boundary_map, affineChartSegment]

omit [T2Space M] in
theorem child_vertex_mem_marks_of_mem_parent_frontier (t : R.mesh.Triangle) (v : Fin 3)
    (hv : F (meshTriangleBasis R.mesh t v) ∈ F '' frontier (convexHull ℝ (range b))) :
    F (meshTriangleBasis R.mesh t v) ∈ S := by
  have hmem : F (meshTriangleBasis R.mesh t v) ∈
      (⋃ t, F '' range (meshTriangleBasis R.mesh t)) ∩
        (F '' frontier (convexHull ℝ (range b))) :=
    ⟨mem_iUnion.mpr ⟨t, mem_image_of_mem F (mem_range_self v)⟩, hv⟩
  rwa [R.boundary_vertices] at hmem



theorem cross_intersections_of_shared_parent_subsegment
    (i j : Fin 3) (a d a' d' : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hd : d ∈ Icc (0 : ℝ) 1)
    (ha' : a' ∈ Icc (0 : ℝ) 1) (hd' : d' ∈ Icc (0 : ℝ) 1)
    (hmarka : F (affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) a) ∈ S)
    (hmarkd : F (affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) d) ∈ S)
    (hmarka' : G (affineChartSegment (c (j.succAbove 0)) (c (j.succAbove 1)) a') ∈ T)
    (hmarkd' : G (affineChartSegment (c (j.succAbove 0)) (c (j.succAbove 1)) d') ∈ T)
    (hparentsF : (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c)) =
      (F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1))) '' uIcc a d)
    (hparentsG : (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c)) =
      (G ∘ affineChartSegment (c (j.succAbove 0)) (c (j.succAbove 1))) '' uIcc a' d')
    (hsync : (S : Set M) ∩ (G '' convexHull ℝ (range c)) =
      (T : Set M) ∩ (F '' convexHull ℝ (range b)))
    (t : R.mesh.Triangle) (u : Q.mesh.Triangle) :
    ((∃ k l : Fin 3,
        (R.face t).carrier ∩ (Q.face u).carrier =
          ((R.face t).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((R.face t).boundary k).map '' Icc (0 : ℝ) 1 =
          ((Q.face u).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ v : Fin 3, (R.face t).carrier ∩ (Q.face u).carrier ⊆
        {F (meshTriangleBasis R.mesh t v)}) ∧
    (R.face t).carrier ∩ (Q.face u).carrier ⊆
      frontier (R.face t).carrier ∩ frontier (Q.face u).carrier := by
  let H := (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c))
  have hHF : H ⊆ F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) := by
    dsimp only [H]
    rw [hparentsF, ← refinement_segment_image, image_image]
    exact image_mono (refinement_uIcc_subset ha hd)
  have hHG : H ⊆ G '' affineSegment ℝ (c (j.succAbove 0)) (c (j.succAbove 1)) := by
    dsimp only [H]
    rw [hparentsG, ← refinement_segment_image, image_image]
    exact image_mono (refinement_uIcc_subset ha' hd')
  have hGfront : H ⊆ G '' frontier (convexHull ℝ (range c)) := by
    apply hHG.trans (image_mono ?_)
    rw [frontier_convexHull_affineBasis_fin3_segments]
    exact subset_iUnion_of_subset j (subset_refl _)
  have hcross : (R.face t).carrier ∩ (Q.face u).carrier ⊆ H :=
    fun _ hq => ⟨R.carrier_subset_parent t hq.1, Q.carrier_subset_parent u hq.2⟩
  have hfront : (R.face t).carrier ∩ (Q.face u).carrier ⊆
      frontier (R.face t).carrier ∩ frontier (Q.face u).carrier := by
    intro q hq
    exact ⟨R.child_inter_parent_edge_subset_frontier t i ⟨hq.1, hHF (hcross hq)⟩,
      Q.child_inter_parent_edge_subset_frontier u j ⟨hq.2, hHG (hcross hq)⟩⟩
  have hStoT {q : M} (hq : q ∈ S) (hH : q ∈ H) : q ∈ T := by
    have hp : q ∈ (S : Set M) ∩ (G '' convexHull ℝ (range c)) := ⟨hq, hH.2⟩
    rw [hsync] at hp
    exact hp.1
  have hTtoS {q : M} (hq : q ∈ T) (hH : q ∈ H) : q ∈ S := by
    have hp : q ∈ (T : Set M) ∩ (F '' convexHull ℝ (range b)) := ⟨hq, hH.1⟩
    rw [← hsync] at hp
    exact hp.1
  refine ⟨?_, hfront⟩
  have hR := R.carrier_inter_marked_parent_subsegment t i a d ha hd hmarka hmarkd
  have hQ := Q.carrier_inter_marked_parent_subsegment u j a' d' ha' hd' hmarka' hmarkd'
  rw [← hparentsF] at hR
  rw [← hparentsG] at hQ
  change (∃ k, (R.face t).carrier ∩ H = _) ∨ (∃ v, (R.face t).carrier ∩ H ⊆ _) at hR
  change (∃ l, (Q.face u).carrier ∩ H = _) ∨ (∃ w, (Q.face u).carrier ∩ H ⊆ _) at hQ
  rcases hR with ⟨k, hk⟩ | ⟨v, hv⟩
  · rcases hQ with ⟨l, hl⟩ | ⟨w, hw⟩
    · have hkH : ((R.face t).boundary k).map '' Icc (0 : ℝ) 1 ⊆ H := by
        rw [← hk]
        exact inter_subset_right
      have hlH : ((Q.face u).boundary l).map '' Icc (0 : ℝ) 1 ⊆ H := by
        rw [← hl]
        exact inter_subset_right
      obtain ⟨_, _, _, _, _, _, hk0, hk1⟩ :=
        R.boundary_parameters_of_subset_parent_edge t k i (hkH.trans hHF)
      obtain ⟨_, _, _, _, _, _, hl0, hl1⟩ :=
        Q.boundary_parameters_of_subset_parent_edge u l j (hlH.trans hHG)
      have hinter : (R.face t).carrier ∩ (Q.face u).carrier =
          (((R.face t).boundary k).map '' Icc (0 : ℝ) 1) ∩
            (((Q.face u).boundary l).map '' Icc (0 : ℝ) 1) := by
        rw [← hk, ← hl]
        ext q
        exact ⟨fun hq => ⟨⟨hq.1, hcross hq⟩, ⟨hq.2, hcross hq⟩⟩,
          fun hq => ⟨hq.1.1, hq.2.1⟩⟩
      rcases R.boundary_intersections_of_common_parent_edge Q t u k l i
        (hkH.trans hHF) (hlH.trans hHF)
        (hStoT hk0 (hkH ⟨0, by simp, rfl⟩))
        (hStoT hk1 (hkH ⟨1, by simp, rfl⟩))
        (hTtoS hl0 (hlH ⟨0, by simp, rfl⟩))
        (hTtoS hl1 (hlH ⟨1, by simp, rfl⟩)) with heq | hleft | hright
      · exact Or.inl ⟨k, l, by rw [hinter, ← heq, inter_self], heq⟩
      · exact Or.inr ⟨k.succAbove 0, hinter ▸ hleft⟩
      · exact Or.inr ⟨k.succAbove 1, hinter ▸ hright⟩
    · have hpoint : (R.face t).carrier ∩ (Q.face u).carrier ⊆
          {G (meshTriangleBasis Q.mesh u w)} :=
        fun _ hq => hw ⟨hq.2, hcross hq⟩
      right
      apply R.vertex_of_subsingleton_marked_set t
        (fun _ hx _ hy => (mem_singleton_iff.mp (hpoint hx)).trans
          (mem_singleton_iff.mp (hpoint hy)).symm) inter_subset_left
      intro q hq
      apply hTtoS ?_ (hcross hq)
      have heq := mem_singleton_iff.mp (hpoint hq)
      rw [heq]
      exact Q.child_vertex_mem_marks_of_mem_parent_frontier u w
        (heq ▸ hGfront (hcross hq))
  · exact Or.inr ⟨v, fun q hq => hv ⟨hq.1, hcross hq⟩⟩

omit [T2Space M] in


theorem cross_intersections_of_marked_parent_point {q : M}
    (hparents : (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c)) ⊆ {q})
    (hqS : q ∈ S) (hqT : q ∈ T) (t : R.mesh.Triangle) (u : Q.mesh.Triangle) :
    (∃ v : Fin 3, (R.face t).carrier ∩ (Q.face u).carrier ⊆
      {F (meshTriangleBasis R.mesh t v)}) ∧
    (R.face t).carrier ∩ (Q.face u).carrier ⊆
      frontier (R.face t).carrier ∩ frontier (Q.face u).carrier := by
  have hpoint : (R.face t).carrier ∩ (Q.face u).carrier ⊆ {q} :=
    fun _ hz => hparents ⟨R.carrier_subset_parent t hz.1, Q.carrier_subset_parent u hz.2⟩
  refine ⟨R.vertex_of_subsingleton_marked_set t
    (fun _ hx _ hy => (mem_singleton_iff.mp (hpoint hx)).trans
      (mem_singleton_iff.mp (hpoint hy)).symm)
    inter_subset_left (fun z hz => (mem_singleton_iff.mp (hpoint hz)) ▸ hqS), ?_⟩
  intro z hz
  have heq := mem_singleton_iff.mp (hpoint hz)
  exact ⟨R.marked_point_mem_child_frontier (heq ▸ hqS) t hz.1,
    Q.marked_point_mem_child_frontier (heq ▸ hqT) u hz.2⟩

omit [T2Space M] in

theorem disjoint_children_of_disjoint_parents
    (hparents : Disjoint (F '' convexHull ℝ (range b)) (G '' convexHull ℝ (range c)))
    (t : R.mesh.Triangle) (u : Q.mesh.Triangle) :
    Disjoint (R.face t).carrier (Q.face u).carrier :=
  hparents.mono (R.carrier_subset_parent t) (Q.carrier_subset_parent u)




theorem cross_intersections
    (hparents :
      Disjoint (F '' convexHull ℝ (range b)) (G '' convexHull ℝ (range c)) ∨
      (∃ q : M, q ∈ S ∧ q ∈ T ∧
        (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c)) ⊆ {q}) ∨
      ∃ (i j : Fin 3) (a d a' d' : ℝ),
        a ∈ Icc (0 : ℝ) 1 ∧ d ∈ Icc (0 : ℝ) 1 ∧
        a' ∈ Icc (0 : ℝ) 1 ∧ d' ∈ Icc (0 : ℝ) 1 ∧
        F (affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) a) ∈ S ∧
        F (affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) d) ∈ S ∧
        G (affineChartSegment (c (j.succAbove 0)) (c (j.succAbove 1)) a') ∈ T ∧
        G (affineChartSegment (c (j.succAbove 0)) (c (j.succAbove 1)) d') ∈ T ∧
        (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c)) =
          (F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1))) '' uIcc a d ∧
        (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c)) =
          (G ∘ affineChartSegment (c (j.succAbove 0)) (c (j.succAbove 1))) '' uIcc a' d')
    (hsync : (S : Set M) ∩ (G '' convexHull ℝ (range c)) =
      (T : Set M) ∩ (F '' convexHull ℝ (range b)))
    (t : R.mesh.Triangle) (u : Q.mesh.Triangle) :
    ((∃ k l : Fin 3,
        (R.face t).carrier ∩ (Q.face u).carrier =
          ((R.face t).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((R.face t).boundary k).map '' Icc (0 : ℝ) 1 =
          ((Q.face u).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ v : Fin 3, (R.face t).carrier ∩ (Q.face u).carrier ⊆
        {F (meshTriangleBasis R.mesh t v)}) ∧
    (R.face t).carrier ∩ (Q.face u).carrier ⊆
      frontier (R.face t).carrier ∩ frontier (Q.face u).carrier := by
  rcases hparents with hdisjoint | ⟨q, hqS, hqT, hpoint⟩ |
    ⟨i, j, a, d, a', d', ha, hd, ha', hd', hma, hmd, hma', hmd', hF, hG⟩
  · have hempty := disjoint_iff_inter_eq_empty.mp
      (R.disjoint_children_of_disjoint_parents Q hdisjoint t u)
    exact ⟨Or.inr ⟨0, by rw [hempty]; exact empty_subset _⟩,
      by rw [hempty]; exact empty_subset _⟩
  · obtain ⟨hvertex, hfront⟩ := R.cross_intersections_of_marked_parent_point Q hpoint hqS hqT t u
    exact ⟨Or.inr hvertex, hfront⟩
  · exact R.cross_intersections_of_shared_parent_subsegment Q i j a d a' d'
      ha hd ha' hd' hma hmd hma' hmd' hF hG hsync t u

end SmoothTriangleBoundarySubdivision
end PoincareConjecture.Topology.Surface
