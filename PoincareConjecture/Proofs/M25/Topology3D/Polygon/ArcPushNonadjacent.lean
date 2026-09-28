import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcCandidate
import PoincareConjecture.Proofs.M25.Topology3D.Plane.TriangleEntry
import PoincareConjecture.Proofs.M25.Topology3D.Plane.TriangleBaseContact

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

private theorem convexHull_inter_unitTriangle_subset
    (S : Set (ℝ × ℝ))
    (hcorner : convexHull ℝ S ∩ unitCorner ⊆ {(1, 0), (0, 1)})
    (hgen : S ∩ unitTriangle ⊆ {(1, 0), (0, 1)})
    (hboth : ¬ ((1, 0) ∈ convexHull ℝ S ∧ (0, 1) ∈ convexHull ℝ S)) :
    convexHull ℝ S ∩ unitTriangle ⊆ {(1, 0), (0, 1)} := by
  let C := convexHull ℝ S
  have hC : Convex ℝ C := convex_convexHull ℝ S
  have hD : Convex ℝ (C \ interior unitTriangle) := by
    apply convex_iff_segment_subset.mpr
    intro a ha b hb z hz
    refine ⟨hC.segment_subset ha.1 hb.1 hz, ?_⟩
    intro hzT
    obtain ⟨w, hw, hwT, _⟩ := exists_endpoint_interior_unitTriangle_le_sum hz hzT
      (fun _ hx => hcorner ⟨hC.segment_subset ha.1 hb.1 hx.1, hx.2⟩)
    rcases hw with rfl | rfl
    · exact ha.2 hwT
    · exact hb.2 hwT
  have hSD : S ⊆ C \ interior unitTriangle := by
    intro x hx
    refine ⟨subset_convexHull ℝ S hx, ?_⟩
    intro hxT
    have hxU := interior_subset hxT
    rw [interior_unitTriangle] at hxT
    rcases hgen ⟨hx, hxU⟩ with rfl | rfl <;> norm_num at hxT
  have havoid : Disjoint C (interior unitTriangle) := by
    apply Set.disjoint_left.mpr
    intro x hx
    exact (convexHull_min hSD hD hx).2
  let D := {x ∈ C | x ∈ unitTriangle → x ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ))}
  have hDconv : Convex ℝ D := by
    apply convex_iff_segment_subset.mpr
    intro a ha b hb z hz
    have hzC : z ∈ C := hC.segment_subset ha.1 hb.1 hz
    refine ⟨hzC, ?_⟩
    intro hzT
    by_cases hx0 : z.1 = 0
    · exact hcorner ⟨hzC, (mem_unitCorner_iff z).mpr
        (Or.inr ⟨hx0, hzT.2.1, by have hh := hzT.2.2; linarith⟩)⟩
    by_cases hy0 : z.2 = 0
    · exact hcorner ⟨hzC, (mem_unitCorner_iff z).mpr
        (Or.inl ⟨hzT.1, by have hh := hzT.2.2; linarith, hy0⟩)⟩
    have hzpos : 0 < z.1 ∧ 0 < z.2 :=
      ⟨lt_of_le_of_ne hzT.1 (Ne.symm hx0), lt_of_le_of_ne hzT.2.1 (Ne.symm hy0)⟩
    have hzH : z.1 + z.2 = 1 := by
      apply le_antisymm hzT.2.2
      by_contra! h
      exact Set.disjoint_left.mp havoid hzC
        (by rw [interior_unitTriangle]; exact ⟨hzpos.1, hzpos.2, h⟩)
    have hznot : z ∉ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)) := by
      rintro (rfl | rfl) <;> norm_num at hzpos
    have hza : a ≠ z := fun h => hznot (h ▸ ha.2 (h.symm ▸ hzT))
    have hzb : b ≠ z := fun h => hznot (h ▸ hb.2 (h.symm ▸ hzT))
    have hseg : segment ℝ a b ⊆ C := hC.segment_subset ha.1 hb.1
    obtain ⟨haH, hbH⟩ := sum_eq_one_of_openSegment_base_hit
      (mem_openSegment_of_ne_left_right hza hzb hz) hzpos hzH (havoid.mono_left hseg)
    have hedgeH (w : ℝ × ℝ) (hw : w ∈ segment ℝ a b) : w.1 + w.2 = 1 := by
      have hc : Convex ℝ {v : ℝ × ℝ | v.1 + v.2 = 1} :=
        (convex_singleton (𝕜 := ℝ) (1 : ℝ)).linear_preimage
          (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ)
      exact hc.segment_subset haH hbH hw
    have hnomid (c : ℝ × ℝ) (hc : c ∈ ({a, b} : Set (ℝ × ℝ))) :
        ¬ (0 < c.1 ∧ c.1 < 1) := by
      intro h
      have hcH : c.1 + c.2 = 1 := by
        rcases hc with rfl | rfl
        · exact haH
        · exact hbH
      have hcT : c ∈ unitTriangle := ⟨h.1.le, by linarith, hcH.le⟩
      have hcV : c ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)) := by
        rcases hc with rfl | rfl
        · exact ha.2 hcT
        · exact hb.2 hcT
      rcases hcV with rfl | rfl <;> norm_num at h
    have hproj : Prod.fst '' segment ℝ a b = Icc (min a.1 b.1) (max a.1 b.1) := by
      calc
        _ = segment ℝ a.1 b.1 := image_segment ℝ (LinearMap.fst ℝ ℝ ℝ).toAffineMap a b
        _ = _ := segment_eq_Icc' _ _
    have hzcoord : z.1 ∈ Icc (min a.1 b.1) (max a.1 b.1) :=
      hproj ▸ mem_image_of_mem Prod.fst hz
    have hz1 : z.1 < 1 := by linarith [hzpos.2]
    have hmin : min a.1 b.1 ≤ 0 := by
      by_contra! h
      rcases le_total a.1 b.1 with hab | hba
      · rw [min_eq_left hab] at h hzcoord
        exact hnomid a (Or.inl rfl) ⟨h, hzcoord.1.trans_lt hz1⟩
      · rw [min_eq_right hba] at h hzcoord
        exact hnomid b (Or.inr rfl) ⟨h, hzcoord.1.trans_lt hz1⟩
    have hmax : 1 ≤ max a.1 b.1 := by
      by_contra! h
      rcases le_total a.1 b.1 with hab | hba
      · rw [max_eq_right hab] at h hzcoord
        exact hnomid b (Or.inr rfl) ⟨hzpos.1.trans_le hzcoord.2, h⟩
      · rw [max_eq_left hba] at h hzcoord
        exact hnomid a (Or.inl rfl) ⟨hzpos.1.trans_le hzcoord.2, h⟩
    have hbase (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : (u, 1 - u) ∈ C := by
      have huim : u ∈ Prod.fst '' segment ℝ a b :=
        hproj.symm ▸ ⟨hmin.trans hu.1, hu.2.trans hmax⟩
      obtain ⟨w, hw, hwu⟩ := huim
      have hwH := hedgeH w hw
      have heq : w = (u, 1 - u) := Prod.ext hwu (by linarith)
      exact heq ▸ hseg hw
    exact (hboth ⟨by simpa using hbase 1 ⟨zero_le_one, le_rfl⟩,
      by simpa using hbase 0 ⟨le_rfl, zero_le_one⟩⟩).elim
  have hSD' : S ⊆ D := fun _ hx =>
    ⟨subset_convexHull ℝ S hx, fun h => hgen ⟨hx, h⟩⟩
  exact fun _ hx => (convexHull_min hSD' hDconv hx.1).2 hx.2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} {p : Polygon E (n + 2)}

theorem IsSimplePolygonalArc.isAdmissible_polygonPushVertex_of_nonadjacent
    (hp : IsSimplePolygonalArc p) (hdim : Module.finrank ℝ E = 2)
    (k l : Fin (n + 2)) (hk : IsAdmissibleArcVertex p k)
    (hl : IsAdmissibleArcVertex p l) (hlk : l ≠ k)
    (hlp : l ≠ (finRotate (n + 2)).symm k) (hls : l ≠ finRotate (n + 2) k)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    IsAdmissibleArcVertex (polygonPushVertex p k t) l := by
  let ρ := finRotate (n + 2)
  have hpl : ρ.symm l ≠ k := fun h => hls (by rw [← h, Equiv.apply_symm_apply])
  have hsl : ρ l ≠ k := fun h => hlp (by rw [← h, Equiv.symm_apply_apply])
  let q := polygonPushVertex p k t
  have hq (i : Fin (n + 2)) (hi : i ≠ k) : q i = p i :=
    polygonReplaceVertex_apply_of_ne p k _ hi
  have hqs := hp.isSimple_polygonPushVertex k hk ht
  by_cases hli : LinearIndependent ℝ ![p (ρ.symm l) - p l, p (ρ l) - p l]
  swap
  · by_contra hn
    have hh := hqs.linearIndependent_of_not_admissible l hl.1 hl.2.1 hn
    change LinearIndependent ℝ ![q (ρ.symm l) - q l, q (ρ l) - q l] at hh
    exact hli (by simpa only [hq l hlk, hq (ρ.symm l) hpl, hq (ρ l) hsl] using hh)
  obtain ⟨f, hfl, hfp, hfs⟩ := exists_continuousAffineEquiv_map_triangle hdim hli
  let Tk := polygonVertexTriangle p k
  let Tl := polygonVertexTriangle p l
  let Cl := segment ℝ (p l) (p (ρ.symm l)) ∪ segment ℝ (p l) (p (ρ l))
  let S : Set (ℝ × ℝ) := {f (p k), f (p (ρ.symm k)), f (p (ρ k))}
  have hTk : f '' Tk = convexHull ℝ S := by
    change f.toAffineMap '' convexHull ℝ _ = convexHull ℝ S
    rw [f.toAffineMap.image_convexHull]
    simp only [image_insert_eq, image_singleton]
    rfl
  have hTl : f '' Tl = unitTriangle := by
    change f.toAffineMap '' convexHull ℝ _ = unitTriangle
    rw [f.toAffineMap.image_convexHull]
    simp only [image_insert_eq, image_singleton]
    change convexHull ℝ {f (p l), f (p (ρ.symm l)), f (p (ρ l))} = unitTriangle
    rw [hfl, hfp, hfs]
    exact unitTriangle_eq_convexHull.symm
  have hCl : f '' Cl = unitCorner := by
    change f.toAffineMap '' Cl = unitCorner
    rw [image_union, image_segment, image_segment]
    change segment ℝ (f (p l)) (f (p (ρ.symm l))) ∪
      segment ℝ (f (p l)) (f (p (ρ l))) = unitCorner
    rw [hfl, hfp, hfs]
    rfl
  have hplnot : p l ∉ Tk := by
    intro h
    rcases (hp.vertex_mem_triangle_iff_of_admissible k hk l).mp h with h | h | h
    · exact hlk h
    · exact hlp h
    · exact hls h
  have hinter : Tk ∩ Cl ⊆ {p (ρ.symm l), p (ρ l)} := by
    obtain ⟨i, j, hil, hjl, hip, hjs, _⟩ :=
      exists_arc_incident_edge_indices l hl.1 hl.2.1
    rintro x ⟨hxT, hx⟩
    have hxl : x ≠ p l := fun h => hplnot (h ▸ hxT)
    rcases hx with hx | hx
    · have hxe : x ∈ p.edgeSet ℝ i.castSucc := by
        rw [polygon_arcEdge_eq_segment, hip, hil, segment_symm]
        exact hx
      have hh := (hp.triangle_inter_edge_subset_of_admissible k hk i
        (by simpa only [hip] using hpl) (by simpa only [hil] using hlk) ⟨hxT, hxe⟩).2
      rw [hip, hil] at hh
      exact Or.inl (hh.resolve_right hxl)
    · have hxe : x ∈ p.edgeSet ℝ j.castSucc := by
        rw [polygon_arcEdge_eq_segment, hjl, hjs]
        exact hx
      have hh := (hp.triangle_inter_edge_subset_of_admissible k hk j
        (by simpa only [hjl] using hlk) (by simpa only [hjs] using hsl) ⟨hxT, hxe⟩).2
      rw [hjl, hjs] at hh
      exact Or.inr (hh.resolve_left hxl)
  have hcorner : convexHull ℝ S ∩ unitCorner ⊆ {(1, 0), (0, 1)} := by
    rintro x ⟨hxT, hxC⟩
    obtain ⟨y, hy, rfl⟩ := hTk.symm ▸ hxT
    obtain ⟨z, hz, hzy⟩ := hCl.symm ▸ hxC
    have hyC : y ∈ Cl := f.injective hzy ▸ hz
    rcases hinter ⟨hy, hyC⟩ with hy | hy
    · exact Or.inl (by rw [hy, hfp])
    · exact Or.inr (show f y = (0, 1) by rw [hy, hfs])
  have hvertex (j : Fin (n + 2)) (hj : p j ∈ Tk) (hjU : f (p j) ∈ unitTriangle) :
      f (p j) ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)) := by
    obtain ⟨x, hx, hxj⟩ := hTl.symm ▸ hjU
    have hjT : p j ∈ Tl := f.injective hxj ▸ hx
    have hjC : p j ∈ Cl := by
      have hh : p j ∈ polygonVertexTriangle p l ∩ polygonArcBoundary p :=
        ⟨hjT, polygon_vertex_mem_arcBoundary p j⟩
      rw [hl.2.2] at hh
      exact hh
    exact hcorner ⟨hTk ▸ mem_image_of_mem f hj, hCl ▸ mem_image_of_mem f hjC⟩
  have hgen : S ∩ unitTriangle ⊆ {(1, 0), (0, 1)} := by
    rintro x ⟨hx, hxU⟩
    rcases hx with rfl | rfl | rfl
    · exact hvertex k (subset_convexHull ℝ _ (by simp)) hxU
    · exact hvertex (ρ.symm k) (subset_convexHull ℝ _ (by simp [ρ])) hxU
    · exact hvertex (ρ k) (subset_convexHull ℝ _ (by simp [ρ])) hxU
  have hvals (i : Fin (n + 2)) (hi0 : i ≠ 0) (hil : i ≠ Fin.last (n + 1)) :
      (ρ.symm i).val + 1 = i.val ∧ (ρ i).val = i.val + 1 := by
    obtain ⟨a, b, hai, hbi, hap, hbs, _⟩ := exists_arc_incident_edge_indices i hi0 hil
    have h1 := congrArg Fin.val hai
    have h2 := congrArg Fin.val hbi
    have h3 := congrArg Fin.val hap
    have h4 := congrArg Fin.val hbs
    change a.val + 1 = i.val at h1
    change b.val = i.val at h2
    change a.val = (ρ.symm i).val at h3
    change b.val + 1 = (ρ i).val at h4
    omega
  obtain ⟨hkp, hks⟩ := hvals k hk.1 hk.2.1
  obtain ⟨hlpv, hlsv⟩ := hvals l hl.1 hl.2.1
  have hboth : ¬ ((1, 0) ∈ convexHull ℝ S ∧ (0, 1) ∈ convexHull ℝ S) := by
    rintro ⟨ha, hb⟩
    obtain ⟨a, haT, haf⟩ := hTk.symm ▸ ha
    obtain ⟨b, hbT, hbf⟩ := hTk.symm ▸ hb
    have haeq : a = p (ρ.symm l) := f.injective (haf.trans hfp.symm)
    have hbeq : b = p (ρ l) := f.injective (hbf.trans hfs.symm)
    have haidx := (hp.vertex_mem_triangle_iff_of_admissible k hk (ρ.symm l)).mp
      (haeq ▸ haT)
    have hbidx := (hp.vertex_mem_triangle_iff_of_admissible k hk (ρ l)).mp (hbeq ▸ hbT)
    change ρ.symm l = k ∨ ρ.symm l = ρ.symm k ∨ ρ.symm l = ρ k at haidx
    change ρ l = k ∨ ρ l = ρ.symm k ∨ ρ l = ρ k at hbidx
    have hne : l.val ≠ k.val := fun h => hlk (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rcases haidx with h | h | h <;> have hv := congrArg Fin.val h <;> omega
    · rcases hbidx with h | h | h <;> have hv := congrArg Fin.val h <;> omega
  have htri : Tk ∩ Tl ⊆ Cl := by
    rintro x ⟨hxk, hxl⟩
    have hx := convexHull_inter_unitTriangle_subset S hcorner hgen hboth
      ⟨hTk ▸ mem_image_of_mem f hxk, hTl ▸ mem_image_of_mem f hxl⟩
    rcases hx with hx | hx
    · have heq := f.injective (hx.trans hfp.symm)
      exact Or.inl (heq ▸ right_mem_segment ℝ (p l) (p (ρ.symm l)))
    · have heq := f.injective (hx.trans hfs.symm)
      exact Or.inr (heq ▸ right_mem_segment ℝ (p l) (p (ρ l)))
  have hTlq : polygonVertexTriangle q l = Tl := by
    change convexHull ℝ {q l, q (ρ.symm l), q (ρ l)} =
      convexHull ℝ {p l, p (ρ.symm l), p (ρ l)}
    rw [hq l hlk, hq (ρ.symm l) hpl, hq (ρ l) hsl]
  have hClq : segment ℝ (q l) (q (ρ.symm l)) ∪ segment ℝ (q l) (q (ρ l)) = Cl := by
    rw [hq l hlk, hq (ρ.symm l) hpl, hq (ρ l) hsl]
  refine ⟨hl.1, hl.2.1, ?_⟩
  change polygonVertexTriangle q l ∩ polygonArcBoundary q = _
  apply Subset.antisymm
  · rw [hTlq, hClq]
    rintro x ⟨hxl, hxG⟩
    by_cases hxk : x ∈ Tk
    · exact htri ⟨hxk, hxl⟩
    · have hold : x ∈ polygonArcBoundary p :=
        by
          have hh : x ∈ polygonArcBoundary q \ Tk := ⟨hxG, hxk⟩
          have hs : polygonArcBoundary q \ Tk = polygonArcBoundary p \ Tk :=
            polygonPushVertex_arcBoundary_sdiff_triangle p k ht
          rw [hs] at hh
          exact hh.1
      have hh : x ∈ polygonVertexTriangle p l ∩ polygonArcBoundary p := ⟨hxl, hold⟩
      rw [hl.2.2] at hh
      exact hh
  · exact polygonArcIncidentEdges_subset_triangle_inter_boundary q l hl.1 hl.2.1

end PoincareConjecture.M25.Topology3D
