import PoincareConjecture.Proofs.M25.Topology3D.Plane.TriangleBaseContact
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.VisibleDiagonal

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  {p : Polygon E n}

theorem IsSimplePolygon.normalized_triangle_interior_disjoint_boundary
    (hp : IsSimplePolygon p) (k : Fin n) (f : E ≃ᴬ[ℝ] (ℝ × ℝ))
    (hfk : f (p k) = (0, 0))
    (hfp : f (p ((finRotate n).symm k)) = (1, 0))
    (hfs : f (p (finRotate n k)) = (0, 1))
    (hempty : ∀ j, f (p j) ∈ unitTriangle →
      j = k ∨ j = (finRotate n).symm k ∨ j = finRotate n k) :
    Disjoint (interior unitTriangle) (f '' p.boundary ℝ) := by
  apply Set.disjoint_left.mpr
  intro w hwT hwB
  obtain ⟨z, hzB, rfl⟩ := hwB
  have hcoords := hwT
  rw [interior_unitTriangle] at hcoords
  have hzC : f z ∉ unitCorner := by
    intro h
    rcases (mem_unitCorner_iff _).mp h with h | h
    · exact hcoords.2.1.ne' h.2.2
    · exact hcoords.1.ne' h.1
  obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff p z).mp hzB
  have himage : f '' p.edgeSet ℝ i =
      segment ℝ (f (p i)) (f (p (finRotate n i))) := by
    rw [polygon_edgeSet_eq_segment]
    exact image_segment ℝ f.toAffineEquiv.toAffineMap _ _
  have hzi : f z ∈ segment ℝ (f (p i)) (f (p (finRotate n i))) :=
    himage ▸ mem_image_of_mem f hi
  have hik : i ≠ k := by
    intro heq
    rw [heq, hfk, hfs] at hzi
    exact hzC (Or.inr hzi)
  have hip : i ≠ (finRotate n).symm k := by
    intro heq
    rw [heq, (finRotate n).apply_symm_apply, hfp, hfk, segment_symm] at hzi
    exact hzC (Or.inl hzi)
  obtain ⟨c, hc, hcT, _⟩ := exists_endpoint_interior_unitTriangle_le_sum hzi hwT
    (hp.normalized_nonincident_edge_inter_corner_subset k f hfk hfp hfs i hik hip)
  obtain ⟨l, hcl⟩ : ∃ l : Fin n, c = f (p l) := by
    rcases hc with hc | hc
    · exact ⟨i, hc⟩
    · exact ⟨finRotate n i, hc⟩
  rw [hcl] at hcT
  rcases hempty l (interior_subset hcT) with rfl | rfl | rfl
  · rw [hfk, interior_unitTriangle] at hcT
    exact (lt_irrefl 0) hcT.1
  · rw [hfp, interior_unitTriangle] at hcT
    exact (lt_irrefl 0) hcT.2.1
  · rw [hfs, interior_unitTriangle] at hcT
    exact (lt_irrefl 0) hcT.1

theorem IsSimplePolygon.normalized_triangle_inter_boundary_eq_corner
    (hp : IsSimplePolygon p) (hn : 3 < n) (k : Fin n) (f : E ≃ᴬ[ℝ] (ℝ × ℝ))
    (hfk : f (p k) = (0, 0))
    (hfp : f (p ((finRotate n).symm k)) = (1, 0))
    (hfs : f (p (finRotate n k)) = (0, 1))
    (hempty : ∀ j, f (p j) ∈ unitTriangle →
      j = k ∨ j = (finRotate n).symm k ∨ j = finRotate n k) :
    unitTriangle ∩ (f '' p.boundary ℝ) = unitCorner := by
  have himage (i : Fin n) : f '' p.edgeSet ℝ i =
      segment ℝ (f (p i)) (f (p (finRotate n i))) := by
    rw [polygon_edgeSet_eq_segment]
    exact image_segment ℝ f.toAffineEquiv.toAffineMap _ _
  have hpred : f '' p.edgeSet ℝ ((finRotate n).symm k) =
      segment ℝ (0, 0) (1, 0) := by
    rw [himage, (finRotate n).apply_symm_apply, hfp, hfk, segment_symm]
  have hsucc : f '' p.edgeSet ℝ k = segment ℝ (0, 0) (0, 1) := by
    rw [himage, hfk, hfs]
  apply subset_antisymm
  · intro w hw
    by_contra hwC
    have hx : 0 < w.1 := by
      by_contra! h
      have heq : w.1 = 0 := le_antisymm h hw.1.1
      exact hwC ((mem_unitCorner_iff w).mpr
        (Or.inr ⟨heq, hw.1.2.1, by linarith [hw.1.2.2]⟩))
    have hy : 0 < w.2 := by
      by_contra! h
      have heq : w.2 = 0 := le_antisymm h hw.1.2.1
      exact hwC ((mem_unitCorner_iff w).mpr
        (Or.inl ⟨hw.1.1, by linarith [hw.1.2.2], heq⟩))
    have hdis := hp.normalized_triangle_interior_disjoint_boundary k f hfk hfp hfs hempty
    have hH : w.1 + w.2 = 1 := by
      apply le_antisymm hw.1.2.2
      by_contra! h
      have hwint : w ∈ interior unitTriangle := by
        rw [interior_unitTriangle]
        exact ⟨hx, hy, h⟩
      exact Set.disjoint_left.mp hdis hwint hw.2
    obtain ⟨z, hzB, hzw⟩ := hw.2
    obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff p z).mp hzB
    have hwi : w ∈ segment ℝ (f (p i)) (f (p (finRotate n i))) := by
      rw [← himage]
      exact ⟨z, hi, hzw⟩
    have hik : i ≠ k := by
      intro heq
      rw [heq, hfk, hfs] at hwi
      exact hwC (Or.inr hwi)
    have hip : i ≠ (finRotate n).symm k := by
      intro heq
      rw [heq, (finRotate n).apply_symm_apply, hfp, hfk, segment_symm] at hwi
      exact hwC (Or.inl hwi)
    have hkedge : p k ∉ p.edgeSet ℝ i := by
      intro h
      rcases (hp.vertex_mem_edgeSet_iff k i).mp h with heq | heq
      · exact hik heq.symm
      · exact hip ((finRotate n).injective
          (heq.symm.trans ((finRotate n).apply_symm_apply k).symm))
    have himB : segment ℝ (f (p i)) (f (p (finRotate n i))) ⊆ f '' p.boundary ℝ := by
      rw [← himage]
      exact image_mono (polygon_edgeSet_subset_boundary p i)
    have hsegdis : Disjoint (segment ℝ (f (p i)) (f (p (finRotate n i))))
        (interior unitTriangle) := hdis.symm.mono_left himB
    have hend : ∀ c ∈ ({f (p i), f (p (finRotate n i))} : Set (ℝ × ℝ)),
        c ∈ unitTriangle → c ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)) := by
      intro c hc hcT
      obtain ⟨l, hl, hcl⟩ : ∃ l : Fin n, p l ∈ p.edgeSet ℝ i ∧ c = f (p l) := by
        rcases hc with hc | hc
        · exact ⟨i, polygon_left_mem_edgeSet p i, hc⟩
        · exact ⟨finRotate n i, polygon_right_mem_edgeSet p i, hc⟩
      rw [hcl] at hcT ⊢
      rcases hempty l hcT with rfl | rfl | rfl
      · exact (hkedge hl).elim
      · exact Or.inl hfp
      · exact Or.inr hfs
    have hinc : segment ℝ (f (p i)) (f (p (finRotate n i))) ∩ {(1, 0), (0, 1)} ⊆
        {f (p i), f (p (finRotate n i))} := by
      intro c hc
      obtain ⟨l, hcl⟩ : ∃ l : Fin n, c = f (p l) := by
        rcases hc.2 with hc | hc
        · exact ⟨(finRotate n).symm k, hc.trans hfp.symm⟩
        · exact ⟨finRotate n k, hc.trans hfs.symm⟩
      have hl : p l ∈ p.edgeSet ℝ i := by
        have hmem := hc.1
        rw [hcl, ← himage] at hmem
        obtain ⟨v, hv, heq⟩ := hmem
        exact f.injective heq ▸ hv
      rcases (hp.vertex_mem_edgeSet_iff l i).mp hl with heq | heq
      · exact Or.inl (by rw [hcl, heq])
      · right
        change c = f (p (finRotate n i))
        rw [hcl, heq]
    rcases unit_base_endpoints_of_segment_base_hit hwi ⟨hx, hy⟩ hH hsegdis hend hinc with
      ⟨ha, _⟩ | ⟨ha, hb⟩
    · exact hip (hp.vertices_injective (f.injective (ha.trans hfp.symm)))
    · have hi : i = finRotate n k := hp.vertices_injective (f.injective (ha.trans hfs.symm))
      have hnext : finRotate n i = (finRotate n).symm k :=
        hp.vertices_injective (f.injective (hb.trans hfp.symm))
      have hthree : finRotate n (finRotate n (finRotate n k)) = k := by
        rw [← hi, hnext, (finRotate n).apply_symm_apply]
      let : NeZero n := ⟨by omega⟩
      simp only [finRotate_apply, add_assoc] at hthree
      have hzero : (1 : Fin n) + (1 + 1) = 0 :=
        add_left_cancel (hthree.trans (add_zero k).symm)
      have hval := congrArg Fin.val hzero
      norm_num [Fin.add_def, Fin.val_natCast, Nat.mod_eq_of_lt (show 1 < n by omega),
        Nat.mod_eq_of_lt (show 2 < n by omega), Nat.mod_eq_of_lt hn] at hval
  · intro w hw
    refine ⟨?_, ?_⟩
    · rcases (mem_unitCorner_iff w).mp hw with h | h
      · exact ⟨h.1, by linarith [h.2.2], by linarith [h.2.1, h.2.2]⟩
      · exact ⟨by linarith [h.1], h.2.1, by linarith [h.1, h.2.2]⟩
    · rcases hw with hw | hw
      · exact image_mono (polygon_edgeSet_subset_boundary p _) (hpred.symm ▸ hw)
      · exact image_mono (polygon_edgeSet_subset_boundary p _) (hsucc.symm ▸ hw)

theorem IsSimplePolygon.supporting_triangle_of_no_triangle_vertex
    [FiniteDimensional ℝ E] (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) (hn : 3 < n) (k : Fin n)
    (hli : LinearIndependent ℝ
      ![p ((finRotate n).symm k) - p k, p (finRotate n k) - p k])
    (X : E →L[ℝ] ℝ) (hX : Function.Surjective X)
    (hsupport : ∀ j, X (p k) ≤ X (p j))
    (hempty : ∀ j, p j ∈ convexHull ℝ {p k, p ((finRotate n).symm k), p (finRotate n k)} →
      j = k ∨ j = (finRotate n).symm k ∨ j = finRotate n k) :
    (convexHull ℝ {p k, p ((finRotate n).symm k), p (finRotate n k)} ∩ p.boundary ℝ =
      segment ℝ (p k) (p ((finRotate n).symm k)) ∪ segment ℝ (p k) (p (finRotate n k))) ∧
    convexHull ℝ {p k, p ((finRotate n).symm k), p (finRotate n k)} ⊆
      closure (polygonInterior p) := by
  let C := convexHull ℝ {p k, p ((finRotate n).symm k), p (finRotate n k)}
  let D := segment ℝ (p k) (p ((finRotate n).symm k)) ∪ segment ℝ (p k) (p (finRotate n k))
  obtain ⟨f, hfk, hfp, hfs, r, hr, hr1, hwedge, _⟩ :=
    hp.exists_local_inside_wedge hdim k hli X hX hsupport
  have hnorm : f '' C = unitTriangle := by
    have him := f.toAffineEquiv.toAffineMap.image_convexHull
      {p k, p ((finRotate n).symm k), p (finRotate n k)}
    change f '' C =
      convexHull ℝ (f '' {p k, p ((finRotate n).symm k), p (finRotate n k)}) at him
    rw [him, image_insert_eq, image_insert_eq, image_singleton, hfk, hfp, hfs,
      ← unitTriangle_eq_convexHull]
  have hCeq : C = f ⁻¹' unitTriangle := by
    ext z
    constructor
    · intro hz
      exact hnorm ▸ mem_image_of_mem f hz
    · intro hz
      have hzimg : f z ∈ f '' C := hnorm.symm ▸ hz
      obtain ⟨w, hw, heq⟩ := hzimg
      exact f.injective heq ▸ hw
  have hmem (c z : E) : z ∈ segment ℝ (p k) c ↔
      f z ∈ segment ℝ (0, 0) (f c) := by
    have him := image_segment ℝ f.toAffineEquiv.toAffineMap (p k) c
    change f '' segment ℝ (p k) c = segment ℝ (f (p k)) (f c) at him
    rw [hfk] at him
    rw [← him]
    constructor
    · exact mem_image_of_mem f
    · rintro ⟨w, hw, heq⟩
      exact f.injective heq ▸ hw
  have hDeq : D = f ⁻¹' unitCorner := by
    ext z
    change z ∈ segment ℝ (p k) (p ((finRotate n).symm k)) ∪
      segment ℝ (p k) (p (finRotate n k)) ↔ f z ∈ unitCorner
    simpa only [unitCorner, mem_union, hfp, hfs] using
      or_congr (hmem (p ((finRotate n).symm k)) z) (hmem (p (finRotate n k)) z)
  have hemptyf : ∀ j, f (p j) ∈ unitTriangle →
      j = k ∨ j = (finRotate n).symm k ∨ j = finRotate n k := by
    intro j hj
    apply hempty j
    change p j ∈ C
    rw [hCeq]
    exact hj
  have hinc := hp.normalized_triangle_inter_boundary_eq_corner hn k f hfk hfp hfs hemptyf
  have hboundary : C ∩ p.boundary ℝ = D := by
    rw [hCeq, hDeq]
    ext z
    change (f z ∈ unitTriangle ∧ z ∈ p.boundary ℝ) ↔ f z ∈ unitCorner
    rw [← hinc]
    constructor
    · intro hz
      exact ⟨hz.1, mem_image_of_mem f hz.2⟩
    · rintro ⟨hzT, w, hw, heq⟩
      exact ⟨hzT, f.injective heq ▸ hw⟩
  have hdis := hp.normalized_triangle_interior_disjoint_boundary k f hfk hfp hfs hemptyf
  obtain ⟨hI, hO, _, _, hIO, hcover, _⟩ := hp.polygonRegions_spec hdim
  have hinside : f ⁻¹' interior unitTriangle ⊆ polygonInterior p := by
    apply IsPreconnected.subset_left_of_subset_union hI hO hIO
    · rw [hcover]
      intro z hz hzB
      exact Set.disjoint_left.mp hdis hz (mem_image_of_mem f hzB)
    · refine ⟨f.symm (r / 4, r / 4), ?_, ?_⟩
      · change f (f.symm (r / 4, r / 4)) ∈ interior unitTriangle
        rw [f.apply_symm_apply, interior_unitTriangle]
        change 0 < r / 4 ∧ 0 < r / 4 ∧ r / 4 + r / 4 < 1
        constructor
        · linarith
        constructor <;> linarith
      · apply hwedge
        change f (f.symm (r / 4, r / 4)) ∈ Ioo 0 r ×ˢ Ioo 0 r
        rw [f.apply_symm_apply]
        constructor <;> constructor <;> dsimp <;> linarith
    · exact f.toHomeomorph.isPreconnected_preimage.mpr convex_unitTriangle.interior.isPreconnected
  refine ⟨hboundary, ?_⟩
  have hclosure := closure_mono hinside
  change closure (f.toHomeomorph ⁻¹' interior unitTriangle) ⊆ closure (polygonInterior p)
    at hclosure
  rw [← f.toHomeomorph.preimage_closure] at hclosure
  change f ⁻¹' closure (interior unitTriangle) ⊆ closure (polygonInterior p) at hclosure
  rw [closure_interior_unitTriangle] at hclosure
  change C ⊆ closure (polygonInterior p)
  rw [hCeq]
  exact hclosure

end PoincareConjecture.M25.Topology3D
