import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcPush
import PoincareConjecture.Proofs.M25.Topology3D.Plane.BendGraph
import PoincareConjecture.Proofs.M25.Topology3D.Plane.CornerSectors
import PoincareConjecture.Proofs.M25.Topology3D.Plane.LocalSideRefinement
import PoincareConjecture.Proofs.M25.Topology3D.Plane.SegmentSubdivision

set_option autoImplicit false

open Set Metric Topology

namespace PoincareConjecture.M25.Topology3D

private noncomputable def cornerMinHomeomorph : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun x := (min x.1 x.2, x.1 - x.2)
  invFun x := (x.1 + max x.2 0, x.1 + max (-x.2) 0)
  left_inv x := by
    rcases le_total x.1 x.2 with h | h
    · apply Prod.ext
      · change min x.1 x.2 + max (x.1 - x.2) 0 = x.1
        rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h), add_zero]
      · change min x.1 x.2 + max (-(x.1 - x.2)) 0 = x.2
        rw [min_eq_left h, max_eq_left (neg_nonneg.mpr (sub_nonpos.mpr h))]
        ring
    · apply Prod.ext
      · change min x.1 x.2 + max (x.1 - x.2) 0 = x.1
        rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
        ring
      · change min x.1 x.2 + max (-(x.1 - x.2)) 0 = x.2
        rw [min_eq_right h, max_eq_right (neg_nonpos.mpr (sub_nonneg.mpr h)), add_zero]
  right_inv x := by
    by_cases h : 0 ≤ x.2
    · apply Prod.ext
      · change min (x.1 + max x.2 0) (x.1 + max (-x.2) 0) = x.1
        rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), add_zero]
        exact min_eq_right (by linarith)
      · change x.1 + max x.2 0 - (x.1 + max (-x.2) 0) = x.2
        rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
        ring
    · have h' : x.2 ≤ 0 := le_of_not_ge h
      apply Prod.ext
      · change min (x.1 + max x.2 0) (x.1 + max (-x.2) 0) = x.1
        rw [max_eq_right h', max_eq_left (neg_nonneg.mpr h'), add_zero]
        exact min_eq_left (by linarith)
      · change x.1 + max x.2 0 - (x.1 + max (-x.2) 0) = x.2
        rw [max_eq_right h', max_eq_left (neg_nonneg.mpr h')]
        ring
  continuous_toFun := (continuous_fst.min continuous_snd).prodMk
    (continuous_fst.sub continuous_snd)
  continuous_invFun := (continuous_fst.add (continuous_snd.max continuous_const)).prodMk
    (continuous_fst.add (continuous_snd.neg.max continuous_const))

private theorem cornerMinHomeomorph_smul (t : ℝ) (ht : 0 ≤ t) (x : ℝ × ℝ) :
    cornerMinHomeomorph (t • x) = t • cornerMinHomeomorph x := by
  apply Prod.ext
  · change min (t * x.1) (t * x.2) = t * min x.1 x.2
    rcases le_total x.1 x.2 with h | h
    · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h ht)]
    · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left h ht)]
  · change t * x.1 - t * x.2 = t * (x.1 - x.2)
    ring

theorem exists_homeomorph_corner_crossing (u v : ℝ × ℝ)
    (hu : 0 < u.1 ∧ 0 < u.2) (hv : v.1 < 0 ∨ v.2 < 0) :
    ∃ h : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), h 0 = 0 ∧
      (∀ x : ℝ × ℝ, (h x).1 = min x.1 x.2) ∧
      (∀ t : ℝ, 0 ≤ t → h (t, 0) = (0, t) ∧ h (0, t) = (0, -t) ∧
        h (t • v) = (t * min v.1 v.2, 0) ∧ h (t • u) = (t * min u.1 u.2, 0)) ∧
      (∀ x : ℝ × ℝ, x ∈ segment ℝ 0 v ∪ segment ℝ 0 u ↔
        min v.1 v.2 ≤ (h x).1 ∧ (h x).1 ≤ min u.1 u.2 ∧ (h x).2 = 0) ∧
      (∀ x : ℝ × ℝ, x ∈ unitCorner ↔
        (h x).1 = 0 ∧ -1 ≤ (h x).2 ∧ (h x).2 ≤ 1) := by
  let R := cornerMinHomeomorph
  have hmu : (R v).1 < 0 := min_lt_iff.mpr hv
  have hnu : 0 < (R u).1 := lt_min hu.1 hu.2
  let h := R.trans (graphFlatteningHomeomorph (bendGraph (R v) (R u))
    (continuous_bendGraph (R v) (R u)))
  have hformula (x : ℝ × ℝ) :
      h x = (min x.1 x.2, x.1 - x.2 - bendGraph (R v) (R u) (min x.1 x.2)) := rfl
  have hzero : h 0 = 0 := by rw [hformula]; simp [bendGraph]
  have hvray (t : ℝ) (ht : 0 ≤ t) : h (t • v) = (t * min v.1 v.2, 0) := by
    change ((R (t • v)).1, (R (t • v)).2 -
      bendGraph (R v) (R u) (R (t • v)).1) = (t * (R v).1, 0)
    rw [cornerMinHomeomorph_smul t ht]
    dsimp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [bendGraph, if_pos (mul_nonpos_of_nonneg_of_nonpos ht hmu.le)]
    apply Prod.ext
    · rfl
    · change t * (R v).2 - (R v).2 / (R v).1 * (t * (R v).1) = 0
      apply sub_eq_zero.mpr
      field_simp [hmu.ne]
  have huray (t : ℝ) (ht : 0 ≤ t) : h (t • u) = (t * min u.1 u.2, 0) := by
    by_cases ht0 : t = 0
    · subst t
      rw [zero_smul, zero_mul, hformula]
      simp [bendGraph]
    have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    change ((R (t • u)).1, (R (t • u)).2 -
      bendGraph (R v) (R u) (R (t • u)).1) = (t * (R u).1, 0)
    rw [cornerMinHomeomorph_smul t ht]
    dsimp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [bendGraph, if_neg (not_le.mpr (mul_pos htpos hnu))]
    apply Prod.ext
    · rfl
    · change t * (R u).2 - (R u).2 / (R u).1 * (t * (R u).1) = 0
      apply sub_eq_zero.mpr
      field_simp [hnu.ne']
  have hseg (z x : ℝ × ℝ) : x ∈ segment ℝ 0 z ↔ R x ∈ segment ℝ 0 (R z) := by
    rw [segment_eq_image, segment_eq_image]
    constructor
    · rintro ⟨t, ht, heq⟩
      refine ⟨t, ht, ?_⟩
      simp only [smul_zero, zero_add] at heq ⊢
      rw [← cornerMinHomeomorph_smul t ht.1, heq]
    · rintro ⟨t, ht, heq⟩
      refine ⟨t, ht, ?_⟩
      simp only [smul_zero, zero_add] at heq ⊢
      apply R.injective
      rw [cornerMinHomeomorph_smul t ht.1]
      exact heq
  refine ⟨h, hzero, fun _ => rfl, ?_, ?_, ?_⟩
  · intro t ht
    refine ⟨?_, ?_, hvray t ht, huray t ht⟩
    · simp [hformula, min_eq_right ht, bendGraph]
    · simp [hformula, min_eq_left ht, bendGraph]
  · intro x
    rw [mem_union, hseg v x, hseg u x, ← mem_union,
      mem_two_segments_zero_iff_graph hmu hnu]
    change (R v).1 ≤ (R x).1 ∧ (R x).1 ≤ (R u).1 ∧
      (R x).2 = bendGraph (R v) (R u) (R x).1 ↔
        (R v).1 ≤ (R x).1 ∧ (R x).1 ≤ (R u).1 ∧
          (R x).2 - bendGraph (R v) (R u) (R x).1 = 0
    rw [sub_eq_zero]
  · intro x
    rw [mem_unitCorner_iff]
    have hfst : (h x).1 = min x.1 x.2 := rfl
    have hsnd (hm : min x.1 x.2 = 0) : (h x).2 = x.1 - x.2 := by
      rw [hformula]
      change x.1 - x.2 - bendGraph (R v) (R u) (min x.1 x.2) = x.1 - x.2
      rw [hm]
      simp [bendGraph]
    rw [hfst]
    constructor
    · rintro (⟨hx0, hx1, hy⟩ | ⟨hx, hy0, hy1⟩)
      · have hm : min x.1 x.2 = 0 := by rw [hy, min_eq_right hx0]
        refine ⟨hm, ?_, ?_⟩ <;> rw [hsnd hm, hy] <;> linarith
      · have hm : min x.1 x.2 = 0 := by rw [hx, min_eq_left hy0]
        refine ⟨hm, ?_, ?_⟩ <;> rw [hsnd hm, hx] <;> linarith
    · rintro ⟨hm, hlo, hhi⟩
      rw [hsnd hm] at hlo hhi
      rcases le_total x.1 x.2 with hle | hle
      · rw [min_eq_left hle] at hm
        exact Or.inr ⟨hm, by linarith, by linarith⟩
      · rw [min_eq_right hle] at hm
        exact Or.inl ⟨by linarith, by linarith, hm⟩

private theorem negative_coordinate_of_affine_height (J : (ℝ × ℝ) →ᵃ[ℝ] ℝ)
    (v : ℝ × ℝ) (hv : J v < J 0) (ha : J 0 ≤ J (1, 0)) (hb : J 0 ≤ J (0, 1)) :
    v.1 < 0 ∨ v.2 < 0 := by
  have hlin (x : ℝ × ℝ) : J.linear x = J x - J 0 := congrFun J.decomp' x
  have hcoords : v = v.1 • (1, 0) + v.2 • (0, 1) := by ext <;> simp
  have hexp : J v - J 0 = v.1 * (J (1, 0) - J 0) + v.2 * (J (0, 1) - J 0) := by
    rw [← hlin v]
    conv_lhs => rw [hcoords, map_add, map_smul, map_smul]
    rw [hlin (1, 0), hlin (0, 1)]
    rfl
  by_contra! h
  have hfirst := mul_nonneg h.1 (sub_nonneg.mpr ha)
  have hsecond := mul_nonneg h.2 (sub_nonneg.mpr hb)
  linarith

private theorem rectangle_sides_spec {X : Type*} [TopologicalSpace X]
    (e : X ≃ₜ (ℝ × ℝ)) (C : Set X) (r : ℝ) (hr : 0 < r)
    (haxis : ∀ x ∈ e ⁻¹' (Ioo (-r) r ×ˢ Ioo (-r) r), x ∈ C ↔ (e x).2 = 0) :
    let W := e ⁻¹' (Ioo (-r) r ×ˢ Ioo (-r) r)
    let A := e ⁻¹' (Ioo (-r) r ×ˢ Ioo (-r) 0)
    let B := e ⁻¹' (Ioo (-r) r ×ˢ Ioo 0 r)
    IsConnected A ∧ IsConnected B ∧ Disjoint A B ∧ A ∪ B = W \ C ∧
      C ∩ W ⊆ closure A ∧ C ∩ W ⊆ closure B := by
  let R : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ Ioo (-r) r
  let A0 : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ Ioo (-r) 0
  let B0 : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ Ioo 0 r
  have hneg : -r < 0 := neg_neg_of_pos hr
  have hwidth : -r < r := hneg.trans hr
  have hAR : A0 ⊆ R := fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.trans hr⟩
  have hBR : B0 ⊆ R := fun _ hx => ⟨hx.1, hneg.trans hx.2.1, hx.2.2⟩
  refine ⟨e.isConnected_preimage.mpr ((isConnected_Ioo hwidth).prod (isConnected_Ioo hneg)),
    e.isConnected_preimage.mpr ((isConnected_Ioo hwidth).prod (isConnected_Ioo hr)),
    ?_, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact (not_lt_of_ge hxA.2.2.le) hxB.2.1
  · apply subset_antisymm
    · rintro x (hx | hx)
      · exact ⟨hAR hx, fun hxC => hx.2.2.ne ((haxis x (hAR hx)).mp hxC)⟩
      · exact ⟨hBR hx, fun hxC => hx.2.1.ne' ((haxis x (hBR hx)).mp hxC)⟩
    · rintro x ⟨hx, hxC⟩
      have hn : (e x).2 ≠ 0 := fun hh => hxC ((haxis x hx).mpr hh)
      rcases hn.lt_or_gt with hn | hp
      · exact Or.inl ⟨hx.1, hx.2.1, hn⟩
      · exact Or.inr ⟨hx.1, hp, hx.2.2⟩
  · rintro x ⟨hxC, hxR⟩
    rw [← e.preimage_closure]
    change e x ∈ closure A0
    rw [closure_prod_eq, closure_Ioo hwidth.ne, closure_Ioo hneg.ne]
    exact ⟨⟨hxR.1.1.le, hxR.1.2.le⟩, by
      rw [(haxis x hxR).mp hxC]
      exact ⟨hneg.le, le_rfl⟩⟩
  · rintro x ⟨hxC, hxR⟩
    rw [← e.preimage_closure]
    change e x ∈ closure B0
    rw [closure_prod_eq, closure_Ioo hwidth.ne, closure_Ioo hr.ne]
    exact ⟨⟨hxR.1.1.le, hxR.1.2.le⟩, by
      rw [(haxis x hxR).mp hxC]
      exact ⟨le_rfl, hr.le⟩⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  {p : Polygon E (n + 2)}

theorem exists_local_alternating_sides_at_arc_vertex
    (hp : IsSimplePolygonalArc p) (k l j : Fin (n + 2))
    (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 1))
    (f : E ≃ᴬ[ℝ] (ℝ × ℝ)) (H : E →ᵃ[ℝ] ℝ)
    (hfk : f (p k) = (0, 0))
    (hfp : f (p ((finRotate (n + 2)).symm k)) = (1, 0))
    (hfs : f (p (finRotate (n + 2) k)) = (0, 1))
    (hpos : 0 < (f (p j)).1 ∧ 0 < (f (p j)).2)
    (hHl : H (p l) < H (p k))
    (hHa : H (p k) ≤ H (p ((finRotate (n + 2)).symm k)))
    (hHb : H (p k) ≤ H (p (finRotate (n + 2) k)))
    (C U V : Set E) (hU : IsOpen U) (hkU : p k ∈ U)
    (hC : ∀ x ∈ U, x ∈ C ↔ x ∈ segment ℝ (p k) (p l) ∪ segment ℝ (p k) (p j))
    (hV : IsOpen V) (hkV : p k ∈ V) :
    let a := p ((finRotate (n + 2)).symm k)
    let b := p (finRotate (n + 2) k)
    let mu := min (f (p l)).1 (f (p l)).2
    let nu := min (f (p j)).1 (f (p j)).2
    ∃ e : E ≃ₜ (ℝ × ℝ), ∃ r eps : ℝ,
      let W := e ⁻¹' (Ioo (-r) r ×ˢ Ioo (-r) r)
      let Cm := e ⁻¹' (Ioo (-r) r ×ˢ Ioo (-r) 0)
      let Cp := e ⁻¹' (Ioo (-r) r ×ˢ Ioo 0 r)
      let Gm := e ⁻¹' (Ioo (-r) 0 ×ˢ Ioo (-r) r)
      let Gp := e ⁻¹' (Ioo 0 r ×ˢ Ioo (-r) r)
      mu < 0 ∧ 0 < nu ∧ e (p k) = 0 ∧
      0 < r ∧ r < 1 ∧ r < -mu ∧ r < nu ∧ 0 < eps ∧ eps < 1 ∧
      IsOpen W ∧ p k ∈ W ∧ W ⊆ U ∩ V ∧
      (∀ x ∈ W, (x ∈ C ↔ (e x).2 = 0) ∧
        (x ∈ polygonArcBoundary p ↔ (e x).1 = 0)) ∧
      IsConnected Cm ∧ IsConnected Cp ∧ Disjoint Cm Cp ∧ Cm ∪ Cp = W \ C ∧
      C ∩ W ⊆ closure Cm ∧ C ∩ W ⊆ closure Cp ∧
      IsConnected Gm ∧ IsConnected Gp ∧ Disjoint Gm Gp ∧
      Gm ∪ Gp = W \ polygonArcBoundary p ∧
      polygonArcBoundary p ∩ W ⊆ closure Gm ∧
      polygonArcBoundary p ∩ W ⊆ closure Gp ∧
      (∀ t : ℝ, 0 ≤ t →
        e (AffineMap.lineMap (p k) a t) = (0, t) ∧
        e (AffineMap.lineMap (p k) b t) = (0, -t) ∧
        e (AffineMap.lineMap (p k) (p l) t) = (t * mu, 0) ∧
        e (AffineMap.lineMap (p k) (p j) t) = (t * nu, 0)) ∧
      (∀ t ∈ Ioo 0 eps,
        AffineMap.lineMap (p k) a t ∈ Cp ∧ AffineMap.lineMap (p k) b t ∈ Cm ∧
        AffineMap.lineMap (p k) (p l) t ∈ Gm ∧
        AffineMap.lineMap (p k) (p j) t ∈ Gp) := by
  let a := p ((finRotate (n + 2)).symm k)
  let b := p (finRotate (n + 2) k)
  let mu := min (f (p l)).1 (f (p l)).2
  let nu := min (f (p j)).1 (f (p j)).2
  let J : (ℝ × ℝ) →ᵃ[ℝ] ℝ := H.comp f.symm.toAffineEquiv.toAffineMap
  have hJ (x : E) : J (f x) = H x := by
    change H (f.symm (f x)) = H x
    rw [f.symm_apply_apply]
  have hJ0 : J 0 = H (p k) := by
    change J (0, 0) = H (p k)
    rw [← hfk, hJ]
  have hJa : J (1, 0) = H a := by simpa only [a, hfp] using hJ a
  have hJb : J (0, 1) = H b := by simpa only [b, hfs] using hJ b
  have hvneg : (f (p l)).1 < 0 ∨ (f (p l)).2 < 0 :=
    negative_coordinate_of_affine_height J (f (p l))
      (by rw [hJ, hJ0]; exact hHl) (by rw [hJ0, hJa]; exact hHa)
      (by rw [hJ0, hJb]; exact hHb)
  have hmu : mu < 0 := min_lt_iff.mpr hvneg
  have hnu : 0 < nu := lt_min hpos.1 hpos.2
  obtain ⟨h, hzero, _, hrays, haux, hcorner⟩ :=
    exists_homeomorph_corner_crossing (f (p j)) (f (p l)) hpos hvneg
  let e := f.toHomeomorph.trans h
  have he0 : e (p k) = 0 := by
    change h (f (p k)) = 0
    rw [hfk]
    exact hzero
  have hline (z : E) (t : ℝ) : f (AffineMap.lineMap (p k) z t) = t • f z := by
    have hh := f.toAffineEquiv.toAffineMap.apply_lineMap (p k) z t
    change f (AffineMap.lineMap (p k) z t) = AffineMap.lineMap (f (p k)) (f z) t at hh
    rw [hh, hfk]
    simp [AffineMap.lineMap_apply_module]
  have herays (t : ℝ) (ht : 0 ≤ t) :
      e (AffineMap.lineMap (p k) a t) = (0, t) ∧
      e (AffineMap.lineMap (p k) b t) = (0, -t) ∧
      e (AffineMap.lineMap (p k) (p l) t) = (t * mu, 0) ∧
      e (AffineMap.lineMap (p k) (p j) t) = (t * nu, 0) := by
    change h (f (AffineMap.lineMap (p k) a t)) = (0, t) ∧
      h (f (AffineMap.lineMap (p k) b t)) = (0, -t) ∧
      h (f (AffineMap.lineMap (p k) (p l) t)) = (t * mu, 0) ∧
      h (f (AffineMap.lineMap (p k) (p j) t)) = (t * nu, 0)
    have hfa : f a = (1, 0) := hfp
    have hfb : f b = (0, 1) := hfs
    simp only [hline, hfa, hfb, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero]
    exact hrays t ht
  have htrans (z x : E) : x ∈ segment ℝ (p k) z ↔ f x ∈ segment ℝ 0 (f z) := by
    have him : f '' segment ℝ (p k) z = segment ℝ (f (p k)) (f z) :=
      image_segment ℝ f.toAffineEquiv.toAffineMap _ _
    have hfzero : f (p k) = 0 := hfk
    rw [hfzero] at him
    rw [← him]
    exact ⟨fun hx => mem_image_of_mem f hx, fun ⟨y, hy, heq⟩ => f.injective heq ▸ hy⟩
  obtain ⟨ei, ej, hik, hjk, hip, hjs, _⟩ := exists_arc_incident_edge_indices k hk0 hkl
  have hei : p.edgeSet ℝ ei.castSucc = segment ℝ (p k) a := by
    rw [polygon_arcEdge_eq_segment, hip, hik, segment_symm]
  have hej : p.edgeSet ℝ ej.castSucc = segment ℝ (p k) b := by
    rw [polygon_arcEdge_eq_segment, hjk, hjs]
  obtain ⟨UG, hUG, hkUG, hUGeq⟩ := exists_open_iUnion_eq_of_mem_imp
    (fun i : Fin (n + 1) => p.edgeSet ℝ i.castSucc)
    (fun i => (polygon_edgeSet_isCompact p i.castSucc).isClosed) {ei, ej} (p k) (by
      intro i hi
      rcases (hp.vertex_mem_edgeSet_iff k i).mp hi with hi | hi
      · right
        apply Fin.ext
        have hh := congrArg (fun x : Fin (n + 2) => x.val) (hi.symm.trans hjk.symm)
        exact hh
      · left
        apply Fin.ext
        have hh := congrArg Fin.val (hi.symm.trans hik.symm)
        simpa only [Fin.val_succ, Nat.add_right_cancel_iff] using hh)
  have hGlocal (x : E) (hx : x ∈ UG) : x ∈ polygonArcBoundary p ↔ f x ∈ unitCorner := by
    have hfa : f a = (1, 0) := hfp
    have hfb : f b = (0, 1) := hfs
    constructor
    · intro hxG
      obtain ⟨i, hi, hxi⟩ := (hUGeq x hx).mp hxG
      rcases hi with rfl | rfl
      · exact Or.inl (hfa ▸ (htrans a x).mp (hei ▸ hxi))
      · exact Or.inr (hfb ▸ (htrans b x).mp (hej ▸ hxi))
    · intro hxG
      apply (hUGeq x hx).mpr
      rcases hxG with hxG | hxG
      · exact ⟨ei, Or.inl rfl, hei.symm ▸ (htrans a x).mpr (hfa.symm ▸ hxG)⟩
      · exact ⟨ej, Or.inr rfl, hej.symm ▸ (htrans b x).mpr (hfb.symm ▸ hxG)⟩
  let Omega := (U ∩ UG) ∩ V
  obtain ⟨rho, hrho, hball⟩ := Metric.isOpen_iff.mp
    (e.isOpenMap Omega ((hU.inter hUG).inter hV)) (e (p k))
    (mem_image_of_mem e ⟨⟨hkU, hkUG⟩, hkV⟩)
  let m0 := min rho (min 1 (min (-mu) nu))
  have hm0 : 0 < m0 := lt_min hrho (lt_min (by norm_num) (lt_min (neg_pos.mpr hmu) hnu))
  let r := m0 / 2
  have hr : 0 < r := div_pos hm0 (by norm_num)
  have hrm : r < m0 := by dsimp [r]; linarith
  have hrrho : r < rho := hrm.trans_le (min_le_left _ _)
  have hr1 : r < 1 := hrm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrmu : r < -mu := hrm.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrnu : r < nu := hrm.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let W := e ⁻¹' (Ioo (-r) r ×ˢ Ioo (-r) r)
  let Cm := e ⁻¹' (Ioo (-r) r ×ˢ Ioo (-r) 0)
  let Cp := e ⁻¹' (Ioo (-r) r ×ˢ Ioo 0 r)
  let Gm := e ⁻¹' (Ioo (-r) 0 ×ˢ Ioo (-r) r)
  let Gp := e ⁻¹' (Ioo 0 r ×ˢ Ioo (-r) r)
  have hRball : (Ioo (-r) r ×ˢ Ioo (-r) r : Set (ℝ × ℝ)) = ball 0 r := by
    change _ = ball ((0 : ℝ), 0) r
    rw [← ball_prod_same, Real.ball_zero_eq_Ioo]
  have hWO : W ⊆ Omega := by
    intro x hx
    have hxr : e x ∈ ball 0 r := hRball ▸ hx
    have hxr' : e x ∈ ball (e (p k)) rho := by
      rw [he0]
      exact ball_subset_ball hrrho.le hxr
    obtain ⟨z, hz, heq⟩ := hball hxr'
    exact e.injective heq ▸ hz
  have hW : IsOpen W := (isOpen_Ioo.prod isOpen_Ioo).preimage e.continuous
  have hkW : p k ∈ W := by
    change e (p k) ∈ Ioo (-r) r ×ˢ Ioo (-r) r
    rw [he0]
    exact ⟨⟨neg_neg_of_pos hr, hr⟩, neg_neg_of_pos hr, hr⟩
  have hCaxis (x : E) (hx : x ∈ W) : x ∈ C ↔ (e x).2 = 0 := by
    have hlo : mu ≤ (e x).1 := by have hh := hx.1.1; linarith
    have hhi : (e x).1 ≤ nu := hx.1.2.le.trans hrnu.le
    rw [hC x (hWO hx).1.1, mem_union, htrans (p l) x, htrans (p j) x,
      ← mem_union, haux (f x)]
    exact ⟨fun hh => hh.2.2, fun hh => ⟨hlo, hhi, hh⟩⟩
  have hGaxis (x : E) (hx : x ∈ W) :
      x ∈ polygonArcBoundary p ↔ (e x).1 = 0 := by
    have hlo : -1 ≤ (e x).2 := by have hh := hx.2.1; linarith
    have hhi : (e x).2 ≤ 1 := hx.2.2.le.trans hr1.le
    rw [hGlocal x (hWO hx).1.2, hcorner (f x)]
    exact ⟨fun hh => hh.1, fun hh => ⟨hh, hlo, hhi⟩⟩
  obtain ⟨hCm, hCp, hCd, hCu, hClm, hClp⟩ := rectangle_sides_spec e C r hr hCaxis
  let es := e.trans (Homeomorph.prodComm ℝ ℝ)
  have hWs : es ⁻¹' (Ioo (-r) r ×ˢ Ioo (-r) r) = W := by
    ext x
    change ((e x).2 ∈ Ioo (-r) r ∧ (e x).1 ∈ Ioo (-r) r) ↔
      ((e x).1 ∈ Ioo (-r) r ∧ (e x).2 ∈ Ioo (-r) r)
    exact and_comm
  have hGms : es ⁻¹' (Ioo (-r) r ×ˢ Ioo (-r) 0) = Gm := by
    ext x
    change ((e x).2 ∈ Ioo (-r) r ∧ (e x).1 ∈ Ioo (-r) 0) ↔
      ((e x).1 ∈ Ioo (-r) 0 ∧ (e x).2 ∈ Ioo (-r) r)
    exact and_comm
  have hGps : es ⁻¹' (Ioo (-r) r ×ˢ Ioo 0 r) = Gp := by
    ext x
    change ((e x).2 ∈ Ioo (-r) r ∧ (e x).1 ∈ Ioo 0 r) ↔
      ((e x).1 ∈ Ioo 0 r ∧ (e x).2 ∈ Ioo (-r) r)
    exact and_comm
  have hGside := rectangle_sides_spec es (polygonArcBoundary p) r hr
    (fun x hx => hGaxis x (hWs ▸ hx))
  dsimp only at hGside
  rw [hWs, hGms, hGps] at hGside
  obtain ⟨hGm, hGp, hGd, hGu, hGlm, hGlp⟩ := hGside
  let D := 1 + |mu| + nu
  have hD : 1 < D := by dsimp [D]; linarith [abs_nonneg mu]
  have hDpos : 0 < D := lt_trans (by norm_num) hD
  have hden : 0 < 2 * D := mul_pos (by norm_num) hDpos
  let eps := r / (2 * D)
  have heps : 0 < eps := div_pos hr hden
  have hepsr : eps < r / 2 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [mul_pos hr (sub_pos.mpr hD)]
  have heps1 : eps < 1 := hepsr.trans (by linarith)
  refine ⟨e, r, eps, hmu, hnu, he0, hr, hr1, hrmu, hrnu, heps, heps1,
    hW, hkW, fun x hx => ⟨(hWO hx).1.1, (hWO hx).2⟩,
    fun x hx => ⟨hCaxis x hx, hGaxis x hx⟩,
    hCm, hCp, hCd, hCu, hClm, hClp, hGm, hGp, hGd, hGu, hGlm, hGlp, herays, ?_⟩
  intro t ht
  have htr : t < r := ht.2.trans (hepsr.trans (by linarith))
  have htD : t * (2 * D) < r := (lt_div_iff₀ hden).mp ht.2
  have hmuD : |mu| < 2 * D := by dsimp [D]; linarith [abs_nonneg mu]
  have hnuD : nu < 2 * D := by dsimp [D]; linarith [abs_nonneg mu]
  have hmut : |mu| * t < r := by
    rw [mul_comm]
    exact (mul_lt_mul_of_pos_left hmuD ht.1).trans htD
  have hnut : nu * t < r := by
    rw [mul_comm]
    exact (mul_lt_mul_of_pos_left hnuD ht.1).trans htD
  have hmutlo : -r < t * mu := by rw [abs_of_neg hmu] at hmut; nlinarith
  have hmuthi : t * mu < 0 := mul_neg_of_pos_of_neg ht.1 hmu
  have hnutlo : 0 < t * nu := mul_pos ht.1 hnu
  have hnuthi : t * nu < r := by rwa [mul_comm]
  obtain ⟨ha, hb, hl, hj⟩ := herays t ht.1.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · change e (AffineMap.lineMap (p k) a t) ∈ Ioo (-r) r ×ˢ Ioo 0 r
    rw [ha]
    exact ⟨⟨neg_neg_of_pos hr, hr⟩, ht.1, htr⟩
  · change e (AffineMap.lineMap (p k) b t) ∈ Ioo (-r) r ×ˢ Ioo (-r) 0
    rw [hb]
    exact ⟨⟨neg_neg_of_pos hr, hr⟩, neg_lt_neg htr, neg_neg_of_pos ht.1⟩
  · change e (AffineMap.lineMap (p k) (p l) t) ∈ Ioo (-r) 0 ×ˢ Ioo (-r) r
    rw [hl]
    exact ⟨⟨hmutlo, hmuthi⟩, neg_neg_of_pos hr, hr⟩
  · change e (AffineMap.lineMap (p k) (p j) t) ∈ Ioo 0 r ×ˢ Ioo (-r) r
    rw [hj]
    exact ⟨⟨hnutlo, hnuthi⟩, neg_neg_of_pos hr, hr⟩

end PoincareConjecture.M25.Topology3D
