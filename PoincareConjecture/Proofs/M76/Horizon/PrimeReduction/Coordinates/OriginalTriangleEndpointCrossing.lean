import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.OriginalTriangleEdgeGerm
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VerticalTriangleGerm
import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

private theorem triangle_intrinsicFrontier_eq_edges
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (K : SimplicialComplex ℝ E) {p q w : E}
    (hpq : p ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (ht : ({w, p, q} : Finset E) ∈ K.faces) :
    intrinsicFrontier ℝ (convexHull ℝ ({w, p, q} : Set E)) =
      segment ℝ p q ∪ (segment ℝ w q ∪ segment ℝ w p) := by
  ext x
  have hh := (K.indep ht).mem_intrinsicFrontier_convexHull_finset
    (K.nonempty_of_mem_faces ht) x
  have hp : ({w, p, q} : Set E) \ {p} = {w, q} := by ext z; simp; aesop
  have hq : ({w, p, q} : Set E) \ {q} = {w, p} := by ext z; simp; aesop
  simpa [hpq, hwp, hwq, hpq.symm, hwp.symm, hwq.symm, convexHull_pair,
    hp, hq, or_assoc] using hh

private theorem exists_ray_coordinates {u : V2} (hu : u ≠ 0) :
    ∃ L : V2 ≃L[ℝ] V2, L u = (0, 1) := by
  let d := u.1 * u.1 + u.2 * u.2
  have hd : d ≠ 0 := by
    intro h
    have h1 : u.1 = 0 := by dsimp only [d] at h; nlinarith [sq_nonneg u.2]
    have h2 : u.2 = 0 := by dsimp only [d] at h; nlinarith [sq_nonneg u.1]
    exact hu (Prod.ext h1 h2)
  let f : V2 →ₗ[ℝ] V2 :=
    { toFun := fun x => (u.2 * x.1 - u.1 * x.2, (u.1 * x.1 + u.2 * x.2) / d)
      map_add' := by intro x y; ext <;> dsimp <;> ring
      map_smul' := by intro r x; ext <;> dsimp <;> ring }
  let g : V2 → V2 := fun x => (u.2 / d * x.1 + u.1 * x.2,
    -u.1 / d * x.1 + u.2 * x.2)
  let L : V2 ≃ₗ[ℝ] V2 :=
    { f with
      invFun := g
      left_inv := by
        intro x
        apply Prod.ext <;> dsimp only [f, g, LinearMap.coe_mk, AddHom.coe_mk]
        all_goals field_simp [hd]; dsimp only [d]; ring
      right_inv := by
        intro x
        apply Prod.ext <;> dsimp only [f, g, LinearMap.coe_mk, AddHom.coe_mk]
        all_goals field_simp [hd]; dsimp only [d]; ring }
  refine ⟨L.toContinuousLinearEquiv, ?_⟩
  change (u.2 * u.1 - u.1 * u.2, d / d) = (0, 1)
  rw [div_self hd]
  congr 1
  ring

private theorem edge_chart_endpoints_on_axis
    (F : C3 ≃ᴬ[ℝ] V3) {p q y : V3} {V : Set V3}
    (hF : F 0 = y) (hV : IsOpen V) (hyV : y ∈ V)
    (hy : y ∈ segment ℝ p q)
    (haxis : ∀ x ∈ V, x ∈ segment ℝ p q → (F.symm x).1 = 0) :
    (F.symm p).1 = 0 ∧ (F.symm q).1 = 0 := by
  have hy0 : F.symm y = 0 := by rw [← hF, F.symm_apply_apply]
  have each (v : V3) (hv : v ∈ segment ℝ p q) : (F.symm v).1 = 0 := by
    have hopen : IsOpen ((AffineMap.lineMap y v : ℝ → V3) ⁻¹' V) :=
      hV.preimage (lipschitzWith_lineMap y v).continuous
    have hzero : (0 : ℝ) ∈ (AffineMap.lineMap y v : ℝ → V3) ⁻¹' V := by
      simpa only [mem_preimage, AffineMap.lineMap_apply_zero] using hyV
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
    let t := min (δ / 2) (1 / 2)
    have ht : 0 < t := lt_min (half_pos hδ) (by norm_num)
    have ht1 : t < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have htV : AffineMap.lineMap y v t ∈ V := hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
      exact (min_le_left _ _).trans_lt (half_lt_self hδ))
    have hfirst := haxis _ htV ((convex_segment p q).segment_subset hy hv
      (lineMap_mem_segment ℝ y v ⟨ht.le, ht1.le⟩))
    change (F.symm.toAffineEquiv.toAffineMap (AffineMap.lineMap y v t)).1 = 0 at hfirst
    rw [AffineMap.apply_lineMap] at hfirst
    change (AffineMap.lineMap (F.symm y) (F.symm v) t).1 = 0 at hfirst
    rw [hy0] at hfirst
    simp only [AffineMap.lineMap_apply_module, smul_zero, zero_add] at hfirst
    have hmul : t • (F.symm v).1 = 0 := hfirst
    exact (smul_eq_zero.mp hmul).resolve_left ht.ne'
  exact ⟨each p (left_mem_segment ℝ _ _), each q (right_mem_segment ℝ _ _)⟩




theorem exists_edge_chart_triangle_halfplane
    (F : C3 ≃ᴬ[ℝ] V3) {p q w y : V3} {V : Set V3}
    (hF : F 0 = y) (hV : IsOpen V) (hyV : y ∈ V)
    (hy : y ∈ openSegment ℝ p q) (hpq : p ≠ q)
    (haxis : ∀ x ∈ V, x ∈ segment ℝ p q → (F.symm x).1 = 0)
    (hw : w ∉ affineSpan ℝ ({p, q} : Set V3)) :
    ∃ (T : C3 ≃ᴬ[ℝ] V3) (U : Set V3),
      IsOpen U ∧ y ∈ U ∧ U ⊆ V ∧ T 0 = y ∧
      (∀ z, (F.symm (T z)).2 = z.2) ∧
      (∀ z, (F.symm (T z)).1 = 0 ↔ z.1 = 0) ∧
      ∀ x ∈ U,
        x ∈ convexHull ℝ ({p, q, w} : Set V3) ↔
          (T.symm x).1.1 = 0 ∧ 0 ≤ (T.symm x).1.2 := by
  have hy0 : F.symm y = 0 := by rw [← hF, F.symm_apply_apply]
  obtain ⟨hp0, hq0⟩ := edge_chart_endpoints_on_axis F hF hV hyV
    (openSegment_subset_segment ℝ p q hy) haxis
  have hpcoord : F.symm p = (0, (F.symm p).2) := Prod.ext hp0 rfl
  have hqcoord : F.symm q = (0, (F.symm q).2) := Prod.ext hq0 rfl
  have hpqheight : (F.symm p).2 ≠ (F.symm q).2 := by
    intro h
    exact hpq (F.symm.injective (hpcoord.trans ((congrArg (fun t : ℝ => ((0 : V2), t)) h).trans hqcoord.symm)))
  have hw0 : (F.symm w).1 ≠ 0 := by
    intro hw0
    apply hw
    apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
    refine ⟨((F.symm w).2 - (F.symm p).2) / ((F.symm q).2 - (F.symm p).2), ?_⟩
    apply F.symm.injective
    change F.symm.toAffineEquiv.toAffineMap (AffineMap.lineMap p q _) = _
    rw [AffineMap.apply_lineMap]
    change AffineMap.lineMap (F.symm p) (F.symm q) _ = F.symm w
    apply Prod.ext
    · simpa [AffineMap.lineMap_apply_module, hp0, hq0] using hw0.symm
    · rw [AffineMap.lineMap_apply_module]
      change (1 - ((F.symm w).2 - (F.symm p).2) / ((F.symm q).2 - (F.symm p).2)) *
          (F.symm p).2 + (((F.symm w).2 - (F.symm p).2) /
          ((F.symm q).2 - (F.symm p).2)) * (F.symm q).2 = (F.symm w).2
      field_simp [sub_ne_zero.mpr hpqheight.symm]
      ring
  obtain ⟨L, hLu⟩ := exists_ray_coordinates hw0
  let N := (L.toContinuousAffineEquiv.prodCongr (ContinuousAffineEquiv.refl ℝ ℝ))
  let T := N.symm.trans F
  have hTzero : T 0 = y := by
    change F (N.symm 0) = y
    change F (L.symm 0, (0 : ℝ)) = y
    rw [map_zero]
    exact hF
  have hheight (z : C3) : (F.symm (T z)).2 = z.2 := by
    change (F.symm (F (N.symm z))).2 = z.2
    rw [F.symm_apply_apply]
    rfl
  have hfirst (z : C3) : (F.symm (T z)).1 = 0 ↔ z.1 = 0 := by
    change (F.symm (F (N.symm z))).1 = 0 ↔ z.1 = 0
    rw [F.symm_apply_apply]
    change L.symm z.1 = 0 ↔ z.1 = 0
    exact L.symm.map_eq_zero_iff
  have hends := edge_chart_height_nonzero F hF hV hyV hy hpq haxis
  obtain ⟨t, ht, hty⟩ := (openSegment_eq_image_lineMap ℝ p q).symm ▸ hy
  have hcomb : (1 - t) * (F.symm p).2 + t * (F.symm q).2 = 0 := by
    rw [← hty] at hy0
    have hh := congrArg Prod.snd hy0
    change (F.symm.toAffineEquiv.toAffineMap (AffineMap.lineMap p q t)).2 = 0 at hh
    rw [AffineMap.apply_lineMap] at hh
    change (AffineMap.lineMap (F.symm p) (F.symm q) t).2 = 0 at hh
    rw [AffineMap.lineMap_apply_module] at hh
    exact hh
  have hopposite : ((F.symm p).2 < 0 ∧ 0 < (F.symm q).2) ∨
      ((F.symm q).2 < 0 ∧ 0 < (F.symm p).2) := by
    rcases lt_or_gt_of_ne hends.1 with hp | hp
    · left
      refine ⟨hp, ?_⟩
      by_contra! hq
      nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr ht.2) hp,
        mul_nonpos_of_nonneg_of_nonpos ht.1.le hq]
    · right
      refine ⟨?_, hp⟩
      by_contra! hq
      nlinarith [mul_pos (sub_pos.mpr ht.2) hp, mul_nonneg ht.1.le hq]
  have hgerm : ∃ O : Set C3, IsOpen O ∧ (0 : C3) ∈ O ∧
      ∀ z ∈ O, z ∈ convexHull ℝ ({F.symm p, F.symm q, F.symm w} : Set C3) ↔
        ∃ r : ℝ, 0 ≤ r ∧ z.1 = r • (F.symm w).1 := by
    have hset : ({F.symm p, F.symm q, F.symm w} : Set C3) =
        {(0, (F.symm p).2), (0, (F.symm q).2), ((F.symm w).1, (F.symm w).2)} := by
      conv_lhs => rw [hpcoord, hqcoord]
    rw [hset]
    rcases hopposite with ⟨hp, hq⟩ | ⟨hq, hp⟩
    · exact exists_open_vertical_triangle_germ hw0 hp hq (F.symm w).2
    · obtain ⟨O, hO, hzero, hlocal⟩ := exists_open_vertical_triangle_germ hw0 hq hp (F.symm w).2
      refine ⟨O, hO, hzero, ?_⟩
      intro z hz
      simpa only [insert_comm] using hlocal z hz
  obtain ⟨O, hO, hzero, hlocal⟩ := hgerm
  refine ⟨T, V ∩ F '' O, hV.inter (F.toHomeomorph.isOpenMap _ hO),
    ⟨hyV, 0, hzero, hF⟩, inter_subset_left, hTzero, hheight, hfirst, ?_⟩
  intro x hx
  have hxO : F.symm x ∈ O := by
    obtain ⟨z, hz, rfl⟩ := hx.2
    simpa only [F.symm_apply_apply] using hz
  have htri : x ∈ convexHull ℝ ({p, q, w} : Set V3) ↔
      F.symm x ∈ convexHull ℝ ({F.symm p, F.symm q, F.symm w} : Set C3) := by
    have himage := F.symm.toAffineEquiv.toAffineMap.image_convexHull ({p, q, w} : Set V3)
    change F.symm '' _ = convexHull ℝ (F.symm '' ({p, q, w} : Set V3)) at himage
    simp only [image_insert_eq, image_singleton] at himage
    rw [← himage]
    exact F.symm.injective.mem_set_image.symm
  rw [htri, hlocal _ hxO]
  have hcoord : (T.symm x).1 = L (F.symm x).1 := rfl
  rw [hcoord]
  constructor
  · rintro ⟨r, hr, hxr⟩
    rw [hxr, map_smul, hLu]
    simpa using hr
  · intro hx
    refine ⟨(L (F.symm x).1).2, hx.2, L.injective ?_⟩
    rw [map_smul, hLu]
    exact Prod.ext (by simpa using hx.1) (by simp)





theorem HasOriginalEdgeCofaceCharts.exists_triangle_endpoint_crossing_of_not_vertex
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {p q w : E}
    (h : HasOriginalEdgeCofaceCharts e S K g {p, q})
    (hgi : InjOn g K.space) {y : X} (hyvertex : y ∉ g '' K.vertices)
    (hpq : p ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (ht : ({w, p, q} : Finset E) ∈ K.faces)
    (hy : y ∈ S ∩ (g '' segment ℝ p q)) :
    ∃ (B : OpenPartialHomeomorph X V3) (V : Set V3) (T : C3 ≃ᴬ[ℝ] V3),
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      y ∈ B.source ∧ IsOpen V ∧ B y ∈ V ∧ V ⊆ B.target ∧ T 0 = B y ∧
      (∀ z, T z ∈ V → (B.symm (T z) ∈ S ↔ z.2 = 0)) ∧
      (∀ z, T z ∈ V →
        (B.symm (T z) ∈ g '' convexHull ℝ ({w, p, q} : Set E) ↔
          z.1.1 = 0 ∧ 0 ≤ z.1.2)) ∧
      (∀ z, T z ∈ V → (B.symm (T z) ∈ g '' segment ℝ p q ↔ z.1 = 0)) ∧
      (∀ z, T z ∈ V →
        (B.symm (T z) ∈ g '' intrinsicFrontier ℝ (convexHull ℝ ({w, p, q} : Set E)) ↔
          z.1 = 0)) := by
  classical
  have hat : ({p, q} : Finset E) ⊆ {w, p, q} := by simp
  have ha : ({p, q} : Finset E) ∈ K.faces :=
    K.down_closed ht hat (Finset.insert_nonempty _ _)
  have hypred : y ∈ S ∩ (g '' convexHull ℝ (({p, q} : Finset E) : Set E)) := by
    simpa only [Finset.coe_pair, convexHull_pair] using hy
  obtain ⟨B, V, F, hB, hyB, hV, hyV, hVB, hF, hFS, hFL, hco⟩ := h y hypred
  obtain ⟨hmap, A, hA⟩ := hco {w, p, q} ht hat
  have hA' : EqOn (B ∘ g) A (convexHull ℝ ({w, p, q} : Set E)) := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using hA
  have hmap' : MapsTo g (convexHull ℝ ({w, p, q} : Set E)) B.source := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using hmap
  have hTspace : convexHull ℝ ({w, p, q} : Set E) ⊆ K.space := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using K.convexHull_subset_space ht
  have hsegsub : segment ℝ p q ⊆ convexHull ℝ ({w, p, q} : Set E) := by
    rw [← convexHull_pair]
    exact convexHull_mono (by intro x hx; exact Or.inr hx)
  have hAi : InjOn A.toAffineMap (convexHull ℝ ({w, p, q} : Set E)) := by
    intro x hx x' hx' heq
    exact hgi (hTspace hx) (hTspace hx')
      (B.injOn (hmap' hx) (hmap' hx') ((hA' hx).trans (heq.trans (hA' hx').symm)))
  have hsourceEdge : MapsTo g (segment ℝ p q) B.source := hmap'.mono_left hsegsub
  have hedge : (B ∘ g) '' segment ℝ p q = segment ℝ (A p) (A q) := by
    calc
      _ = A.toAffineMap '' segment ℝ p q := image_congr (fun x hx => hA' (hsegsub hx))
      _ = _ := image_segment ℝ A.toAffineMap p q
  have hphysical (x : V3) (hx : x ∈ B.target) :
      B.symm x ∈ g '' segment ℝ p q ↔ x ∈ segment ℝ (A p) (A q) := by
    constructor
    · rintro ⟨u, hu, heq⟩
      rw [← hedge]
      exact ⟨u, hu, by change B (g u) = x; rw [heq, B.right_inv hx]⟩
    · intro hxe
      obtain ⟨u, hu, heq⟩ := hedge.symm.subset hxe
      refine ⟨u, hu, ?_⟩
      rw [← heq]
      exact (B.left_inv (hsourceEdge hu)).symm
  have hyseg : B y ∈ segment ℝ (A p) (A q) :=
    (hphysical (B y) (B.map_source hyB)).mp (by simpa only [B.left_inv hyB] using hy.2)
  have hvertex_ne (v : E) (hv : v ∈ ({p, q} : Finset E)) : A v ≠ B y := by
    have hve : v ∈ segment ℝ p q := by
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact left_mem_segment ℝ _ _
      · exact Finset.mem_singleton.mp hv ▸ right_mem_segment ℝ _ _
    intro heq
    have hgy : g v = y := B.injOn (hsourceEdge hve) hyB ((hA' (hsegsub hve)).trans heq)
    exact hyvertex ⟨v, K.face_subset_vertices ha hv, hgy⟩
  have hyopen : B y ∈ openSegment ℝ (A p) (A q) :=
    mem_openSegment_of_ne_left_right (hvertex_ne p (by simp)) (hvertex_ne q (by simp)) hyseg
  have hApq : A p ≠ A q := fun heq => hpq (hAi
    (hsegsub (left_mem_segment ℝ p q)) (hsegsub (right_mem_segment ℝ p q)) heq)
  have hrange : range ((↑) : ({w, p, q} : Finset E) → E) = ({w, p, q} : Set E) := by
    rw [Subtype.range_coe]
    simp only [Finset.coe_insert, Finset.coe_singleton]
  have hind := A.toAffineMap.affineIndependent_comp_of_injOn_convexHull
    (p := ((↑) : ({w, p, q} : Finset E) → E)) (K.indep ht)
    (by rw [hrange]; exact hAi)
  let ip : ({w, p, q} : Finset E) := ⟨p, by simp⟩
  let iq : ({w, p, q} : Finset E) := ⟨q, by simp⟩
  let iw : ({w, p, q} : Finset E) := ⟨w, by simp⟩
  have hnot := hind.notMem_affineSpan_sdiff iw {ip, iq}
  have hset : ({ip, iq} : Set ({w, p, q} : Finset E)) \ {iw} = {ip, iq} := by
    apply sdiff_eq_left.mpr
    apply disjoint_singleton_right.mpr
    simp [ip, iq, iw, Subtype.ext_iff, hwp, hwq]
  rw [hset, image_pair] at hnot
  change A w ∉ affineSpan ℝ ({A p, A q} : Set V3) at hnot
  have haxis (x : V3) (hx : x ∈ V) (hxe : x ∈ segment ℝ (A p) (A q)) :
      (F.symm x).1 = 0 := by
    have hh := hFL (F.symm x) (by simpa only [F.apply_symm_apply] using hx)
    apply hh.mp
    simpa only [F.apply_symm_apply, Finset.coe_pair, convexHull_pair] using
      (hphysical x (hVB hx)).mpr hxe
  obtain ⟨T, U, hU, hyU, hUV, hT, hheight, haxisT, htri⟩ :=
    exists_edge_chart_triangle_halfplane F hF hV hyV hyopen hApq haxis hnot
  have htriangle : (B ∘ g) '' convexHull ℝ ({w, p, q} : Set E) =
      convexHull ℝ ({A p, A q, A w} : Set V3) := by
    calc
      _ = A.toAffineMap '' convexHull ℝ ({w, p, q} : Set E) := image_congr hA'
      _ = convexHull ℝ ({A w, A p, A q} : Set V3) := by
        rw [A.toAffineMap.image_convexHull, image_insert_eq, image_pair]
        rfl
      _ = _ := by congr 1; ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto
  have hother_sub (v : E) (hv : v = p ∨ v = q) :
      segment ℝ w v ⊆ convexHull ℝ ({w, p, q} : Set E) := by
    rw [← convexHull_pair]
    apply convexHull_mono
    rintro z (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr hv
  have hother_image (v : E) (hv : v = p ∨ v = q) :
      (B ∘ g) '' segment ℝ w v = segment ℝ (A w) (A v) := by
    calc
      _ = A.toAffineMap '' segment ℝ w v := image_congr (fun x hx => hA' (hother_sub v hv hx))
      _ = _ := image_segment ℝ A.toAffineMap w v
  have hnotother (v : E) (hv : v = p ∨ v = q) : B y ∉ segment ℝ (A w) (A v) := by
    intro hyother
    obtain ⟨x, hx, hxy⟩ := hy.2
    obtain ⟨x', hx', hx'y⟩ := (hother_image v hv).symm.subset hyother
    have hxy' : B (g x) = B y := congrArg B hxy
    have hxx' : x = x' := hAi (hsegsub hx) (hother_sub v hv hx')
      ((hA' (hsegsub hx)).symm.trans (hxy'.trans
        (hx'y.symm.trans (hA' (hother_sub v hv hx')))))
    have hvface : ({w, v} : Finset E) ∈ K.faces := K.down_closed ht
      (by rcases hv with rfl | rfl <;> simp) (Finset.insert_nonempty _ _)
    have hmeet := K.inter_subset_convexHull ha hvface
      ⟨by simpa only [Finset.coe_pair, convexHull_pair] using hx,
        by simpa only [Finset.coe_pair, convexHull_pair, hxx'] using hx'⟩
    have hinter : ({p, q} : Set E) ∩ {w, v} ⊆ {v} := by
      rintro z ⟨hz, rfl | hz⟩
      · rcases hz with hp | hq
        · exact (hwp hp).elim
        · exact (hwq hq).elim
      · exact hz
    have hxv : x = v := by
      have hm : x ∈ convexHull ℝ (({p, q} : Set E) ∩ {w, v}) := by
        simpa only [Finset.coe_pair] using hmeet
      simpa only [convexHull_singleton, mem_singleton_iff] using
        convexHull_mono hinter hm
    exact hyvertex
      ⟨v, K.face_subset_vertices ha (by simpa using hv), hxv ▸ hxy⟩
  let D := segment ℝ (A w) (A p) ∪ segment ℝ (A w) (A q)
  have hD : IsClosed D := by
    apply IsClosed.union
    · simpa only [convexHull_pair] using
        ((Set.toFinite ({A w, A p} : Set V3)).isCompact_convexHull ℝ).isClosed
    · simpa only [convexHull_pair] using
        ((Set.toFinite ({A w, A q} : Set V3)).isCompact_convexHull ℝ).isClosed
  have hyD : B y ∉ D := fun hh => hh.elim
    (hnotother p (Or.inl rfl)) (hnotother q (Or.inr rfl))
  have hnewV : U ∩ Dᶜ ⊆ B.target := inter_subset_left.trans (hUV.trans hVB)
  have hedgeT (z : C3) (hz : T z ∈ U) :
      B.symm (T z) ∈ g '' segment ℝ p q ↔ z.1 = 0 := by
    have hh := hFL (F.symm (T z)) (by simpa only [F.apply_symm_apply] using hUV hz)
    have heq : B.symm (T z) ∈ g '' segment ℝ p q ↔ (F.symm (T z)).1 = 0 := by
      simpa only [F.apply_symm_apply, Finset.coe_pair, convexHull_pair] using hh
    exact heq.trans (haxisT z)
  refine ⟨B, U ∩ Dᶜ, T, hB, hyB, hU.inter hD.isOpen_compl, ⟨hyU, hyD⟩,
    hnewV, hT, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hh := hFS (F.symm (T z)) (by simpa only [F.apply_symm_apply] using hUV hz.1)
    simpa only [F.apply_symm_apply, hheight] using hh
  · intro z hz
    have hTx := hnewV hz
    have heq : B.symm (T z) ∈ g '' convexHull ℝ ({w, p, q} : Set E) ↔
        T z ∈ convexHull ℝ ({A p, A q, A w} : Set V3) := by
      rw [← htriangle]
      constructor
      · rintro ⟨x, hx, heq⟩
        exact ⟨x, hx, by change B (g x) = T z; rw [heq, B.right_inv hTx]⟩
      · rintro ⟨x, hx, heq⟩
        exact ⟨x, hx, by rw [← heq]; exact (B.left_inv (hmap' hx)).symm⟩
    exact heq.trans (by simpa only [T.symm_apply_apply] using htri (T z) hz.1)
  · intro z hz
    exact hedgeT z hz.1
  · intro z hz
    rw [← hedgeT z hz.1, triangle_intrinsicFrontier_eq_edges K hpq hwp hwq ht,
      image_union, image_union]
    constructor
    · rintro (hxe | hxother | hxother)
      · exact hxe
      · exfalso
        apply hz.2
        apply Or.inr
        rw [← hother_image q (Or.inr rfl)]
        obtain ⟨x, hx, heq⟩ := hxother
        exact ⟨x, hx, by change B (g x) = T z; rw [heq, B.right_inv (hnewV hz)]⟩
      · exfalso
        apply hz.2
        apply Or.inl
        rw [← hother_image p (Or.inl rfl)]
        obtain ⟨x, hx, heq⟩ := hxother
        exact ⟨x, hx, by change B (g x) = T z; rw [heq, B.right_inv (hnewV hz)]⟩
    · exact Or.inl



theorem HasOriginalEdgeCofaceCharts.exists_triangle_endpoint_crossing
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {p q w : E}
    (h : HasOriginalEdgeCofaceCharts e S K g {p, q})
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    (hpq : p ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (ht : ({w, p, q} : Finset E) ∈ K.faces)
    {y : X} (hy : y ∈ S ∩ (g '' segment ℝ p q)) :
    ∃ (B : OpenPartialHomeomorph X V3) (V : Set V3) (T : C3 ≃ᴬ[ℝ] V3),
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      y ∈ B.source ∧ IsOpen V ∧ B y ∈ V ∧ V ⊆ B.target ∧ T 0 = B y ∧
      (∀ z, T z ∈ V → (B.symm (T z) ∈ S ↔ z.2 = 0)) ∧
      (∀ z, T z ∈ V →
        (B.symm (T z) ∈ g '' convexHull ℝ ({w, p, q} : Set E) ↔
          z.1.1 = 0 ∧ 0 ≤ z.1.2)) ∧
      (∀ z, T z ∈ V → (B.symm (T z) ∈ g '' segment ℝ p q ↔ z.1 = 0)) ∧
      (∀ z, T z ∈ V →
        (B.symm (T z) ∈ g '' intrinsicFrontier ℝ (convexHull ℝ ({w, p, q} : Set E)) ↔
          z.1 = 0)) :=
  h.exists_triangle_endpoint_crossing_of_not_vertex hgi
    (fun hyv => disjoint_left.mp hSV hy.1 hyv) hpq hwp hwq ht hy

end PoincareConjecture.M76
