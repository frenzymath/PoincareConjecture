import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ProtectedCarrierRefinement
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ProtectedFiniteComplexPosition
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ProtectedMotionImage
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.AffineLevelComplexPosition
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineLevelComplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections
















set_option autoImplicit false

open Set Geometry unitInterval

namespace PoincareConjecture.M76.Dehn

private theorem exists_finite_nonzero_height_margin {E : Type*}
    (V : Set E) (hV : V.Finite) (height : E → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ V, height v ≠ 0 → δ ≤ |height v| := by
  induction V, hV using Set.Finite.induction_on with
  | empty => exact ⟨1, by norm_num, fun _ hv => hv.elim⟩
  | @insert a V _ha _hV ih =>
    obtain ⟨δ, hδ, hbound⟩ := ih
    by_cases hzero : height a = 0
    · refine ⟨δ, hδ, ?_⟩
      intro v hv hvzero
      rcases mem_insert_iff.mp hv with rfl | hv
      · exact (hvzero hzero).elim
      · exact hbound v hv hvzero
    · refine ⟨min δ |height a|, lt_min hδ (abs_pos.mpr hzero), ?_⟩
      intro v hv hvzero
      rcases mem_insert_iff.mp hv with rfl | hv
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbound v hv hvzero)

private theorem height_signs_of_small_displacement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ell : E →L[ℝ] ℝ) {δ ε : ℝ} (hδ : 0 < δ)
    (hε : (‖ell‖ + 1) * ε < δ / 2)
    {x y : E} (hxy : dist y x < ε) (hbound : δ ≤ |ell x|) :
    |ell y - ell x| < |ell x| / 2 ∧
      (0 < ell y ↔ 0 < ell x) ∧ (ell y < 0 ↔ ell x < 0) := by
  have hnorm := ell.dist_le_opNorm y x
  have hdist : |ell y - ell x| ≤ ‖ell‖ * dist y x := by
    simpa only [Real.dist_eq] using hnorm
  have hmul : ‖ell‖ * dist y x ≤ (‖ell‖ + 1) * dist y x :=
    mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
  have hsmall : |ell y - ell x| < δ / 2 :=
    (hdist.trans hmul).trans_lt
      ((mul_lt_mul_of_pos_left hxy (by positivity)).trans hε)
  have hhalf : |ell y - ell x| < |ell x| / 2 :=
    hsmall.trans_le (by linarith)
  have hxzero : ell x ≠ 0 := by
    intro hx
    rw [hx, abs_zero] at hbound
    linarith
  refine ⟨hhalf, ?_⟩
  have habs := abs_lt.mp hhalf
  rcases lt_or_gt_of_ne hxzero with hx | hx
  · rw [abs_of_neg hx] at habs
    have hy : ell y < 0 := by linarith
    exact ⟨iff_of_false (not_lt_of_ge hy.le) (not_lt_of_ge hx.le),
      iff_of_true hy hx⟩
  · rw [abs_of_pos hx] at habs
    have hy : 0 < ell y := by linarith
    exact ⟨iff_of_true hy hx,
      iff_of_false (not_lt_of_ge hy.le) (not_lt_of_ge hx.le)⟩

private theorem nonzero_of_plane_face_position
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ell : E →L[ℝ] ℝ) (hell : ell ≠ 0)
    (L : SimplicialComplex ℝ E) {f : E → E} {v : E}
    (hL : L.space ⊆ {x | ell x = 0})
    (hmem : ell (f v) = 0 → f v ∈ L.space)
    (hposition : ∀ t ∈ L.faces,
      affineSpan ℝ (f '' ({v} : Set E) ∪ (t : Set E)) = ⊤ ∨
        Disjoint (intrinsicInterior ℝ (convexHull ℝ (f '' ({v} : Set E))))
          (convexHull ℝ (t : Set E))) : ell (f v) ≠ 0 := by
  intro hzero
  obtain ⟨t, ht, hvt⟩ := SimplicialComplex.mem_space_iff.mp (hmem hzero)
  rcases hposition t ht with hspan | hdisjoint
  · let A : AffineSubspace ℝ E := ell.toLinearMap.ker.toAffineSubspace
    have hle : affineSpan ℝ (f '' ({v} : Set E) ∪ (t : Set E)) ≤ A := by
      apply affineSpan_le.mpr
      intro x hx
      change ell x = 0
      rcases hx with ⟨w, hw, rfl⟩ | hx
      · rw [mem_singleton_iff.mp hw]
        exact hzero
      · exact hL (L.subset_space ht hx)
    rw [hspan] at hle
    apply hell
    ext x
    exact hle (show x ∈ (⊤ : AffineSubspace ℝ E) from mem_univ x)
  · have hv : f v ∈ intrinsicInterior ℝ (convexHull ℝ (f '' ({v} : Set E))) := by
      simp only [image_singleton, convexHull_singleton, intrinsicInterior_singleton,
        mem_singleton_iff]
    exact Set.disjoint_left.mp hdisjoint hv hvt






theorem exists_protected_branch_repair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (J P P₀ : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hP : P.faces.Finite) (hP₀ : P₀.faces.Finite)
    (hcv : Convex ℝ J.space) (hP₀P : P₀.space ⊆ P.space)
    (hPJ : P.space ⊆ J.space)
    (hfront : P.space ∩ frontier J.space ⊆ P₀.space)
    (ell : E →L[ℝ] ℝ) (hell : ell ≠ 0) :
    ∃ R K K₀ L : SimplicialComplex ℝ E,
      R.faces.Finite ∧ R.IsSubdivision J ∧ K ≤ R ∧ K.space = P.space ∧
      K₀ ≤ K ∧ K₀.space = P₀.space ∧
      (∀ s ∈ K.faces, (∀ v ∈ s, v ∈ K₀.vertices) → s ∈ K₀.faces) ∧
      L.faces.Finite ∧ L.space = J.space ∩ {x | ell x = 0} ∧
      ∃ δ : ℝ, 0 < δ ∧
        (∀ v ∈ R.vertices, ell v ≠ 0 → δ ≤ |ell v|) ∧
        ∀ ε : ℝ, 0 < ε → ∃ H : PLCarrierMotion J.space P₀.space ε,
          R.AffineOnFaces (H.map 1) ∧
          (∀ v ∈ R.vertices, ell v ≠ 0 → ∀ t,
            |ell (H.map t v) - ell v| < |ell v| / 2 ∧
              (0 < ell (H.map t v) ↔ 0 < ell v) ∧
              (ell (H.map t v) < 0 ↔ ell v < 0)) ∧
          (∀ v ∈ K.vertices,
            ell (H.map 1 v) = 0 ↔ v ∈ K₀.vertices ∧ ell v = 0) ∧
          (∀ s ∈ K.faces, (∀ v ∈ s, ell (H.map 1 v) = 0) ↔
            s ∈ K₀.faces ∧ ∀ v ∈ s, ell v = 0) ∧
          (∃ A : SimplicialComplex ℝ E, A.faces.Finite ∧
            A.space = H.map 1 '' P.space ∧ K₀ ≤ A) ∧
          ∀ s ∈ K.faces, s ∉ K₀.faces → ∀ t ∈ L.faces,
            affineSpan ℝ (H.map 1 '' (s : Set E) ∪ (t : Set E)) = ⊤ ∨
              Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (s : Set E))))
                (convexHull ℝ (t : Set E)) := by
  classical
  obtain ⟨R, K, K₀, Q, hR, hRJ, hK, hKs, hK₀, hK₀s,
    hfull, hQ, hQs, hfree⟩ :=
    J.exists_protected_carrier_refinement P P₀ hJ hP hP₀ hcv hP₀P hPJ hfront
  obtain ⟨L, hL, hLs⟩ :=
    J.exists_finite_affineLevel_complex hJ ell.toLinearMap.toAffineMap 0
  obtain ⟨δ, hδ, hmargin⟩ :=
    exists_finite_nonzero_height_margin R.vertices
      (R.finite_vertices_of_finite_faces hR) ell
  refine ⟨R, K, K₀, L, hR, hRJ, hK, hKs, hK₀, hK₀s, hfull,
    hL, hLs, δ, hδ, hmargin, ?_⟩
  intro ε hε
  obtain ⟨η, hη, hηbound⟩ := exists_pos_mul_lt (half_pos hδ) (‖ell‖ + 1)
  let ζ := min ε η
  have hζ : 0 < ζ := lt_min hε hη
  have hζbound : (‖ell‖ + 1) * ζ < δ / 2 :=
    (mul_le_mul_of_nonneg_left (min_le_right ε η) (by positivity)).trans_lt hηbound
  have hRs : R.space = J.space := hRJ.space_eq
  have hRcv : Convex ℝ R.space := hRs.symm ▸ hcv
  have hRQfront : frontier R.space ⊆ Q.space := by
    rw [hRs, hQs]
    exact subset_union_right
  have hK₀Q : K₀.space ⊆ Q.space := by
    rw [hK₀s, hQs]
    exact subset_union_left
  obtain ⟨H, hHaff, hHfixed, hHfaces⟩ :=
    SimplicialComplex.exists_protected_finite_complex_position R Q K K₀ hR hRcv
      hQ hRQfront hK hfull hK₀Q hfree (fun _ : Unit => L) (fun _ => hL) hζ
  let F : PLCarrierMotion J.space P₀.space ε :=
    { map := H.map
      continuous_map := H.continuous_map
      continuous_symm := H.continuous_symm
      zero := H.zero
      outside := by simpa only [hRs] using H.outside
      fixed_protected := fun t x hx => hHfixed t x (hK₀s.symm ▸ hx)
      carrier := by simpa only [hRs] using H.carrier
      finitePL := by
        rw [← hRs]
        exact H.finitePL
      small := fun t x => (H.small t x).trans_le (min_le_left ε η) }
  have hsigns (v : E) (hv : v ∈ R.vertices) (hvzero : ell v ≠ 0) (t : I) :
      |ell (H.map t v) - ell v| < |ell v| / 2 ∧
        (0 < ell (H.map t v) ↔ 0 < ell v) ∧
        (ell (H.map t v) < 0 ↔ ell v < 0) :=
    height_signs_of_small_displacement ell hδ hζbound (H.small t v)
      (hmargin v hv hvzero)
  have havoid (v : E) (hv : v ∈ K.vertices) (hv₀ : v ∉ K₀.vertices) :
      ell (H.map 1 v) ≠ 0 := by
    apply nonzero_of_plane_face_position ell hell L
    · intro x hx
      exact (hLs.subset hx).2
    · intro hx
      apply hLs.symm.subset
      refine ⟨?_, hx⟩
      exact hRs.subset ((H.carrier 1).subset
        ⟨v, R.vertices_subset_space (hK hv), rfl⟩)
    · intro t ht
      simpa only [Finset.coe_singleton] using hHfaces () {v} hv hv₀ t ht
  have hzero (v : E) (hv : v ∈ K.vertices) :
      ell (H.map 1 v) = 0 ↔ v ∈ K₀.vertices ∧ ell v = 0 := by
    constructor
    · intro hz
      have hv₀ : v ∈ K₀.vertices := by
        by_contra hn
        exact havoid v hv hn hz
      refine ⟨hv₀, ?_⟩
      rwa [hHfixed 1 v (K₀.vertices_subset_space hv₀)] at hz
    · rintro ⟨hv₀, hz⟩
      rw [hHfixed 1 v (K₀.vertices_subset_space hv₀)]
      exact hz
  have hfacezero (s : Finset E) (hs : s ∈ K.faces) :
      (∀ v ∈ s, ell (H.map 1 v) = 0) ↔
        s ∈ K₀.faces ∧ ∀ v ∈ s, ell v = 0 := by
    have hvK (v : E) (hv : v ∈ s) : v ∈ K.vertices :=
      K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    constructor
    · intro hz
      exact ⟨hfull s hs (fun v hv => ((hzero v (hvK v hv)).mp (hz v hv)).1),
        fun v hv => ((hzero v (hvK v hv)).mp (hz v hv)).2⟩
    · rintro ⟨hs₀, hz⟩ v hv
      rw [hHfixed 1 v (K₀.subset_space hs₀ hv)]
      exact hz v hv
  have hKaff : K.AffineOnFaces (H.map 1) := fun s hs => hHaff s (hK hs)
  have hinj : InjOn (H.map 1) K.space := (H.map 1).injective.injOn
  refine ⟨F, hHaff, hsigns, hzero, hfacezero, ?_, hHfaces ()⟩
  refine ⟨hKaff.embeddedImage hinj, hKaff.embeddedImage_finite hinj (hR.subset hK),
    ?_, hKaff.protected_le_embeddedImage hinj hK₀ (fun x hx => hHfixed 1 x hx)⟩
  rw [hKaff.embeddedImage_space hinj, hKs]








theorem exists_protected_boundary_branch_repair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (J B P C : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hB : B.faces.Finite)
    (hP : P.faces.Finite) (hC : C.faces.Finite)
    (hcv : Convex ℝ J.space) (hPB : P.space ⊆ B.space)
    (hBJ : B.space ⊆ J.space) (hCJ : C.space ⊆ J.space)
    (height ell : E →L[ℝ] ℝ) (hlevel : P.space ⊆ {x | height x = 0})
    (htransverse : ∃ u : E, height u = 0 ∧ ell u ≠ 0) :
    ∃ R W K K₀ L : SimplicialComplex ℝ E,
      R.faces.Finite ∧ R.IsSubdivision J ∧ W ≤ R ∧ W.space = B.space ∧
      K ≤ W ∧ K.space = P.space ∧ K₀ ≤ K ∧
      K₀.space = P.space ∩ (C.space ∪ frontier J.space) ∧
      (∀ s ∈ K.faces, (∀ v ∈ s, v ∈ K₀.vertices) → s ∈ K₀.faces) ∧
      L.faces.Finite ∧ L.space = J.space ∩ {x | height x = 0 ∧ ell x = 0} ∧
      ∃ δ : ℝ, 0 < δ ∧
        (∀ v ∈ R.vertices, ell v ≠ 0 → δ ≤ |ell v|) ∧
        ∀ ε : ℝ, 0 < ε → ∃ H : PLCarrierMotion J.space C.space ε,
          R.AffineOnFaces (H.map 1) ∧
          (∀ t x, height (H.map t x) = height x) ∧
          (∀ v ∈ R.vertices, ell v ≠ 0 → ∀ t,
            |ell (H.map t v) - ell v| < |ell v| / 2 ∧
              (0 < ell (H.map t v) ↔ 0 < ell v) ∧
              (ell (H.map t v) < 0 ↔ ell v < 0)) ∧
          (∀ v ∈ K.vertices,
            ell (H.map 1 v) = 0 ↔ v ∈ K₀.vertices ∧ ell v = 0) ∧
          (∀ s ∈ K.faces, (∀ v ∈ s, ell (H.map 1 v) = 0) ↔
            s ∈ K₀.faces ∧ ∀ v ∈ s, ell v = 0) ∧
          (∀ s ∈ W.faces, (∀ v ∈ s, ell (H.map 1 v) = 0) →
            ∀ v ∈ s, ell v = 0) ∧
          (∃ W' K' : SimplicialComplex ℝ E,
            W'.faces.Finite ∧ K'.faces.Finite ∧
            W'.space = H.map 1 '' B.space ∧ K'.space = H.map 1 '' P.space ∧
            K' ≤ W' ∧ K₀ ≤ K') ∧
          ∀ s ∈ K.faces, s ∉ K₀.faces → ∀ t ∈ L.faces,
            affineSpan ℝ (H.map 1 '' (s : Set E) ∪ (t : Set E)) =
                height.toLinearMap.ker.toAffineSubspace ∨
              Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (s : Set E))))
                (convexHull ℝ (t : Set E)) := by
  classical
  obtain ⟨D, hD, hDs⟩ := J.exists_finite_convex_frontier_triangulation hJ hcv
  obtain ⟨Q₀, hQ₀, hQ₀s⟩ := C.exists_finite_triangulation_union D hC hD
  have hQ₀J : Q₀.space ⊆ J.space := by
    rw [hQ₀s, hDs]
    exact union_subset hCJ (J.isCompact_space_of_finite hJ).isClosed.frontier_subset
  obtain ⟨P₀, hP₀, hP₀s⟩ := P.exists_finite_triangulation_inter Q₀ hP hQ₀
  let M : Bool × Bool → SimplicialComplex ℝ E
    | (false, false) => B
    | (false, true) => P
    | (true, false) => P₀
    | (true, true) => Q₀
  have hM : ∀ i, (M i).faces.Finite := by
    rintro ⟨a, b⟩
    cases a <;> cases b <;> assumption
  have hMJ : ∀ i, (M i).space ⊆ J.space := by
    rintro ⟨a, b⟩
    cases a <;> cases b
    · exact hBJ
    · exact hPB.trans hBJ
    · exact fun x hx => hBJ (hPB (hP₀s.subset hx).1)
    · exact hQ₀J
  obtain ⟨R, T, hR, hRJ, hT⟩ :=
    J.exists_subdivision_with_finite_full_polyhedra hJ M hM hMJ
  let W := T (false, false)
  let K := T (false, true)
  let K₀ := T (true, false)
  let Q := T (true, true)
  have hW : W ≤ R := (hT (false, false)).1
  have hK : K ≤ R := (hT (false, true)).1
  have hK₀R : K₀ ≤ R := (hT (true, false)).1
  have hQ : Q ≤ R := (hT (true, true)).1
  have hWs : W.space = B.space := (hT (false, false)).2.1
  have hKs : K.space = P.space := (hT (false, true)).2.1
  have hQs : Q.space = C.space ∪ frontier J.space := by
    rw [(hT (true, true)).2.1, hQ₀s, hDs]
  have hK₀s : K₀.space = P.space ∩ (C.space ∪ frontier J.space) := by
    rw [(hT (true, false)).2.1, hP₀s, hQ₀s, hDs]
  have hKW : K ≤ W := by
    intro s hs
    apply (hT (false, false)).2.2 s (hK hs)
    intro v hv
    apply SimplicialComplex.mem_subcomplex_vertices_of_mem_space hW
    · exact R.down_closed (hK hs) (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)
    · exact hWs.symm.subset (hPB (hKs.subset (K.subset_space hs hv)))
  have hK₀ : K₀ ≤ K := by
    intro s hs
    apply (hT (false, true)).2.2 s (hK₀R hs)
    intro v hv
    apply SimplicialComplex.mem_subcomplex_vertices_of_mem_space hK
    · exact R.down_closed (hK₀R hs) (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)
    · exact hKs.symm.subset (hK₀s.subset (K₀.subset_space hs hv)).1
  have hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ K₀.vertices) → s ∈ K₀.faces :=
    fun s hs => (hT (true, false)).2.2 s (hK hs)
  have hfree : ∀ v ∈ K.vertices, v ∉ K₀.vertices → v ∉ Q.vertices := by
    intro v hv hv₀ hvQ
    apply hv₀
    apply SimplicialComplex.mem_subcomplex_vertices_of_mem_space hK₀R (hK hv)
    exact hK₀s.symm.subset
      ⟨hKs.subset (K.vertices_subset_space hv), hQs.subset (Q.vertices_subset_space hvQ)⟩
  obtain ⟨V, hV, hVs⟩ :=
    J.exists_finite_affineLevel_complex hJ height.toLinearMap.toAffineMap 0
  obtain ⟨L, hL, hLs'⟩ :=
    V.exists_finite_affineLevel_complex hV ell.toLinearMap.toAffineMap 0
  have hLs : L.space = J.space ∩ {x | height x = 0 ∧ ell x = 0} := by
    rw [hLs', hVs]
    ext x
    change ((x ∈ J.space ∧ height x = 0) ∧ ell x = 0) ↔
      (x ∈ J.space ∧ height x = 0 ∧ ell x = 0)
    exact and_assoc
  let A : AffineSubspace ℝ E := height.toLinearMap.ker.toAffineSubspace
  have hKA : K.space ⊆ A := fun x hx => hlevel (hKs.subset hx)
  have hLA : L.space ⊆ A := fun x hx => (hLs.subset hx).2.1
  obtain ⟨δ, hδ, hmargin⟩ :=
    exists_finite_nonzero_height_margin R.vertices
      (R.finite_vertices_of_finite_faces hR) ell
  refine ⟨R, W, K, K₀, L, hR, hRJ, hW, hWs, hKW, hKs, hK₀, hK₀s, hfull,
    hL, hLs, δ, hδ, hmargin, ?_⟩
  intro ε hε
  obtain ⟨η, hη, hηbound⟩ := exists_pos_mul_lt (half_pos hδ) (‖ell‖ + 1)
  let ζ := min ε η
  have hζ : 0 < ζ := lt_min hε hη
  have hζbound : (‖ell‖ + 1) * ζ < δ / 2 :=
    (mul_le_mul_of_nonneg_left (min_le_right ε η) (by positivity)).trans_lt hηbound
  have hRs : R.space = J.space := hRJ.space_eq
  have hRcv : Convex ℝ R.space := hRs.symm ▸ hcv
  have hRQfront : frontier R.space ⊆ Q.space := by
    rw [hRs, hQs]
    exact subset_union_right
  have hK₀Q : K₀.space ⊆ Q.space := by
    rw [hK₀s, hQs]
    exact inter_subset_right
  obtain ⟨H, hHaff, hHfixed, hHdir, hHfaces⟩ :=
    SimplicialComplex.exists_protected_affine_level_complex_position R Q K K₀ hR hRcv
      hQ hRQfront hK hfull hK₀Q hfree A hKA (fun _ : Unit => L) (fun _ => hL)
      (fun _ => hLA) hζ
  let F : PLCarrierMotion J.space C.space ε :=
    { map := H.map
      continuous_map := H.continuous_map
      continuous_symm := H.continuous_symm
      zero := H.zero
      outside := by simpa only [hRs] using H.outside
      fixed_protected := fun t x hx => H.fixed_protected t x (hQs.symm.subset (Or.inl hx))
      carrier := by simpa only [hRs] using H.carrier
      finitePL := by
        rw [← hRs]
        exact H.finitePL
      small := fun t x => (H.small t x).trans_le (min_le_left ε η) }
  have hheight (t : I) (x : E) : height (H.map t x) = height x := by
    have hd : H.map t x - x ∈ height.toLinearMap.ker := by
      simpa only [A, Submodule.toAffineSubspace_direction] using hHdir t x
    have hz : height (H.map t x - x) = 0 := hd
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz
  have hsigns (v : E) (hv : v ∈ R.vertices) (hvzero : ell v ≠ 0) (t : I) :
      |ell (H.map t v) - ell v| < |ell v| / 2 ∧
        (0 < ell (H.map t v) ↔ 0 < ell v) ∧
        (ell (H.map t v) < 0 ↔ ell v < 0) :=
    height_signs_of_small_displacement ell hδ hζbound (H.small t v)
      (hmargin v hv hvzero)
  have havoid (v : E) (hv : v ∈ K.vertices) (hv₀ : v ∉ K₀.vertices) :
      ell (H.map 1 v) ≠ 0 := by
    intro hz
    have hvL : H.map 1 v ∈ L.space :=
      hLs.symm.subset ⟨hRs.subset ((H.carrier 1).subset
        ⟨v, R.vertices_subset_space (hK hv), rfl⟩),
        (hheight 1 v).trans (hlevel (hKs.subset (K.vertices_subset_space hv))), hz⟩
    obtain ⟨s, hs, hvs⟩ := SimplicialComplex.mem_space_iff.mp hvL
    have hposition := hHfaces () {v} hv hv₀ s hs
    simp only [Finset.coe_singleton] at hposition
    rcases hposition with hspan | hdisjoint
    · have hle : affineSpan ℝ (H.map 1 '' ({v} : Set E) ∪ (s : Set E)) ≤
          ell.toLinearMap.ker.toAffineSubspace := by
        apply affineSpan_le.mpr
        intro x hx
        change ell x = 0
        rcases hx with ⟨w, hw, rfl⟩ | hx
        · rw [mem_singleton_iff.mp hw]
          exact hz
        · exact (hLs.subset (L.subset_space hs hx)).2.2
      rw [hspan] at hle
      obtain ⟨u, hu, hellu⟩ := htransverse
      exact hellu (hle (show u ∈ A from hu))
    · have hv' : H.map 1 v ∈ intrinsicInterior ℝ
          (convexHull ℝ (H.map 1 '' ({v} : Set E))) := by
        simp only [image_singleton, convexHull_singleton, intrinsicInterior_singleton,
          mem_singleton_iff]
      exact Set.disjoint_left.mp hdisjoint hv' hvs
  have hzero (v : E) (hv : v ∈ K.vertices) :
      ell (H.map 1 v) = 0 ↔ v ∈ K₀.vertices ∧ ell v = 0 := by
    constructor
    · intro hz
      have hv₀ : v ∈ K₀.vertices := by
        by_contra hn
        exact havoid v hv hn hz
      refine ⟨hv₀, ?_⟩
      rwa [hHfixed 1 v (K₀.vertices_subset_space hv₀)] at hz
    · rintro ⟨hv₀, hz⟩
      rw [hHfixed 1 v (K₀.vertices_subset_space hv₀)]
      exact hz
  have hfacezero (s : Finset E) (hs : s ∈ K.faces) :
      (∀ v ∈ s, ell (H.map 1 v) = 0) ↔
        s ∈ K₀.faces ∧ ∀ v ∈ s, ell v = 0 := by
    have hvK (v : E) (hv : v ∈ s) : v ∈ K.vertices :=
      K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    constructor
    · intro hz
      exact ⟨hfull s hs (fun v hv => ((hzero v (hvK v hv)).mp (hz v hv)).1),
        fun v hv => ((hzero v (hvK v hv)).mp (hz v hv)).2⟩
    · rintro ⟨hs₀, hz⟩ v hv
      rw [hHfixed 1 v (K₀.subset_space hs₀ hv)]
      exact hz v hv
  have hwhole (s : Finset E) (hs : s ∈ W.faces)
      (hz : ∀ v ∈ s, ell (H.map 1 v) = 0) : ∀ v ∈ s, ell v = 0 := by
    intro v hv
    by_contra hn
    have hvR : v ∈ R.vertices := R.down_closed (hW hs)
      (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have hsmall := (hsigns v hvR hn 1).1
    rw [hz v hv, zero_sub, abs_neg] at hsmall
    have hnonneg := abs_nonneg (ell v)
    linarith
  have hWaff : W.AffineOnFaces (H.map 1) := fun s hs => hHaff s (hW hs)
  have hKaff : K.AffineOnFaces (H.map 1) := fun s hs => hHaff s (hK hs)
  have hinjW : InjOn (H.map 1) W.space := (H.map 1).injective.injOn
  have hinjK : InjOn (H.map 1) K.space := (H.map 1).injective.injOn
  have himage_le : hKaff.embeddedImage hinjK ≤ hWaff.embeddedImage hinjW := by
    intro s hs
    change s ∈ (hKaff.embeddedImage hinjK).faces at hs
    change s ∈ (hWaff.embeddedImage hinjW).faces
    rw [hKaff.embeddedImage_faces hinjK] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [hWaff.embeddedImage_faces hinjW]
    exact ⟨t, hKW ht, rfl⟩
  refine ⟨F, hHaff, hheight, hsigns, hzero, hfacezero, hwhole, ?_, hHfaces ()⟩
  refine ⟨hWaff.embeddedImage hinjW, hKaff.embeddedImage hinjK,
    hWaff.embeddedImage_finite hinjW (hR.subset hW),
    hKaff.embeddedImage_finite hinjK (hR.subset hK), ?_, ?_, himage_le,
    hKaff.protected_le_embeddedImage hinjK hK₀ (fun x hx => hHfixed 1 x hx)⟩
  · rw [hWaff.embeddedImage_space hinjW, hWs]
  · rw [hKaff.embeddedImage_space hinjK, hKs]

end PoincareConjecture.M76.Dehn
