import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.PolygonalDomains

set_option autoImplicit false
open Set

namespace Poincare.Topology.Plane.Meshes

noncomputable def cornerSeparator (b : AffineBasis (Fin 3) ℝ Plane) : Plane →ᵃ[ℝ] ℝ :=
  b.coord 1 - b.coord 2

@[simp] theorem cornerSeparator_zero (b : AffineBasis (Fin 3) ℝ Plane) :
    cornerSeparator b (b 0) = 0 := by simp [cornerSeparator]

@[simp] theorem cornerSeparator_one (b : AffineBasis (Fin 3) ℝ Plane) :
    cornerSeparator b (b 1) = 1 := by simp [cornerSeparator]

@[simp] theorem cornerSeparator_two (b : AffineBasis (Fin 3) ℝ Plane) :
    cornerSeparator b (b 2) = -1 := by simp [cornerSeparator]

theorem cornerSeparator_surjective (b : AffineBasis (Fin 3) ℝ Plane) :
    Function.Surjective (cornerSeparator b) := by
  intro t
  exact ⟨AffineMap.lineMap (b 0) (b 1) t, by
    rw [AffineMap.apply_lineMap, cornerSeparator_zero, cornerSeparator_one]
    simp [AffineMap.lineMap_apply_ring]⟩

theorem inter_corner_eq_one_side
    (b : AffineBasis (Fin 3) ℝ Plane) {K : Set Plane}
    (hside : (∀ z ∈ K, 0 ≤ cornerSeparator b z) ∨
      (∀ z ∈ K, cornerSeparator b z ≤ 0)) :
    K ∩ (segment ℝ (b 0) (b 1) ∪ segment ℝ (b 0) (b 2)) =
        K ∩ segment ℝ (b 0) (b 1) ∨
      K ∩ (segment ℝ (b 0) (b 1) ∪ segment ℝ (b 0) (b 2)) =
        K ∩ segment ℝ (b 0) (b 2) := by
  rcases hside with hpos | hneg
  · left
    apply Subset.antisymm
    · rintro z ⟨hzK, hz | hz⟩
      · exact ⟨hzK, hz⟩
      · rw [segment_eq_image_lineMap] at hz
        obtain ⟨t, ht, rfl⟩ := hz
        have h := hpos _ hzK
        rw [AffineMap.apply_lineMap, cornerSeparator_zero, cornerSeparator_two,
          AffineMap.lineMap_apply_ring] at h
        have ht0 : t = 0 := by linarith [ht.1]
        simp only [ht0, AffineMap.lineMap_apply_zero] at hzK ⊢
        exact ⟨hzK, left_mem_segment _ _ _⟩
    · exact inter_subset_inter_right K subset_union_left
  · right
    apply Subset.antisymm
    · rintro z ⟨hzK, hz | hz⟩
      · rw [segment_eq_image_lineMap] at hz
        obtain ⟨t, ht, rfl⟩ := hz
        have h := hneg _ hzK
        rw [AffineMap.apply_lineMap, cornerSeparator_zero, cornerSeparator_one,
          AffineMap.lineMap_apply_ring] at h
        have ht0 : t = 0 := by linarith [ht.1]
        simp only [ht0, AffineMap.lineMap_apply_zero] at hzK ⊢
        exact ⟨hzK, left_mem_segment _ _ _⟩
      · exact ⟨hzK, hz⟩
    · exact inter_subset_inter_right K subset_union_right

theorem inter_segment_eq_empty_or_subsegment {K : Set Plane}
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) (p q : Plane) :
    K ∩ segment ℝ p q = ∅ ∨
      ∃ a b : ℝ, a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧ a ≤ b ∧
        K ∩ segment ℝ p q = AffineMap.lineMap p q '' Icc a b := by
  let A : Set ℝ := Icc (0 : ℝ) 1 ∩ (AffineMap.lineMap p q) ⁻¹' K
  have hAcompact : IsCompact A :=
    isCompact_Icc.inter_right (hclosed.preimage
      (AffineMap.lineMap p q : ℝ →ᵃ[ℝ] Plane).continuous_of_finiteDimensional)
  have hAconvex : Convex ℝ A :=
    (convex_Icc (0 : ℝ) 1).inter (hconvex.affine_preimage (AffineMap.lineMap p q))
  have himage : K ∩ segment ℝ p q = AffineMap.lineMap p q '' A := by
    dsimp only [A]
    rw [segment_eq_image_lineMap, image_inter_preimage, inter_comm]
  by_cases hA : A.Nonempty
  · right
    refine ⟨sInf A, sSup A, (hAcompact.sInf_mem hA).1, (hAcompact.sSup_mem hA).1,
      csInf_le_csSup hA hAcompact.bddBelow hAcompact.bddAbove, ?_⟩
    exact himage.trans (congrArg (fun B => AffineMap.lineMap p q '' B)
      (eq_Icc_of_connected_compact ⟨hA, hAconvex.isPreconnected⟩ hAcompact))
  · left
    rw [himage, Set.not_nonempty_iff_eq_empty.mp hA, image_empty]

theorem inter_piece_eq_empty_or_corner_subsegment
    (b : AffineBasis (Fin 3) ℝ Plane) {K A : Set Plane}
    (hclosed : IsClosed K) (hconvex : Convex ℝ K)
    (hside : (∀ z ∈ K, 0 ≤ cornerSeparator b z) ∨
      (∀ z ∈ K, cornerSeparator b z ≤ 0))
    (hsides : segment ℝ (b 0) (b 1) ∪ segment ℝ (b 0) (b 2) ⊆ A)
    (hcontact : K ∩ A ⊆ segment ℝ (b 0) (b 1) ∪ segment ℝ (b 0) (b 2)) :
    K ∩ A = ∅ ∨ ∃ (j : Fin 3) (a d : ℝ), (j = 1 ∨ j = 2) ∧
      a ∈ Icc (0 : ℝ) 1 ∧ d ∈ Icc (0 : ℝ) 1 ∧ a ≤ d ∧
      K ∩ A = AffineMap.lineMap (b 0) (b j) '' Icc a d := by
  have hreduce : K ∩ A = K ∩
      (segment ℝ (b 0) (b 1) ∪ segment ℝ (b 0) (b 2)) :=
    Subset.antisymm (fun _ hz => ⟨hz.1, hcontact hz⟩)
      (inter_subset_inter_right K hsides)
  rcases inter_corner_eq_one_side b hside with hleft | hright
  · rcases inter_segment_eq_empty_or_subsegment hclosed hconvex (b 0) (b 1) with
      hempty | ⟨a, d, ha, hd, had, heq⟩
    · exact Or.inl (hreduce.trans (hleft.trans hempty))
    · exact Or.inr ⟨1, a, d, Or.inl rfl, ha, hd, had, hreduce.trans (hleft.trans heq)⟩
  · rcases inter_segment_eq_empty_or_subsegment hclosed hconvex (b 0) (b 2) with
      hempty | ⟨a, d, ha, hd, had, heq⟩
    · exact Or.inl (hreduce.trans (hright.trans hempty))
    · exact Or.inr ⟨2, a, d, Or.inr rfl, ha, hd, had, hreduce.trans (hright.trans heq)⟩

namespace TriangleMesh

variable (T : TriangleMesh)

theorem IsMonochromatic.triangleCarrier_halfspace {l : Plane →ᵃ[ℝ] ℝ}
    (hmono : T.IsMonochromatic l) (t : T.Triangle) :
    (∀ z ∈ T.triangleCarrier t.1, 0 ≤ l z) ∨
      (∀ z ∈ T.triangleCarrier t.1, l z ≤ 0) := by
  rcases hmono t.1 t.2 with hpos | hneg
  · left
    apply convexHull_min
    · rintro _ ⟨v, hv, rfl⟩
      exact hpos v hv
    · exact (convex_Ici (0 : ℝ)).affine_preimage l
  · right
    apply convexHull_min
    · rintro _ ⟨v, hv, rfl⟩
      exact hneg v hv
    · exact (convex_Iic (0 : ℝ)).affine_preimage l

theorem IsMonochromatic.inter_corner_eq_one_side
    (b : AffineBasis (Fin 3) ℝ Plane)
    (hmono : T.IsMonochromatic (cornerSeparator b)) (t : T.Triangle) :
    T.triangleCarrier t.1 ∩ (segment ℝ (b 0) (b 1) ∪ segment ℝ (b 0) (b 2)) =
        T.triangleCarrier t.1 ∩ segment ℝ (b 0) (b 1) ∨
      T.triangleCarrier t.1 ∩ (segment ℝ (b 0) (b 1) ∪ segment ℝ (b 0) (b 2)) =
        T.triangleCarrier t.1 ∩ segment ℝ (b 0) (b 2) :=
  Meshes.inter_corner_eq_one_side b (hmono.triangleCarrier_halfspace T t)

theorem IsMonochromatic.inter_zero_subset_frontier {l : Plane →ᵃ[ℝ] ℝ}
    (hmono : T.IsMonochromatic l) (hsurj : Function.Surjective l) (t : T.Triangle) :
    T.triangleCarrier t.1 ∩ {z | l z = 0} ⊆ frontier (T.triangleCarrier t.1) := by
  intro z hz
  exact ⟨subset_closure hz.1, fun hi => disjoint_left.mp
    (hmono.interior_disjoint_zero T hsurj t) hi hz.2⟩

theorem exists_refinement_with_single_side_contacts
    {I : Type*} [Finite I] (b : I → AffineBasis (Fin 3) ℝ Plane) :
    ∃ S : TriangleMesh,
      S.toPlaneComplex.support = T.toPlaneComplex.support ∧
      S.toPlaneComplex.Subdivides T.toPlaneComplex ∧
      (∀ i, S.IsMonochromatic (cornerSeparator (b i))) ∧
      ∀ (t : S.Triangle) i,
        S.triangleCarrier t.1 ∩
            (segment ℝ (b i 0) (b i 1) ∪ segment ℝ (b i 0) (b i 2)) =
          S.triangleCarrier t.1 ∩ segment ℝ (b i 0) (b i 1) ∨
        S.triangleCarrier t.1 ∩
            (segment ℝ (b i 0) (b i 1) ∪ segment ℝ (b i 0) (b i 2)) =
          S.triangleCarrier t.1 ∩ segment ℝ (b i 0) (b i 2) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let lines := (Finset.univ : Finset I).toList.map (fun i => cornerSeparator (b i))
  let S := T.refineByLines lines
  have hmono (i : I) : S.IsMonochromatic (cornerSeparator (b i)) :=
    T.refineByLines_isMonochromatic_of_mem lines (by simp [lines])
  exact ⟨S, T.refineByLines_support lines, T.refineByLines_subdivides lines, hmono,
    fun t i => (hmono i).inter_corner_eq_one_side S (b i) t⟩

theorem exists_refinement_with_corner_contact_subsegments
    {I : Type*} [Finite I] (b : I → AffineBasis (Fin 3) ℝ Plane) (A : I → Set Plane)
    (hsides : ∀ i, segment ℝ (b i 0) (b i 1) ∪ segment ℝ (b i 0) (b i 2) ⊆ A i)
    (hcontact : ∀ i, T.toPlaneComplex.support ∩ A i ⊆
      segment ℝ (b i 0) (b i 1) ∪ segment ℝ (b i 0) (b i 2)) :
    ∃ S : TriangleMesh,
      S.toPlaneComplex.support = T.toPlaneComplex.support ∧
      S.toPlaneComplex.Subdivides T.toPlaneComplex ∧
      ∀ (t : S.Triangle) i,
        (S.triangleCarrier t.1 ∩ A i ⊆ frontier (S.triangleCarrier t.1)) ∧
        (S.triangleCarrier t.1 ∩ A i = ∅ ∨
          ∃ (j : Fin 3) (a d : ℝ), (j = 1 ∨ j = 2) ∧
            a ∈ Icc (0 : ℝ) 1 ∧ d ∈ Icc (0 : ℝ) 1 ∧ a ≤ d ∧
            S.triangleCarrier t.1 ∩ A i =
              AffineMap.lineMap (b i 0) (b i j) '' Icc a d) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let cornerLines := (Finset.univ : Finset I).toList.map (fun i => cornerSeparator (b i))
  let sideLines := (Finset.univ : Finset (I × Fin 3)).toList.map
    (fun p => (b p.1).coord p.2)
  let lines := cornerLines ++ sideLines
  let S := T.refineByLines lines
  have hsupport : S.toPlaneComplex.support = T.toPlaneComplex.support :=
    T.refineByLines_support lines
  have hcorner (i : I) : S.IsMonochromatic (cornerSeparator (b i)) :=
    T.refineByLines_isMonochromatic_of_mem lines (by simp [lines, cornerLines])
  have hside (i : I) (k : Fin 3) : S.IsMonochromatic ((b i).coord k) :=
    T.refineByLines_isMonochromatic_of_mem lines (by
      apply List.mem_append_right
      apply List.mem_map.mpr
      exact ⟨(i, k), by simp, rfl⟩)
  refine ⟨S, hsupport, T.refineByLines_subdivides lines, ?_⟩
  intro t i
  have htsupport : S.triangleCarrier t.1 ⊆ T.toPlaneComplex.support := by
    rw [← hsupport, TriangleMesh.toPlaneComplex_support]
    exact subset_iUnion₂_of_subset t.1 t.2 Subset.rfl
  have htc : S.triangleCarrier t.1 ∩ A i ⊆
      segment ℝ (b i 0) (b i 1) ∪ segment ℝ (b i 0) (b i 2) :=
    fun _ hz => hcontact i ⟨htsupport hz.1, hz.2⟩
  constructor
  · intro z hz
    rcases htc hz with hleft | hright
    · apply (hside i 2).inter_zero_subset_frontier S ((b i).surjective_coord 2) t
      refine ⟨hz.1, ?_⟩
      rw [segment_eq_image_lineMap] at hleft
      obtain ⟨a, -, rfl⟩ := hleft
      simp [AffineMap.apply_lineMap]
    · apply (hside i 1).inter_zero_subset_frontier S ((b i).surjective_coord 1) t
      refine ⟨hz.1, ?_⟩
      rw [segment_eq_image_lineMap] at hright
      obtain ⟨a, -, rfl⟩ := hright
      simp [AffineMap.apply_lineMap]
  · exact inter_piece_eq_empty_or_corner_subsegment (b i)
      ((t.1.finite_toSet.image S.position).isClosed_convexHull ℝ)
      (convex_convexHull ℝ _) ((hcorner i).triangleCarrier_halfspace S t) (hsides i) htc

end TriangleMesh

theorem exists_triangleMesh_of_frontier_in_lines_with_monochromatic
    {U : Set Plane} (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (lines extra : List (Plane →ᵃ[ℝ] ℝ))
    (hsurj : ∀ l ∈ lines, Function.Surjective l)
    (hfrontier : frontier U ⊆ ⋃ l ∈ lines, {p : Plane | l p = 0}) :
    ∃ T : TriangleMesh, T.toPlaneComplex.support = closure U ∧
      ∀ l ∈ lines ++ extra, T.IsMonochromatic l := by
  obtain ⟨T, hT⟩ := exists_triangleMesh_of_frontier_in_finitely_many_lines
    hU hbounded lines hsurj hfrontier
  exact ⟨T.refineByLines (lines ++ extra),
    (T.refineByLines_support _).trans hT,
    fun _ hl => T.refineByLines_isMonochromatic_of_mem _ hl⟩

end Poincare.Topology.Plane.Meshes
