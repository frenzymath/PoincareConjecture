import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.GraphCoordinates

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.CollarMesh
local notation "E" => ((ℝ × ℝ) × ℝ)

theorem finitePL_normalBaseMargin_comp
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    {S : Set D} {f : D → E} (hf : FinitePiecewiseAffineOn f S) (r : ℝ) :
    FinitePiecewiseAffineOn (fun p => normalMargin r ((f p).1, 0)) S := by
  let x := ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)).toContinuousAffineMap
  let y := ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)).toContinuousAffineMap
  have hx := hf.postcomp x
  have hy := hf.postcomp y
  have hnx := hf.postcomp (-x)
  have hny := hf.postcomp (-y)
  have hn : FinitePiecewiseAffineOn (fun p => ‖(f p).1‖) S := by
    apply ((hx.max hnx).max (hy.max hny)).congr
    intro p _
    change max (max (f p).1.1 (-(f p).1.1))
      (max (f p).1.2 (-(f p).1.2)) = ‖(f p).1‖
    simp only [Prod.norm_def, Real.norm_eq_abs, abs_eq_max_neg]
  have hr := hf.postcomp (ContinuousAffineMap.const ℝ E r)
  apply (hr.sub hn).positivePart.congr
  intro p _
  have hp : ‖((f p).1, (0 : ℝ))‖ = ‖(f p).1‖ := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg (f p).1)]
  change max 0 (r - ‖(f p).1‖) = max 0 (r - ‖((f p).1, (0 : ℝ))‖)
  rw [hp]

theorem exists_normal_graph_source_subdivision
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (K : SimplicialComplex ℝ D) (hK : K.faces.Finite)
    {f : D → E} (hf : FinitePiecewiseAffineOn f K.space) (r : ℝ) :
    ∃ J : SimplicialComplex ℝ D, J.faces.Finite ∧ J.IsSubdivision K ∧
      J.AffineOnFaces f ∧
      J.AffineOnFaces (fun p => normalMargin r ((f p).1, 0)) ∧
      ∀ c : ℝ, J.AffineOnFaces ((normalGraphCoordinates r c) ∘ f) := by
  obtain ⟨M, hM, hMs, hMf⟩ := hf.prod_mk (finitePL_normalBaseMargin_comp hf r)
  obtain ⟨J, hJ, hJK, hJM⟩ := K.exists_common_finite_subdivision M hK hM hMs.symm
  have hpair := hJM.affineOnFaces hMf
  have hJf := hpair.postcomp (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
  have hJm := hpair.postcomp (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap
  refine ⟨J, hJ, hJK, hJf, hJm, ?_⟩
  intro c s hs
  obtain ⟨A, hA⟩ := hJf s hs
  obtain ⟨B, hB⟩ := hJm s hs
  let fst := (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap.comp A
  let snd := (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap.comp A
  refine ⟨fst.prod (snd - c • B), ?_⟩
  intro p hp
  have hAp : f p = A p := hA hp
  have hBp : normalMargin r ((f p).1, 0) = B p := hB hp
  change ((f p).1, (f p).2 - c * normalMargin r ((f p).1, 0)) =
    ((A p).1, (A p).2 - c * B p)
  rw [hBp, hAp]

theorem exists_normal_motion_with_affine_source_cofaces
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (K : SimplicialComplex ℝ D) (hK : K.faces.Finite)
    {f : D → E} (hf : FinitePiecewiseAffineOn f K.space) (r : ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (J : SimplicialComplex ℝ D) (c : ℝ) (H : E ≃ₜ E),
      J.faces.Finite ∧ J.IsSubdivision K ∧ c ∈ Ioo (0 : ℝ) epsilon ∧
      H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E ∧
      (∀ p, H p = (p.1, p.2 + c * normalMargin r p)) ∧
      EqOn H id (Metric.closedBall (0 : E) r)ᶜ ∧
      (∀ p, (H p).1 = p.1) ∧ (∀ p, (H.symm p).1 = p.1) ∧
      J.AffineOnFaces f ∧
      J.AffineOnFaces (fun p => normalMargin r ((f p).1, 0)) ∧
      J.AffineOnFaces ((normalGraphCoordinates r c) ∘ f) ∧
      Disjoint (H '' {p : E | p.2 = 0})
        (f '' J.vertices ∩ {p : E | ‖p.1‖ < r}) := by
  obtain ⟨J, hJ, hJK, hJf, hm, hflat⟩ := exists_normal_graph_source_subdivision K hK hf r
  let rho : D → ℝ := fun p => -normalMargin r ((f p).1, 0)
  have hV := (J.finite_vertices_of_finite_faces hJ).subset
    (inter_subset_left : J.vertices ∩ {p | rho p ≠ 0} ⊆ J.vertices)
  obtain ⟨c, hc, havoid⟩ := hV.exists_pos_height_perturbation_parameter
    (fun p => (f p).2) rho (fun p hp hpzero => (hp.2 hpzero).elim)
    (lt_min hepsilon zero_lt_one)
  have hc1 : |c| < 1 := by rw [abs_of_pos hc.1]; exact hc.2.trans_le (min_le_right _ _)
  obtain ⟨H, hPL, hval, hoff, hfst, hinv⟩ := exists_normal_motion r c hc1
  refine ⟨J, c, H, hJ, hJK, ⟨hc.1, hc.2.trans_le (min_le_left _ _)⟩,
    hPL, hval, hoff, hfst, hinv, hJf, hm, hflat c, disjoint_left.mpr ?_⟩
  rintro p hp ⟨⟨v, hv, rfl⟩, hpr⟩
  have hrho : rho v ≠ 0 := by
    change -normalMargin r ((f v).1, 0) ≠ 0
    apply neg_ne_zero.mpr (ne_of_gt ?_)
    have hnorm : ‖((f v).1, (0 : ℝ))‖ = ‖(f v).1‖ := by
      rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg (f v).1)]
    unfold normalMargin
    rw [hnorm]
    exact lt_max_of_lt_right (sub_pos.mpr hpr)
  apply havoid v ⟨hv, hrho⟩
  rw [normal_motion_plane_image hval] at hp
  change (f v).2 = c * normalMargin r ((f v).1, 0) at hp
  change (f v).2 + c * (-normalMargin r ((f v).1, 0)) = 0
  rw [hp]
  ring

theorem exists_normal_graph_source_refinement_family
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (K : SimplicialComplex ℝ D) (hK : K.faces.Finite)
    {f : D → E} (hf : FinitePiecewiseAffineOn f K.space) (r : ℝ) :
    ∃ J : SimplicialComplex ℝ D, J.faces.Finite ∧ J.IsSubdivision K ∧
      ∀ (N : SimplicialComplex ℝ D), N.faces.Finite → N.IsSubdivision J →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∃ (c : ℝ) (H : E ≃ₜ E), c ∈ Ioo (0 : ℝ) epsilon ∧
        H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E ∧
        (∀ p, H p = (p.1, p.2 + c * normalMargin r p)) ∧
        EqOn H id (Metric.closedBall (0 : E) r)ᶜ ∧
        (∀ p, (H p).1 = p.1) ∧ (∀ p, (H.symm p).1 = p.1) ∧
        N.AffineOnFaces ((normalGraphCoordinates r c) ∘ f) ∧
        Disjoint (H '' {p : E | p.2 = 0})
          (f '' N.vertices ∩ {p : E | ‖p.1‖ < r}) := by
  obtain ⟨J, hJ, hJK, _, _, hflat⟩ := exists_normal_graph_source_subdivision K hK hf r
  refine ⟨J, hJ, hJK, ?_⟩
  intro N hN hNJ epsilon hepsilon
  let rho : D → ℝ := fun p => -normalMargin r ((f p).1, 0)
  have hV := (N.finite_vertices_of_finite_faces hN).subset
    (inter_subset_left : N.vertices ∩ {p | rho p ≠ 0} ⊆ N.vertices)
  obtain ⟨c, hc, havoid⟩ := hV.exists_pos_height_perturbation_parameter
    (fun p => (f p).2) rho (fun p hp hpzero => (hp.2 hpzero).elim)
    (lt_min hepsilon zero_lt_one)
  have hc1 : |c| < 1 := by rw [abs_of_pos hc.1]; exact hc.2.trans_le (min_le_right _ _)
  obtain ⟨H, hPL, hval, hoff, hfst, hinv⟩ := exists_normal_motion r c hc1
  refine ⟨c, H, ⟨hc.1, hc.2.trans_le (min_le_left _ _)⟩,
    hPL, hval, hoff, hfst, hinv, hNJ.affineOnFaces (hflat c), disjoint_left.mpr ?_⟩
  rintro p hp ⟨⟨v, hv, rfl⟩, hpr⟩
  have hrho : rho v ≠ 0 := by
    change -normalMargin r ((f v).1, 0) ≠ 0
    apply neg_ne_zero.mpr (ne_of_gt ?_)
    have hnorm : ‖((f v).1, (0 : ℝ))‖ = ‖(f v).1‖ := by
      rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg (f v).1)]
    unfold normalMargin
    rw [hnorm]
    exact lt_max_of_lt_right (sub_pos.mpr hpr)
  apply havoid v ⟨hv, hrho⟩
  rw [normal_motion_plane_image hval] at hp
  change (f v).2 = c * normalMargin r ((f v).1, 0) at hp
  change (f v).2 + c * (-normalMargin r ((f v).1, 0)) = 0
  rw [hp]
  ring

end PoincareConjecture.M76.CollarMesh
