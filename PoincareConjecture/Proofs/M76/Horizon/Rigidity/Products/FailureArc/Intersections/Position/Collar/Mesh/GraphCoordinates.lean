import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.EdgeMotion



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.CollarMesh
local notation "E" => ((ℝ × ℝ) × ℝ)

noncomputable def normalGraphCoordinates (r c : ℝ) : E ≃ₜ E where
  toFun p := (p.1, p.2 - c * normalMargin r (p.1, 0))
  invFun p := (p.1, p.2 + c * normalMargin r (p.1, 0))
  left_inv := by intro p; ext <;> simp
  right_inv := by intro p; ext <;> simp
  continuous_toFun := by
    exact continuous_fst.prodMk
      (continuous_snd.sub (continuous_const.mul
        ((lipschitzWith_normalMargin r).continuous.comp
          (continuous_fst.prodMk continuous_const))))
  continuous_invFun := by
    exact continuous_fst.prodMk
      (continuous_snd.add (continuous_const.mul
        ((lipschitzWith_normalMargin r).continuous.comp
          (continuous_fst.prodMk continuous_const))))

theorem normalGraphCoordinates_PL (r c : ℝ) :
    (normalGraphCoordinates r c).toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E := by
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  intro p _
  obtain ⟨K, hK, hpK, _⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed
      isCompact_singleton isOpen_univ (singleton_subset_iff.mpr (mem_univ p))
  have hm := finitePiecewiseAffineOn_normalBaseMargin r K hK
  have hcPL := hm.postcomp (c • ContinuousAffineMap.id ℝ ℝ)
  have hf := (K.affineOnFaces_affine
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  have hs := (K.affineOnFaces_affine
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  obtain ⟨J, hJ, hJK, hPL⟩ := hf.prod_mk (hs.sub hcPL)
  refine ⟨J, hJ, ?_, fun _ _ => mem_univ _, hPL⟩
  rw [hJK]
  exact hpK (mem_singleton p)

theorem normalGraphCoordinates_first (r c : ℝ) (p : E) :
    (normalGraphCoordinates r c p).1 = p.1 := rfl

theorem normalGraphCoordinates_surface {H : E ≃ₜ E} {r c : ℝ}
    (hval : ∀ p, H p = (p.1, p.2 + c * normalMargin r p)) (p : E) :
    p ∈ H '' {q : E | q.2 = 0} ↔ (normalGraphCoordinates r c p).2 = 0 := by
  rw [normal_motion_plane_image hval]
  change p.2 = c * normalMargin r (p.1, 0) ↔ p.2 - c * normalMargin r (p.1, 0) = 0
  exact sub_eq_zero.symm



theorem exists_normal_graph_affine_subdivision
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (r : ℝ) :
    ∃ J : SimplicialComplex ℝ E, J.faces.Finite ∧ J.IsSubdivision K ∧
      J.AffineOnFaces (fun p : E => normalMargin r (p.1, 0)) ∧
      ∀ c : ℝ, J.AffineOnFaces (normalGraphCoordinates r c : E → E) := by
  obtain ⟨M, hM, hMs, hMf⟩ := finitePiecewiseAffineOn_normalBaseMargin r K hK
  obtain ⟨J, hJ, hJK, hJM⟩ := K.exists_common_finite_subdivision M hK hM hMs.symm
  have hJf := hJM.affineOnFaces hMf
  refine ⟨J, hJ, hJK, hJf, ?_⟩
  intro c s hs
  obtain ⟨A, hA⟩ := hJf s hs
  let fst := (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap
  let snd := (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap
  refine ⟨fst.prod (snd - c • A), ?_⟩
  intro p hp
  change (p.1, p.2 - c * normalMargin r (p.1, 0)) = (p.1, p.2 - c * A p)
  have hAp : normalMargin r (p.1, 0) = A p := hA hp
  rw [hAp]




theorem exists_normal_motion_with_affine_cofaces
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (r : ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (J : SimplicialComplex ℝ E) (c : ℝ) (H : E ≃ₜ E),
      J.faces.Finite ∧ J.IsSubdivision K ∧ c ∈ Ioo (0 : ℝ) epsilon ∧
      H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E ∧
      (∀ p, H p = (p.1, p.2 + c * normalMargin r p)) ∧
      EqOn H id (Metric.closedBall (0 : E) r)ᶜ ∧
      (∀ p, (H p).1 = p.1) ∧ (∀ p, (H.symm p).1 = p.1) ∧
      J.AffineOnFaces (fun p : E => normalMargin r (p.1, 0)) ∧
      J.AffineOnFaces (normalGraphCoordinates r c : E → E) ∧
      Disjoint (H '' {p : E | p.2 = 0})
        (J.vertices ∩ {p : E | ‖p.1‖ < r}) := by
  obtain ⟨J, hJ, hJK, hm, hflat⟩ := exists_normal_graph_affine_subdivision K hK r
  let rho : E → ℝ := fun p => -normalMargin r (p.1, 0)
  have hV := (J.finite_vertices_of_finite_faces hJ).subset
    (inter_subset_left : J.vertices ∩ {p | rho p ≠ 0} ⊆ J.vertices)
  obtain ⟨c, hc, havoid⟩ := hV.exists_pos_height_perturbation_parameter
    (fun p : E => p.2) rho (fun p hp hpzero => (hp.2 hpzero).elim)
    (lt_min hepsilon zero_lt_one)
  have hc1 : |c| < 1 := by rw [abs_of_pos hc.1]; exact hc.2.trans_le (min_le_right _ _)
  obtain ⟨H, hPL, hval, hoff, hfst, hinv⟩ := exists_normal_motion r c hc1
  refine ⟨J, c, H, hJ, hJK, ⟨hc.1, hc.2.trans_le (min_le_left _ _)⟩,
    hPL, hval, hoff, hfst, hinv, hm, hflat c, disjoint_left.mpr ?_⟩
  intro p hp hpJ
  have hrho : rho p ≠ 0 := by
    change -normalMargin r (p.1, 0) ≠ 0
    apply neg_ne_zero.mpr (ne_of_gt ?_)
    have hnorm : ‖(p.1, (0 : ℝ))‖ = ‖p.1‖ := by
      rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg p.1)]
    unfold normalMargin
    rw [hnorm]
    exact lt_max_of_lt_right (sub_pos.mpr hpJ.2)
  apply havoid p ⟨hpJ.1, hrho⟩
  rw [normal_motion_plane_image hval] at hp
  change p.2 = c * normalMargin r (p.1, 0) at hp
  change p.2 + c * (-normalMargin r (p.1, 0)) = 0
  rw [hp]
  ring

end PoincareConjecture.M76.CollarMesh
