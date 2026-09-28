import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.NormalMotion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.FiniteContacts
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FreeFaceCarrierBounds

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.CollarMesh
local notation "E" => ((ℝ × ℝ) × ℝ)

theorem normal_motion_plane_image {H : E ≃ₜ E} {r c : ℝ}
    (hval : ∀ p, H p = (p.1, p.2 + c * normalMargin r p)) :
    H '' {p : E | p.2 = 0} =
      {p : E | p.2 = c * normalMargin r (p.1, 0)} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change (H q).2 = c * normalMargin r ((H q).1, 0)
    have hq' : q.2 = 0 := hq
    rw [hval]
    change q.2 + c * normalMargin r q = c * normalMargin r (q.1, 0)
    rw [hq', zero_add]
    congr 2
    exact Prod.ext rfl hq'
  · intro hp
    refine ⟨(p.1, 0), rfl, ?_⟩
    rw [hval]
    apply Prod.ext
    · rfl
    · exact (zero_add _).trans hp.symm

theorem finitePiecewiseAffineOn_normalBaseMargin (r : ℝ)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    FinitePiecewiseAffineOn (fun p : E => normalMargin r (p.1, 0)) K.space := by
  let x := ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)).toContinuousAffineMap
  let y := ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)).toContinuousAffineMap
  have hx := (K.affineOnFaces_affine x).finitePiecewiseAffineOn hK
  have hy := (K.affineOnFaces_affine y).finitePiecewiseAffineOn hK
  have hnx := (K.affineOnFaces_affine (-x)).finitePiecewiseAffineOn hK
  have hny := (K.affineOnFaces_affine (-y)).finitePiecewiseAffineOn hK
  have hn : FinitePiecewiseAffineOn (fun p : E => ‖p.1‖) K.space := by
    apply ((hx.max hnx).max (hy.max hny)).congr
    intro p _
    change max (max p.1.1 (-p.1.1)) (max p.1.2 (-p.1.2)) = ‖p.1‖
    simp only [Prod.norm_def, Real.norm_eq_abs, abs_eq_max_neg]
  have hr := (K.affineOnFaces_affine (ContinuousAffineMap.const ℝ E r)).finitePiecewiseAffineOn hK
  apply (hr.sub hn).positivePart.congr
  intro p _
  have hp : ‖(p.1, (0 : ℝ))‖ = ‖p.1‖ := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg p.1)]
  change max 0 (r - ‖p.1‖) = max 0 (r - ‖(p.1, (0 : ℝ))‖)
  rw [hp]

theorem exists_normal_motion_finite_edge_contacts
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hcard : ∀ s ∈ K.faces, s.card ≤ 2) (r : ℝ)
    (hfixed : (K.space ∩ {p : E | p.2 = 0 ∧ r ≤ ‖p.1‖}).Finite)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ c ∈ Ioo (0 : ℝ) epsilon, ∃ H : E ≃ₜ E,
      H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E ∧
      (∀ p, H p = (p.1, p.2 + c * normalMargin r p)) ∧
      EqOn H id (Metric.closedBall (0 : E) r)ᶜ ∧
      (∀ p, (H p).1 = p.1) ∧
      (∀ p, (H.symm p).1 = p.1) ∧
      (H '' {p : E | p.2 = 0} ∩ K.space).Finite := by
  let rho : E → ℝ := fun p => -normalMargin r (p.1, 0)
  have hrho : FinitePiecewiseAffineOn rho K.space :=
    (finitePiecewiseAffineOn_normalBaseMargin r K hK).postcomp
      (-ContinuousAffineMap.id ℝ ℝ)
  obtain ⟨J, hJ, hJs, hJrho⟩ := hrho
  have hJcard : ∀ s ∈ J.faces, s.card ≤ 2 := fun s hs =>
    J.face_card_le_of_hull_subset_finite_carrier K hK hs
      ((J.convexHull_subset_space hs).trans hJs.subset) hcard
  have hfixedJ : (J.space ∩ {p : E | p.2 = 0 ∧ rho p = 0}).Finite := by
    apply hfixed.subset
    rintro p ⟨hp, hpz, hprho⟩
    refine ⟨hJs.subset hp, hpz, ?_⟩
    have hm : normalMargin r (p.1, 0) = 0 := neg_eq_zero.mp hprho
    have hn : r - ‖p.1‖ ≤ 0 := by
      have h := le_max_right 0 (r - ‖(p.1, (0 : ℝ))‖)
      change r - ‖(p.1, (0 : ℝ))‖ ≤ normalMargin r (p.1, 0) at h
      rw [hm] at h
      have hp : ‖(p.1, (0 : ℝ))‖ = ‖p.1‖ := by
        rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg p.1)]
      rwa [hp] at h
    linarith
  obtain ⟨c, hc, _, hfinite⟩ := exists_finite_contacts_normal_parameter J hJ hJcard
    (J.affineOnFaces_affine (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap)
    hJrho hfixedJ (lt_min hepsilon zero_lt_one)
  have hc1 : |c| < 1 := by rw [abs_of_pos hc.1]; exact hc.2.trans_le (min_le_right _ _)
  obtain ⟨H, hPL, hval, hoff, hfst, hinv⟩ := exists_normal_motion r c hc1
  refine ⟨c, ⟨hc.1, hc.2.trans_le (min_le_left _ _)⟩, H,
    hPL, hval, hoff, hfst, hinv, ?_⟩
  rw [normal_motion_plane_image hval]
  apply hfinite.subset
  rintro p ⟨hp, hpK⟩
  refine ⟨hJs.symm.subset hpK, ?_⟩
  change p.2 + c * (-normalMargin r (p.1, 0)) = 0
  change p.2 = c * normalMargin r (p.1, 0) at hp
  rw [hp]
  ring

theorem exists_normal_motion_finite_local_edge_contacts
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hcard : ∀ s ∈ K.faces, s.card ≤ 2) (r : ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ c ∈ Ioo (0 : ℝ) epsilon, ∃ H : E ≃ₜ E,
      H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E ∧
      (∀ p, H p = (p.1, p.2 + c * normalMargin r p)) ∧
      EqOn H id (Metric.closedBall (0 : E) r)ᶜ ∧
      (∀ p, (H p).1 = p.1) ∧
      (∀ p, (H.symm p).1 = p.1) ∧
      (H '' {p : E | p.2 = 0} ∩ K.space ∩ {p : E | ‖p.1‖ < r}).Finite := by
  let rho : E → ℝ := fun p => -normalMargin r (p.1, 0)
  have hrho : FinitePiecewiseAffineOn rho K.space :=
    (finitePiecewiseAffineOn_normalBaseMargin r K hK).postcomp
      (-ContinuousAffineMap.id ℝ ℝ)
  obtain ⟨J, hJ, hJs, hJrho⟩ := hrho
  have hJcard : ∀ s ∈ J.faces, s.card ≤ 2 := fun s hs =>
    J.face_card_le_of_hull_subset_finite_carrier K hK hs
      ((J.convexHull_subset_space hs).trans hJs.subset) hcard
  obtain ⟨c, hc, _, hfinite⟩ := exists_finite_moving_contacts_normal_parameter J hJ hJcard
    (J.affineOnFaces_affine (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap)
    hJrho (lt_min hepsilon zero_lt_one)
  have hc1 : |c| < 1 := by rw [abs_of_pos hc.1]; exact hc.2.trans_le (min_le_right _ _)
  obtain ⟨H, hPL, hval, hoff, hfst, hinv⟩ := exists_normal_motion r c hc1
  refine ⟨c, ⟨hc.1, hc.2.trans_le (min_le_left _ _)⟩, H,
    hPL, hval, hoff, hfst, hinv, ?_⟩
  rw [normal_motion_plane_image hval]
  apply hfinite.subset
  rintro p ⟨⟨hp, hpK⟩, hpr⟩
  refine ⟨hJs.symm.subset hpK, ?_, ?_⟩
  · change p.2 + c * (-normalMargin r (p.1, 0)) = 0
    change p.2 = c * normalMargin r (p.1, 0) at hp
    rw [hp]
    ring
  · change -normalMargin r (p.1, 0) ≠ 0
    apply neg_ne_zero.mpr
    apply ne_of_gt
    have hnorm : ‖(p.1, (0 : ℝ))‖ = ‖p.1‖ := by
      rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg p.1)]
    unfold normalMargin
    rw [hnorm]
    exact lt_max_of_lt_right (sub_pos.mpr hpr)

end PoincareConjecture.M76.CollarMesh
