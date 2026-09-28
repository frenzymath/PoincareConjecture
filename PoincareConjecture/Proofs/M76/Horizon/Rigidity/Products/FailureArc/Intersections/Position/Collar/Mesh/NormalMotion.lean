import PoincareConjecture.Proofs.M76.Mathlib.SupportedPlanarShear

set_option autoImplicit false
open Set Geometry
open scoped NNReal

namespace PoincareConjecture.M76
namespace CollarMesh

local notation "E" => ((ℝ × ℝ) × ℝ)

noncomputable def normalMargin (r : ℝ) (p : E) : ℝ := max 0 (r - ‖p‖)

theorem lipschitzWith_normalMargin (r : ℝ) : LipschitzWith 1 (normalMargin r) := by
  have h : LipschitzWith 1 (fun p : E => r - ‖p‖) := by
    simpa using (LipschitzWith.const r).sub
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : E → ℝ))
  exact h.const_max 0

theorem finitePiecewiseAffineOn_normalMargin (r : ℝ)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    FinitePiecewiseAffineOn (normalMargin r) K.space := by
  let x := ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)).toContinuousAffineMap
  let y := ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)).toContinuousAffineMap
  let z := (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap
  have hx := (K.affineOnFaces_affine x).finitePiecewiseAffineOn hK
  have hy := (K.affineOnFaces_affine y).finitePiecewiseAffineOn hK
  have hz := (K.affineOnFaces_affine z).finitePiecewiseAffineOn hK
  have hnx := (K.affineOnFaces_affine (-x)).finitePiecewiseAffineOn hK
  have hny := (K.affineOnFaces_affine (-y)).finitePiecewiseAffineOn hK
  have hnz := (K.affineOnFaces_affine (-z)).finitePiecewiseAffineOn hK
  have hn : FinitePiecewiseAffineOn (norm : E → ℝ) K.space := by
    apply (((hx.max hnx).max (hy.max hny)).max (hz.max hnz)).congr
    intro p _
    change max (max (max p.1.1 (-p.1.1)) (max p.1.2 (-p.1.2)))
      (max p.2 (-p.2)) = ‖p‖
    simp only [Prod.norm_def, Real.norm_eq_abs, abs_eq_max_neg]
  have hr := (K.affineOnFaces_affine (ContinuousAffineMap.const ℝ E r)).finitePiecewiseAffineOn hK
  exact (hr.sub hn).positivePart

theorem exists_normal_motion (r c : ℝ) (hc : |c| < 1) :
    ∃ H : E ≃ₜ E,
      H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E ∧
      (∀ p, H p = (p.1, p.2 + c * normalMargin r p)) ∧
      EqOn H id (Metric.closedBall (0 : E) r)ᶜ ∧
      (∀ p, (H p).1 = p.1) ∧
      (∀ p, (H.symm p).1 = p.1) := by
  let L : ℝ≥0 := ⟨|c|, abs_nonneg c⟩
  let u : E → E := fun p => (0, c * normalMargin r p)
  have hu : LipschitzWith L u := by
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro p q
    have hv : |normalMargin r p - normalMargin r q| ≤ ‖p - q‖ := by
      simpa only [Real.norm_eq_abs, NNReal.coe_one, one_mul] using
        (lipschitzWith_normalMargin r).norm_sub_le p q
    change ‖((0 : ℝ × ℝ) - 0, c * normalMargin r p - c * normalMargin r q)‖ ≤
      |c| * ‖p - q‖
    simp only [sub_self, Prod.norm_def, norm_zero, Real.norm_eq_abs, ← mul_sub, abs_mul]
    rw [max_eq_right (mul_nonneg (abs_nonneg c) (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_left hv (abs_nonneg c)
  obtain ⟨H, hH⟩ := hu.exists_homeomorph_add (show L < 1 from hc)
  have hval (p : E) : H p = (p.1, p.2 + c * normalMargin r p) := by
    rw [hH]
    exact Prod.ext (add_zero p.1) rfl
  have hfirst (p : E) : (H p).1 = p.1 := by rw [hval]
  refine ⟨H, ?_, hval, ?_, hfirst, ?_⟩
  · apply (mem_piecewiseAffineGroupoid_iff_forward H.toOpenPartialHomeomorph).mpr
    intro p _
    obtain ⟨K, hK, hpK, _⟩ :=
      SimplicialComplex.exists_finite_neighborhood_subset_normed
        isCompact_singleton isOpen_univ (singleton_subset_iff.mpr (mem_univ p))
    have hm := finitePiecewiseAffineOn_normalMargin r K hK
    have hcPL := hm.postcomp (c • ContinuousAffineMap.id ℝ ℝ)
    have hf := (K.affineOnFaces_affine
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
    have hs := (K.affineOnFaces_affine
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
    obtain ⟨J, hJ, hJK, hPL⟩ := hf.prod_mk (hs.add hcPL)
    refine ⟨J, hJ, ?_, fun _ _ => mem_univ _, ?_⟩
    · rw [hJK]
      exact hpK (mem_singleton p)
    · exact hPL.congr (fun q _ => (hval q).symm)
  · intro p hp
    have hnorm : r ≤ ‖p‖ := le_of_lt (by simpa using hp)
    rw [hval, normalMargin, max_eq_left (sub_nonpos.mpr hnorm), mul_zero, add_zero]
    rfl
  · intro p
    simpa only [H.apply_symm_apply] using (hfirst (H.symm p)).symm

theorem exists_normal_motion_avoiding_plane {r c : ℝ}
    (hc : |c| < 1) (hc0 : c ≠ 0) :
    ∃ H : E ≃ₜ E,
      H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E ∧
      EqOn H id (Metric.closedBall (0 : E) r)ᶜ ∧
      (∀ p, (H p).1 = p.1) ∧
      (∀ p, (H.symm p).1 = p.1) ∧
      Disjoint (H '' {p : E | p.2 = 0})
        ({p : E | p.2 = 0} ∩ Metric.ball (0 : E) r) := by
  obtain ⟨H, hPL, hval, hoff, hfst, hinv⟩ := exists_normal_motion r c hc
  refine ⟨H, hPL, hoff, hfst, hinv, disjoint_left.mpr ?_⟩
  rintro p ⟨q, hq, rfl⟩ ⟨hp, hball⟩
  have heq : H q = q := Prod.ext (hfst q) (hp.trans hq.symm)
  have hqr : ‖q‖ < r := by simpa only [heq, Metric.mem_ball, dist_zero_right] using hball
  have hmargin : 0 < normalMargin r q := lt_max_of_lt_right (sub_pos.mpr hqr)
  have hz : c * normalMargin r q = 0 := by
    have hq' : q.2 = 0 := hq
    have hp' : (H q).2 = 0 := hp
    have ht : (H q).2 = q.2 + c * normalMargin r q := by rw [hval]
    rw [hp', hq', zero_add] at ht
    exact ht.symm
  exact (mul_ne_zero hc0 (ne_of_gt hmargin)) hz

end CollarMesh
end PoincareConjecture.M76
