import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMinimum
import PoincareConjecture.Proofs.M76.Mathlib.SmallLipschitzHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse

set_option autoImplicit false

open Set Geometry
open scoped NNReal

namespace Geometry

theorem FinitePiecewiseAffineOn.max {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f g : E → ℝ} {S : Set E} (hf : FinitePiecewiseAffineOn f S)
    (hg : FinitePiecewiseAffineOn g S) :
    FinitePiecewiseAffineOn (fun x => max (f x) (g x)) S := by
  apply (hf.add (hg.sub hf).positivePart).congr
  intro x _
  change f x + Max.max 0 (g x - f x) = Max.max (f x) (g x)
  by_cases h : f x ≤ g x
  · rw [max_eq_right h, max_eq_right (sub_nonneg.mpr h)]
    ring
  · rw [max_eq_left (le_of_not_ge h), max_eq_left (by linarith)]
    ring

end Geometry

namespace SupportedPlanarShear

noncomputable def margin (R : ℝ) (z : ℝ × ℝ) : ℝ :=
  max 0 (R - ‖z‖)

noncomputable def clippedCoordinate (R : ℝ) (z : ℝ × ℝ) : ℝ :=
  max (-margin R z) (min z.2 (margin R z))

theorem lipschitzWith_margin (R : ℝ) : LipschitzWith 1 (margin R) := by
  have h : LipschitzWith 1 (fun z : ℝ × ℝ => R - ‖z‖) := by
    simpa using (LipschitzWith.const R).sub
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : (ℝ × ℝ) → ℝ))
  exact h.const_max 0

theorem lipschitzWith_clippedCoordinate (R : ℝ) :
    LipschitzWith 1 (clippedCoordinate R) := by
  have h := lipschitzWith_margin R
  change LipschitzWith 1 (fun z => max (-margin R z) (min z.2 (margin R z)))
  simpa only [Pi.neg_apply, max_self] using h.neg.max (LipschitzWith.prod_snd.min h)

theorem clippedCoordinate_eq_zero {R : ℝ} {z : ℝ × ℝ} (hz : R ≤ ‖z‖) :
    clippedCoordinate R z = 0 := by
  have hw : margin R z = 0 := max_eq_left (sub_nonpos.mpr hz)
  simp only [clippedCoordinate, hw, neg_zero]
  exact max_eq_left (min_le_right _ _)

theorem clippedCoordinate_eq_snd {R : ℝ} {z : ℝ × ℝ} (hz : 2 * ‖z‖ ≤ R) :
    clippedCoordinate R z = z.2 := by
  have hy : |z.2| ≤ ‖z‖ := norm_snd_le z
  have hw : |z.2| ≤ margin R z := by
    exact (show |z.2| ≤ R - ‖z‖ by linarith).trans (le_max_right _ _)
  rw [clippedCoordinate, min_eq_left (le_abs_self z.2 |>.trans hw),
    max_eq_right (by linarith [(abs_le.mp hw).1])]

theorem finitePiecewiseAffineOn_clippedCoordinate (R : ℝ)
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hK : K.faces.Finite) :
    FinitePiecewiseAffineOn (clippedCoordinate R) K.space := by
  let a := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  let b := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  have ha := (K.affineOnFaces_affine a).finitePiecewiseAffineOn hK
  have hb := (K.affineOnFaces_affine b).finitePiecewiseAffineOn hK
  have hna := (K.affineOnFaces_affine (-a)).finitePiecewiseAffineOn hK
  have hnb := (K.affineOnFaces_affine (-b)).finitePiecewiseAffineOn hK
  have hnorm : FinitePiecewiseAffineOn (norm : (ℝ × ℝ) → ℝ) K.space := by
    apply ((ha.max hna).max (hb.max hnb)).congr
    intro z _
    change max (max z.1 (-z.1)) (max z.2 (-z.2)) = ‖z‖
    simp only [Prod.norm_def, Real.norm_eq_abs, abs_eq_max_neg]
  have hR := (K.affineOnFaces_affine
    (ContinuousAffineMap.const ℝ (ℝ × ℝ) R)).finitePiecewiseAffineOn hK
  have hw : FinitePiecewiseAffineOn (margin R) K.space := (hR.sub hnorm).positivePart
  have hnw : FinitePiecewiseAffineOn (fun z => -margin R z) K.space := by
    exact (hw.postcomp (-ContinuousAffineMap.id ℝ ℝ)).congr (fun _ _ => rfl)
  exact hnw.max (hb.min hw)

noncomputable def shearMap (R c : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 + c * clippedCoordinate R z, z.2)

theorem finitePiecewiseAffineOn_shearMap (R c : ℝ)
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hK : K.faces.Finite) :
    FinitePiecewiseAffineOn (shearMap R c) K.space := by
  have ha := (K.affineOnFaces_affine
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  have hb := (K.affineOnFaces_affine
    (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  have hv : FinitePiecewiseAffineOn (fun z => c * clippedCoordinate R z) K.space := by
    exact ((finitePiecewiseAffineOn_clippedCoordinate R K hK).postcomp
      (c • ContinuousAffineMap.id ℝ ℝ)).congr (fun _ _ => rfl)
  exact (ha.add hv).prod_mk hb

theorem exists_shear_homeomorph (R c : ℝ) (hc : |c| < 1) :
    ∃ H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ),
      H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid (ℝ × ℝ) ∧
      (∀ z, H z = shearMap R c z) ∧
      (∀ z, R ≤ ‖z‖ → H z = z) ∧
      ∀ z, 2 * ‖z‖ ≤ R → H z = (z.1 + c * z.2, z.2) := by
  let L : ℝ≥0 := ⟨|c|, abs_nonneg c⟩
  let u : (ℝ × ℝ) → ℝ × ℝ := fun z => (c * clippedCoordinate R z, 0)
  have hu : LipschitzWith L u := by
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro x y
    have hv : |clippedCoordinate R x - clippedCoordinate R y| ≤ ‖x - y‖ := by
      simpa only [Real.norm_eq_abs, NNReal.coe_one, one_mul] using
        (lipschitzWith_clippedCoordinate R).norm_sub_le x y
    change ‖(c * clippedCoordinate R x - c * clippedCoordinate R y, (0 : ℝ) - 0)‖ ≤
      |c| * ‖x - y‖
    simp only [sub_self, Prod.norm_def, norm_zero, Real.norm_eq_abs, ← mul_sub, abs_mul]
    rw [max_eq_left (mul_nonneg (abs_nonneg c) (abs_nonneg _))]
    simpa only [Prod.norm_def, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left hv (abs_nonneg c)
  obtain ⟨H, hH⟩ := hu.exists_homeomorph_add (show L < 1 from hc)
  have hval (z : ℝ × ℝ) : H z = shearMap R c z := by
    rw [hH]
    exact Prod.ext rfl (add_zero z.2)
  refine ⟨H, ?_, hval, ?_, ?_⟩
  · apply (mem_piecewiseAffineGroupoid_iff_forward H.toOpenPartialHomeomorph).mpr
    intro z _
    obtain ⟨K, hK, hzK, hKU⟩ :=
      SimplicialComplex.exists_finite_neighborhood_subset_normed
        isCompact_singleton isOpen_univ (singleton_subset_iff.mpr (mem_univ z))
    obtain ⟨J, hJ, hJK, hPL⟩ := finitePiecewiseAffineOn_shearMap R c K hK
    refine ⟨J, hJ, ?_, fun _ _ => mem_univ _, ?_⟩
    · rw [hJK]
      exact hzK (mem_singleton z)
    · exact hPL.congr (fun x _ => (hval x).symm)
  · intro z hz
    rw [hval, shearMap, clippedCoordinate_eq_zero hz, mul_zero, add_zero]
  · intro z hz
    rw [hval, shearMap, clippedCoordinate_eq_snd hz]

end SupportedPlanarShear
