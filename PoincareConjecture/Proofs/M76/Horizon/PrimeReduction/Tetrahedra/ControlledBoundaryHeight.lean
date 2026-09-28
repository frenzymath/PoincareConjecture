import PoincareConjecture.Proofs.M76.Mathlib.UniformConvexPLLipschitz
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PunctureBallTriangulation









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76

theorem exists_finitePL_disk_height_preserving_zero_set
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D R : Set E} (hD : IsFinitePLBallPair (ℝ × ℝ) D R)
    {F : E × ℝ → ℝ} (hF : FinitePiecewiseAffineOn F (D ×ˢ Icc (0 : ℝ) 1))
    (hbound : ∀ z ∈ D ×ˢ Icc (0 : ℝ) 1, F z ∈ Icc 0 1)
    (hzero : ∀ x ∈ D, F (x, 0) = 0 ↔ x ∈ R) :
    ∃ h : E → ℝ, FinitePiecewiseAffineOn h D ∧
      ∀ x ∈ D, h x ∈ Icc 0 1 ∧ (h x = 0 ↔ x ∈ R) ∧
        (F (x, h x) = 0 ↔ x ∈ R) := by
  obtain ⟨K, _, hK, hKs, _, _⟩ := hD.exists_finite_carrier_and_rim_complexes
  let b : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E (0 : ℝ))
  have hb : FinitePiecewiseAffineOn b D :=
    ⟨K, hK, hKs, K.affineOnFaces_affine b⟩
  have hbmap : MapsTo b D (D ×ˢ Icc (0 : ℝ) 1) := fun x hx => ⟨hx, by simp [b]⟩
  have hf : FinitePiecewiseAffineOn (fun x => F (x, 0)) D := hF.comp hb hbmap
  obtain ⟨L, hL⟩ := hF.exists_uniform_vertical_lipschitzOnWith
  let c : ℝ := 1 / (2 * ((L : ℝ) + 1))
  have hden : 0 < 2 * ((L : ℝ) + 1) := by positivity
  have hc : 0 < c := one_div_pos.mpr hden
  have hc1 : c ≤ 1 := (div_le_one hden).mpr (by nlinarith [L.coe_nonneg])
  have hLc : (L : ℝ) * c < 1 := by
    change (L : ℝ) * (1 / (2 * ((L : ℝ) + 1))) < 1
    rw [mul_one_div]
    exact (div_lt_one hden).mpr (by nlinarith [L.coe_nonneg])
  let h : E → ℝ := fun x => c * F (x, 0)
  have hh : FinitePiecewiseAffineOn h D :=
    hf.postcomp (c • ContinuousAffineMap.id ℝ ℝ)
  refine ⟨h, hh, fun x hx => ?_⟩
  have hfbound : F (x, 0) ∈ Icc 0 1 := hbound (x, 0) ⟨hx, by simp⟩
  have hhbound : h x ∈ Icc 0 1 := ⟨mul_nonneg hc.le hfbound.1,
    (mul_le_mul_of_nonneg_left hfbound.2 hc.le).trans (by simpa using hc1)⟩
  have hhzero : h x = 0 ↔ x ∈ R := by
    change c * F (x, 0) = 0 ↔ x ∈ R
    rw [mul_eq_zero, or_iff_right hc.ne']
    exact hzero x hx
  refine ⟨hhbound, hhzero, ?_⟩
  constructor
  · intro hz
    by_contra hxr
    have hfp : 0 < F (x, 0) := lt_of_le_of_ne hfbound.1
      (Ne.symm (fun h => hxr ((hzero x hx).mp h)))
    have hsmall : (L : ℝ) * h x < F (x, 0) := by
      change (L : ℝ) * (c * F (x, 0)) < F (x, 0)
      rw [← mul_assoc]
      simpa only [one_mul] using mul_lt_mul_of_pos_right hLc hfp
    have hdist := (hL x hx).dist_le_mul (h x) hhbound 0 (by simp)
    rw [hz, Real.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hfp,
      sub_zero, abs_of_nonneg hhbound.1] at hdist
    exact (not_le_of_gt hsmall) hdist
  · intro hxr
    rw [hhzero.mpr hxr]
    exact (hzero x hx).mpr hxr

end PoincareConjecture.M76
