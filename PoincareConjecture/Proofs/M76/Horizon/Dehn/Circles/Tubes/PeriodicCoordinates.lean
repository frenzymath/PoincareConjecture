import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondSquareCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.IdentityAnnulus
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedPeriodCut

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

noncomputable def periodicTubeCoordinates (L d α β : ℝ) : C3 →ᴬ[ℝ] C3 :=
  ((signedSquareToDiamond.toContinuousLinearMap.comp
    (d⁻¹ • ContinuousLinearMap.fst ℝ P2 ℝ)).toContinuousAffineMap).prod
    (ContinuousAffineMap.const ℝ C3 α +
      (((β - α) / (4 * L)) • ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap)

theorem periodicTubeCoordinates_apply (L d α β : ℝ) (z : C3) :
    periodicTubeCoordinates L d α β z =
      (signedSquareToDiamond (d⁻¹ • z.1), α + ((β - α) / (4 * L)) * z.2) := rfl

theorem periodicTubeCoordinates_mapsTo {L d α β : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hab : α < β) :
    MapsTo (periodicTubeCoordinates L d α β) (_root_.Dehn.identityTube L d)
      (signedTubeDiamond ×ˢ Icc α β) := by
  rintro ⟨⟨x, y⟩, s⟩ ⟨⟨hx, hy⟩, hs⟩
  have hp : 0 < 4 * L := by positivity
  have hc : 0 < (β - α) / (4 * L) := div_pos (sub_pos.mpr hab) hp
  refine ⟨(signedSquareToDiamond_mem _).mpr ?_, ?_, ?_⟩
  · change (-1 ≤ d⁻¹ * x ∧ d⁻¹ * x ≤ 1) ∧
      (-1 ≤ d⁻¹ * y ∧ d⁻¹ * y ≤ 1)
    simp only [← div_eq_inv_mul, le_div_iff₀ hd, div_le_iff₀ hd, neg_one_mul, one_mul]
    exact ⟨hx, hy⟩
  · change α ≤ α + ((β - α) / (4 * L)) * s
    nlinarith [mul_nonneg hc.le hs.1]
  · change α + ((β - α) / (4 * L)) * s ≤ β
    have h := mul_le_mul_of_nonneg_left hs.2 hc.le
    rw [div_mul_cancel₀ _ hp.ne'] at h
    linarith

theorem periodicTubeCoordinates_injective {L d α β : ℝ}
    (hL : L ≠ 0) (hd : d ≠ 0) (hab : α ≠ β) :
    Function.Injective (periodicTubeCoordinates L d α β) := by
  intro x y h
  have hc : (β - α) / (4 * L) ≠ 0 := div_ne_zero (sub_ne_zero.mpr hab.symm)
    (mul_ne_zero (by norm_num) hL)
  have hxy := signedSquareToDiamond.injective (congrArg Prod.fst h)
  have ht := congrArg Prod.snd h
  apply Prod.ext
  · exact (smul_right_injective _ (inv_ne_zero hd)) hxy
  · change α + ((β - α) / (4 * L)) * x.2 =
      α + ((β - α) / (4 * L)) * y.2 at ht
    exact mul_left_cancel₀ hc (add_left_cancel ht)

theorem periodicTubeCoordinates_image {L d α β : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hab : α < β) :
    periodicTubeCoordinates L d α β '' _root_.Dehn.identityTube L d =
      signedTubeDiamond ×ˢ Icc α β := by
  apply Subset.antisymm
  · exact (periodicTubeCoordinates_mapsTo hL hd hab).image_subset
  · rintro ⟨v, t⟩ ⟨hv, ht⟩
    let w := signedSquareToDiamond.symm v
    have hw : w ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
      (signedSquareToDiamond_mem w).mp (by simpa only [w,
        ContinuousLinearEquiv.apply_symm_apply] using hv)
    have hp : 0 < 4 * L := by positivity
    have hdiff : 0 < β - α := sub_pos.mpr hab
    refine ⟨(d • w, (4 * L) * ((t - α) / (β - α))), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · change (-d ≤ d * w.1 ∧ d * w.1 ≤ d) ∧
          (-d ≤ d * w.2 ∧ d * w.2 ≤ d)
        constructor <;> constructor <;> nlinarith [hw.1.1, hw.1.2, hw.2.1, hw.2.2]
      · exact mul_nonneg hp.le (div_nonneg (sub_nonneg.mpr ht.1) hdiff.le)
      · have hr : (t - α) / (β - α) ≤ 1 :=
          (div_le_one hdiff).mpr (by linarith [ht.2])
        nlinarith
    · rw [periodicTubeCoordinates_apply, smul_smul, inv_mul_cancel₀ hd.ne', one_smul]
      apply Prod.ext
      · exact signedSquareToDiamond.apply_symm_apply v
      · dsimp
        field_simp
        ring

theorem periodicTubeCoordinates_finitePL {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (α β : ℝ) : FinitePiecewiseAffineOn (periodicTubeCoordinates L d α β)
      (_root_.Dehn.identityTube L d) := by
  have hbox := ((isFinitePLBallPair_Icc (show -d < d by linarith)).prod
    (isFinitePLBallPair_Icc (show -d < d by linarith))).prod
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 4 * L by positivity))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hbox
  exact ⟨K, hK, hKs, K.affineOnFaces_affine (periodicTubeCoordinates L d α β)⟩

theorem periodicTubeCoordinates_sheet {L d α β : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hab : α < β)
    (j : Fin 2) (z : C3) (hz : z ∈ _root_.Dehn.identityTube L d) :
    (periodicTubeCoordinates L d α β z).1 ∈ signedTubeSheet j ↔
      z.1.2 = if j = 0 then z.1.1 else -z.1.1 := by
  have hm := (periodicTubeCoordinates_mapsTo hL hd hab hz).1
  rw [signedTubeSheet_coordinate_iff _ hm]
  rw [periodicTubeCoordinates_apply, signedSquareToDiamond_apply]
  fin_cases j <;> norm_num <;> constructor <;> intro h
  · have h' : d⁻¹ * z.1.1 = d⁻¹ * z.1.2 := by linarith
    exact (mul_left_cancel₀ (inv_ne_zero hd.ne') h').symm
  · simp [h]
  · have h' : d⁻¹ * z.1.2 = d⁻¹ * (-z.1.1) := by linarith
    exact mul_left_cancel₀ (inv_ne_zero hd.ne') h'
  · simp [h]

end PoincareConjecture.M76.Dehn
