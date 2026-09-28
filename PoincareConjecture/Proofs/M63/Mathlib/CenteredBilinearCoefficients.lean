import Mathlib.Analysis.Normed.Operator.Bilinear









set_option autoImplicit false

namespace PoincareConjecture.M63




theorem norm_centeredBilinearCoefficients_sub_le
    {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : S →L[ℝ] S) (hJ : ∀ u, ‖J u‖ ≤ ‖u‖) (M : E →L[ℝ] S →L[ℝ] S)
    (G : S → E) (Q : S → S) (V : S)
    {W r eps KG KQ : ℝ} (_hW : 0 ≤ W) (hr : 0 < r)
    (heps : 0 ≤ eps) (hKG : 0 ≤ KG) (_hKQ : 0 ≤ KQ)
    (hV : ‖V‖ ≤ W) (hG0 : ‖G V‖ ≤ eps)
    (hG : ∀ u v, ‖u‖ ≤ W + r → ‖v‖ ≤ W + r → ‖G u - G v‖ ≤ KG * ‖u - v‖)
    (hQ : ∀ u v, ‖u‖ ≤ W + r → ‖v‖ ≤ W + r → ‖Q u - Q v‖ ≤ KQ * ‖u - v‖)
    (z z' : S) (hz : ‖z‖ ≤ r) (hz' : ‖z'‖ ≤ r) :
    ‖G (V + z) - G (V + z')‖ ≤ KG * ‖z - z'‖ ∧
      ‖(Q (V + z) - M (G (V + z)) (J (V + z))) -
        (Q (V + z') - M (G (V + z')) (J (V + z')))‖ ≤
        (KQ + ‖M‖ * (KG * (W + r) + eps + KG * r)) * ‖z - z'‖ := by
  have hu : ‖V + z‖ ≤ W + r := (norm_add_le _ _).trans (add_le_add hV hz)
  have hv : ‖V + z'‖ ≤ W + r := (norm_add_le _ _).trans (add_le_add hV hz')
  have hGdiff : ‖G (V + z) - G (V + z')‖ ≤ KG * ‖z - z'‖ := by
    simpa only [add_sub_add_left_eq_sub] using hG _ _ hu hv
  have hQdiff : ‖Q (V + z) - Q (V + z')‖ ≤ KQ * ‖z - z'‖ := by
    simpa only [add_sub_add_left_eq_sub] using hQ _ _ hu hv
  have hGv : ‖G (V + z')‖ ≤ eps + KG * r := by
    have hdiff := hG (V + z') V hv (hV.trans (le_add_of_nonneg_right hr.le))
    simp only [add_sub_cancel_left] at hdiff
    calc
      _ ≤ ‖G (V + z') - G V‖ + ‖G V‖ := norm_le_norm_sub_add _ _
      _ ≤ KG * ‖z'‖ + eps := add_le_add hdiff hG0
      _ ≤ eps + KG * r := by nlinarith only [mul_le_mul_of_nonneg_left hz' hKG]
  have heq : (Q (V + z) - M (G (V + z)) (J (V + z))) -
      (Q (V + z') - M (G (V + z')) (J (V + z'))) =
      (Q (V + z) - Q (V + z')) -
        (M (G (V + z) - G (V + z')) (J (V + z)) + M (G (V + z')) (J (z - z'))) := by
    simp only [map_sub, map_add, sub_apply]
    abel
  refine ⟨hGdiff, ?_⟩
  rw [heq]
  calc
    _ ≤ ‖Q (V + z) - Q (V + z')‖ +
        (‖M (G (V + z) - G (V + z')) (J (V + z))‖ +
          ‖M (G (V + z')) (J (z - z'))‖) :=
      (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ KQ * ‖z - z'‖ +
        (‖M‖ * ‖G (V + z) - G (V + z')‖ * ‖J (V + z)‖ +
          ‖M‖ * ‖G (V + z')‖ * ‖J (z - z')‖) :=
      add_le_add hQdiff (add_le_add (M.le_opNorm₂ _ _) (M.le_opNorm₂ _ _))
    _ ≤ KQ * ‖z - z'‖ +
        (‖M‖ * (KG * ‖z - z'‖) * (W + r) +
          ‖M‖ * (eps + KG * r) * ‖z - z'‖) := by
      gcongr
      · exact hJ (V + z) |>.trans hu
      · exact hJ (z - z')
    _ = _ := by ring

end PoincareConjecture.M63
