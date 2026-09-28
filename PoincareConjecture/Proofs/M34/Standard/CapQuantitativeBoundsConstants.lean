import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Analysis.SpecialFunctions.Pow.Real










set_option autoImplicit false

namespace PoincareConjecture.M34



noncomputable def capPersistenceUpperConstant (C : ℝ) : ℝ :=
  (2 * C) ^ 2 + 4 * C * (2 * C) ^ (1 / 2 : ℝ) +
    8 * C * (2 * C) ^ (3 / 2 : ℝ) +
    (C * C ^ (3 / 2 : ℝ) + 1) * (2 * C) ^ (3 / 2 : ℝ) +
    (C * C ^ 2 + 1) * (2 * C) ^ 2 + 1



theorem capPersistenceUpperConstant_witnesses {C : ℝ} (hC : 0 ≤ C) :
    (2 * C) ^ 2 < capPersistenceUpperConstant C ∧
    4 * C * (2 * C) ^ (1 / 2 : ℝ) < capPersistenceUpperConstant C ∧
    8 * C * (2 * C) ^ (3 / 2 : ℝ) < capPersistenceUpperConstant C ∧
    (C * C ^ (3 / 2 : ℝ) + 1) * (2 * C) ^ (3 / 2 : ℝ) < capPersistenceUpperConstant C ∧
    (C * C ^ 2 + 1) * (2 * C) ^ 2 < capPersistenceUpperConstant C := by
  have h1 : 0 ≤ (2 * C) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ 4 * C * (2 * C) ^ (1 / 2 : ℝ) := by positivity
  have h3 : 0 ≤ 8 * C * (2 * C) ^ (3 / 2 : ℝ) := by positivity
  have h4 : 0 ≤ (C * C ^ (3 / 2 : ℝ) + 1) * (2 * C) ^ (3 / 2 : ℝ) := by positivity
  have h5 : 0 ≤ (C * C ^ 2 + 1) * (2 * C) ^ 2 := by positivity
  unfold capPersistenceUpperConstant
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩



theorem capPersistenceUpperConstant_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < capPersistenceUpperConstant C :=
  (sq_nonneg (2 * C)).trans_lt (capPersistenceUpperConstant_witnesses hC).1



noncomputable def capPersistenceConstant (C beta : ℝ) : ℝ :=
  capPersistenceUpperConstant C + beta⁻¹ + 1




theorem capPersistenceConstant_bounds {C beta : ℝ} (hC : 0 ≤ C) (hbeta : 0 < beta) :
    0 < capPersistenceConstant C beta ∧
    capPersistenceUpperConstant C < capPersistenceConstant C beta ∧
    (capPersistenceConstant C beta)⁻¹ < beta := by
  have hB := capPersistenceUpperConstant_pos hC
  have hi := inv_pos.mpr hbeta
  have hK : 0 < capPersistenceConstant C beta := by
    unfold capPersistenceConstant
    positivity
  have hBK : capPersistenceUpperConstant C < capPersistenceConstant C beta := by
    unfold capPersistenceConstant
    linarith
  have hiK : beta⁻¹ < capPersistenceConstant C beta := by
    unfold capPersistenceConstant
    linarith
  refine ⟨hK, hBK, ?_⟩
  simpa only [inv_inv] using (inv_lt_inv₀ hK hi).mpr hiK

end PoincareConjecture.M34
