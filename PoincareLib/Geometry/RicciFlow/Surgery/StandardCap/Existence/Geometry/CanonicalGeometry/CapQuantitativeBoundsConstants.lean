import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Cap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# One cap constant before the limit and convergence index

Five actual upper-field witnesses and the positive normalized-ball volume
coefficient determine one strict common constant. Source: Definition 9.72,
pp. 230-231, and Theorem 12.28, pp. 323-324;
cap-quantitative-bounds.md, section 3.
-/

set_option autoImplicit false

namespace PoincareMT.M34

/-- A common strict upper bound for the five transferred cap witnesses,
depending only on the prior classification constant (Theorem 12.28). -/
noncomputable def capPersistenceUpperConstant (C : ℝ) : ℝ :=
  (2 * C) ^ 2 + 4 * C * (2 * C) ^ (1 / 2 : ℝ) +
    8 * C * (2 * C) ^ (3 / 2 : ℝ) +
    (C * C ^ (3 / 2 : ℝ) + 1) * (2 * C) ^ (3 / 2 : ℝ) +
    (C * C ^ 2 + 1) * (2 * C) ^ 2 + 1

/-- Each individual quantitative coefficient is strictly below the
chosen common upper constant (Definition 9.72, Theorem 12.28). -/
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

/-- The common upper constant is positive, including at C=0
(Definition 9.72, Theorem 12.28). -/
theorem capPersistenceUpperConstant_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < capPersistenceUpperConstant C :=
  (sq_nonneg (2 * C)).trans_lt (capPersistenceUpperConstant_witnesses hC).1

/-- The final constant also leaves a strict normalized-ball lower-volume
witness; it precedes every cap, map and radius (Theorem 12.28). -/
noncomputable def capPersistenceConstant (C beta : ℝ) : ℝ :=
  capPersistenceUpperConstant C + beta⁻¹ + 1

/-- Positive beta supplies both strict upper-field margins and the
strict inverse-constant margin required by the actual cap record
(Definition 9.72(4)-(8)). -/
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

end PoincareMT.M34
