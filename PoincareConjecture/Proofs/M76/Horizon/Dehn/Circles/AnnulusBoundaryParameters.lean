import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusHomeomorph
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SquareAnnulusBoundary










set_option autoImplicit false

open Set

namespace PLAnnularStrip



theorem exists_period_parameter_of_depth {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) (p : squareAnnulus L d) :
    ∃ s ∈ Icc 0 (4 * L),
      (p : ℝ × ℝ) = annulusMap L (by linarith) ((s : AddCircle (4 * L)), depth L p) := by
  have hL : 0 < L := by linarith
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  obtain ⟨E, hE⟩ := exists_annulus_homeomorph hL hd.le hwidth
  let q := E.symm p
  let s : ℝ := AddCircle.equivIco (4 * L) 0 q.1
  have hs : s ∈ Icc 0 (4 * L) :=
    ⟨(AddCircle.equivIco (4 * L) 0 q.1).property.1,
      by simpa only [zero_add] using (AddCircle.equivIco (4 * L) 0 q.1).property.2.le⟩
  have hsq : (s : AddCircle (4 * L)) = q.1 := AddCircle.coe_equivIco
  have hpoint : (p : ℝ × ℝ) = annulusMap L hL (q.1, q.2) := by
    rw [← hE q]
    exact congrArg Subtype.val (E.apply_symm_apply p).symm
  have hdepth : depth L p = (q.2 : ℝ) := by
    rw [hpoint]
    exact depth_annulusMap hL
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr q.2.property) (by norm_num)) hwidth) q.1
  exact ⟨s, hs, by rw [hsq, hdepth]; exact hpoint⟩

end PLAnnularStrip
