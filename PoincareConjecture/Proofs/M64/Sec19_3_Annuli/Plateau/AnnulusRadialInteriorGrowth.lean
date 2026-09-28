import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MorreyGrowthPower

set_option autoImplicit false

noncomputable section

open Set

namespace PoincareConjecture

theorem m64Morrey_power_of_scaled_initial_bound
    {E : ℝ → ℝ} {R q K beta : ℝ} (hR : 0 < R) (hq : 0 < q)
    (hK : 0 ≤ K) (hbeta : 0 < beta) (hbetaq : beta ≤ -Real.log q)
    (hmono : MonotoneOn E (Ioc (0 : ℝ) R))
    (hpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 ≤ E r)
    (hbase : E R ≤ K * (4 * R) ^ beta)
    (hstep : ∀ r ∈ Ioc (0 : ℝ) R, E (r * Real.exp (-1)) ≤ q * E r)
    {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) R) :
    E r ≤ (K * (4 : ℝ) ^ beta / Real.exp (-beta)) * r ^ beta := by
  let q' := Real.exp (-beta)
  have hq' : 0 < q' := Real.exp_pos _
  have hq'1 : q' < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hbeta)
  have hqq' : q ≤ q' := by
    rw [← Real.exp_log hq]
    apply Real.exp_le_exp.mpr
    linarith
  have hstep' (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) R) : E (s * Real.exp (-1)) ≤ q' * E s :=
    (hstep s hs).trans (mul_le_mul_of_nonneg_right hqq' (hpos s hs))
  have hpow := m64Morrey_energy_le_power_of_contraction hR hq' hq'1
    (mul_nonneg hK (Real.rpow_nonneg (by positivity) _)) hmono hbase hstep' hr
  have hexp : -Real.log q' = beta := by simp [q']
  rw [hexp] at hpow
  refine hpow.trans_eq ?_
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hR.le]
  have hRpow : R ^ beta ≠ 0 := (Real.rpow_pos_of_pos hR _).ne'
  change K * ((4 : ℝ) ^ beta * R ^ beta) / (q' * R ^ beta) * r ^ beta = _
  field_simp
  simp [q']
  ring

end PoincareConjecture
