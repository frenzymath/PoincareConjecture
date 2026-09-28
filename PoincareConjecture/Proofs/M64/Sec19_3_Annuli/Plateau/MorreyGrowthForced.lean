import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MorreyGrowthPower












set_option autoImplicit false

noncomputable section

open Set

namespace PoincareConjecture



theorem m64Morrey_energy_le_power_of_forced_contraction
    {E : ℝ → ℝ} {rho q D0 D : ℝ} (hrho : 0 < rho) (hq : 0 < q) (hq1 : q < 1)
    (hD0 : 0 ≤ D0) (hD : 0 ≤ D) (hmono : MonotoneOn E (Ioc 0 rho))
    (hE_nonneg : ∀ r ∈ Ioc (0 : ℝ) rho, 0 ≤ E r) (hbase : E rho ≤ D0)
    (hstep : ∀ r ∈ Ioc 0 rho,
      E (r * Real.exp (-1)) ≤ q * E r + D * r ^ 2)
    : ∃ beta : ℝ, 0 < beta ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ r ∈ Ioc (0 : ℝ) rho, E r ≤ K * r ^ beta := by
  let a := Real.exp (-1)
  let a2 := a ^ 2
  let q' := (max q a2 + 1) / 2
  have ha : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have ha2 : 0 ≤ a2 := sq_nonneg _
  have ha2lt : a2 < 1 := by
    dsimp [a2]
    simpa using (sq_lt_sq₀ (by positivity : 0 ≤ a) (by norm_num : (0 : ℝ) ≤ 1)).mpr ha1
  have hq'pos : 0 < q' := by dsimp [q']; positivity
  have hq'lt : q' < 1 := by
    dsimp [q']
    have hm : max q a2 < 1 := max_lt hq1 ha2lt
    linarith
  have hqle : q ≤ q' := by dsimp [q']; linarith [le_max_left q a2]
  have ha2le : a2 ≤ q' := by dsimp [q']; linarith [le_max_right q a2]
  have hmax : max q a2 < 1 := max_lt hq1 ha2lt
  have ha2lt' : a2 < q' := by dsimp [q']; linarith [le_max_right q a2]
  have hden : 0 < q' - a2 := sub_pos.mpr ha2lt'
  let T := D / (q' - a2)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let F := fun x => E x + T * x ^ 2
  have hFmono : MonotoneOn F (Ioc 0 rho) := by
    intro x hx y hy hxy
    dsimp [F]
    exact add_le_add (hmono hx hy hxy)
      (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hx.1.le hy.1.le).mpr hxy) hT)
  have hFnonneg : ∀ x ∈ Ioc (0 : ℝ) rho, 0 ≤ F x := by
    intro x hx
    exact add_nonneg (hE_nonneg x hx) (mul_nonneg hT (sq_nonneg x))
  have hFbase : F rho ≤ D0 + T * rho ^ 2 := by
    dsimp [F]
    exact add_le_add hbase le_rfl
  have hFstep : ∀ x ∈ Ioc (0 : ℝ) rho, F (x * a) ≤ q' * F x := by
    intro x hx
    have hs := hstep x hx
    have hqE := mul_le_mul_of_nonneg_right (hqle) (hE_nonneg x hx)
    have hcoeff : D + T * a2 = q' * T := by
      dsimp [T]
      field_simp
      ring
    dsimp [F, a, a2] at hs ⊢
    rw [show (x * Real.exp (-1)) ^ 2 = x ^ 2 * (Real.exp (-1)) ^ 2 by ring]
    nlinarith [hcoeff, hqE]
  have hFbound : ∀ r ∈ Ioc (0 : ℝ) rho,
      F r ≤ (D0 + T * rho ^ 2) / (q' * rho ^ (-Real.log q')) * r ^ (-Real.log q') := by
    intro r hr
    exact m64Morrey_energy_le_power_of_contraction hrho hq'pos hq'lt
      (add_nonneg hD0 (mul_nonneg hT (sq_nonneg rho))) hFmono hFbase hFstep hr
  refine ⟨-Real.log q', neg_pos.mpr (Real.log_neg hq'pos hq'lt),
    (D0 + T * rho ^ 2) / (q' * rho ^ (-Real.log q')),
    by positivity, ?_⟩
  intro r hr
  exact (le_add_of_nonneg_right (mul_nonneg hT (sq_nonneg r))).trans (hFbound r hr)

end PoincareConjecture
