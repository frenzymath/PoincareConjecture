import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MorreyGrowthForced












set_option autoImplicit false

noncomputable section

open Set

namespace PoincareConjecture



theorem m64Morrey_exists_uniform_power_of_forced_contraction
    {rho q D0 D : ℝ} (hrho : 0 < rho) (hq : 0 < q) (hq1 : q < 1)
    (hD0 : 0 ≤ D0) (hD : 0 ≤ D) :
    ∃ beta : ℝ, 0 < beta ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ E : ℝ → ℝ, MonotoneOn E (Ioc 0 rho) →
        (∀ r ∈ Ioc (0 : ℝ) rho, 0 ≤ E r) → E rho ≤ D0 →
        (∀ r ∈ Ioc 0 rho, E (r * Real.exp (-1)) ≤ q * E r + D * r ^ 2) →
        ∀ r ∈ Ioc (0 : ℝ) rho, E r ≤ K * r ^ beta := by
  let a2 := (Real.exp (-1)) ^ 2
  let q' := (max q a2 + 1) / 2
  have ha2 : 0 ≤ a2 := sq_nonneg _
  have ha2lt : a2 < 1 := by
    have ha1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    simpa only [a2, one_pow] using
      (sq_lt_sq₀ (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 1)).mpr ha1
  have hmax : max q a2 < 1 := max_lt hq1 ha2lt
  have hq'pos : 0 < q' := by dsimp [q']; positivity
  have hq'lt : q' < 1 := by dsimp [q']; linarith
  have hqle : q ≤ q' := by dsimp [q']; linarith [le_max_left q a2]
  have ha2lt' : a2 < q' := by dsimp [q']; linarith [le_max_right q a2]
  have hden : 0 < q' - a2 := sub_pos.mpr ha2lt'
  let T := D / (q' - a2)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hcoeff : D + T * a2 = q' * T := by
    dsimp [T]
    field_simp
    ring
  obtain ⟨beta, hbeta, K, hK, hpower⟩ := m64Morrey_exists_uniform_power_of_contraction
    hrho hq'pos hq'lt (add_nonneg hD0 (mul_nonneg hT (sq_nonneg rho)))
  refine ⟨beta, hbeta, K, hK, ?_⟩
  intro E hmono hpos hbase hstep r hr
  let F := fun x => E x + T * x ^ 2
  have hFmono : MonotoneOn F (Ioc 0 rho) := by
    intro x hx y hy hxy
    exact add_le_add (hmono hx hy hxy)
      (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hx.1.le hy.1.le).mpr hxy) hT)
  have hFbase : F rho ≤ D0 + T * rho ^ 2 := add_le_add hbase le_rfl
  have hFstep : ∀ x ∈ Ioc (0 : ℝ) rho,
      F (x * Real.exp (-1)) ≤ q' * F x := by
    intro x hx
    have hs := hstep x hx
    have hqE := mul_le_mul_of_nonneg_right hqle (hpos x hx)
    have hcoeff' := congrArg (fun y => y * x ^ 2) hcoeff
    dsimp only [F]
    dsimp only [a2] at hcoeff'
    nlinarith
  exact (le_add_of_nonneg_right (mul_nonneg hT (sq_nonneg r))).trans
    (hpower F hFmono hFbase hFstep r hr)

end PoincareConjecture
