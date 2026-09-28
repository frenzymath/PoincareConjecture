import PoincareConjecture.Proofs.M47.TerminalCurvatureMovingJetBounds










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalCurvature_exists_bounded_pullback_error_constant
    (m : ℕ) {D : ℝ} (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E → E) (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E),
      ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ B (f x) →
      (∀ j ≤ m + 1, ‖iteratedFDeriv ℝ j f x‖ ≤ D) →
      ∀ rho : ℝ, 0 ≤ rho →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j B (f x)‖ ≤ rho) →
      ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun y =>
        (B (f y)).bilinearComp (fderiv ℝ f y) (fderiv ℝ f y)) x‖ ≤ C * rho := by
  classical
  choose C hC hbound using fun j : Fin (m + 1) =>
    terminalCurvature_exists_moving_pullback_jet_bound j hD
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), ?_⟩
  intro f B x hf hB hfjet rho hrho hBjet j hj
  let i : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  exact (hbound i f B x hf hB (fun l hl => hfjet l (by omega)) rho hrho
    (fun l hl => hBjet l (hl.trans hj))).trans
      (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun l _ => hC l) (Finset.mem_univ i)) hrho)




theorem terminalCurvature_eventually_bounded_moving_pullback
    {ι : Type*} (m : ℕ) {D : ℝ} (hD : 1 ≤ D)
    {K : Set E} {B : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ}
    {f : ℕ → ι → E → E} {Z : ℕ → Set ι}
    (hf : ∀ k z, z ∈ Z k → ContDiffAt ℝ ∞ (f k z) 0)
    (hB : ∀ k z, z ∈ Z k → ContDiffAt ℝ ∞ (B k) (f k z 0))
    (hcenter : ∀ k z, z ∈ Z k → f k z 0 ∈ K)
    (hfjet : ∀ k z, z ∈ Z k → ∀ j ≤ m + 1,
      ‖iteratedFDeriv ℝ j (f k z) 0‖ ≤ D)
    (hBjet : ∀ j ≤ m, TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ j (B k)) (fun _ => 0) atTop K)
    {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ k in atTop, ∀ z ∈ Z k, ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (fun y =>
        (B k (f k z y)).bilinearComp (fderiv ℝ (f k z) y)
          (fderiv ℝ (f k z) y)) 0‖ ≤ rho := by
  obtain ⟨C, hC, hbound⟩ := terminalCurvature_exists_bounded_pullback_error_constant m hD
  let delta := rho / (C + 1)
  have hdelta : 0 < delta := div_pos hrho (by positivity)
  have hsmall : C * delta ≤ rho := by
    have heq : (C + 1) * delta = rho := by dsimp only [delta]; field_simp
    nlinarith
  have hevent : ∀ᶠ k in atTop, ∀ j : Fin (m + 1), ∀ x ∈ K,
      ‖iteratedFDeriv ℝ (j : ℕ) (B k) x‖ ≤ delta := by
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp
      (hBjet j (Nat.le_of_lt_succ j.isLt))) delta hdelta] with k hk x hx
    simpa only [dist_zero_right, dist_zero_left] using (hk x hx).le
  filter_upwards [hevent] with k hk z hz j hj
  apply (hbound (f k z) (B k) 0 (hf k z hz) (hB k z hz) (hfjet k z hz)
    delta hdelta.le (fun l hl => hk ⟨l, Nat.lt_succ_of_le hl⟩ _ (hcenter k z hz))
    j hj).trans hsmall

end PoincareConjecture.M47
