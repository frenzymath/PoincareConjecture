import PoincareConjecture.Proofs.M25.Topology3D.Space3.CircleRadialChart











set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D




theorem sourceDisc_collar_mem_retained_iff
    {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph E2 X) (he : closedBall 0 1 ⊆ e.source)
    (Q : UnitCircle × ℝ → X) (sigma : ℝ) {delta r k : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hrdelta : 1 - r < delta) (hk : 0 < k)
    (hnear : ∀ x : E2, |‖x‖ - 1| < delta →
      x ∈ e.source ∧ e x = Q (circleDirection x, sigma * (k * (1 - ‖x‖))))
    (theta : UnitCircle) {s : ℝ} (hs : 0 ≤ s) (hsa : s ≤ k * (1 - r)) :
    Q (theta, sigma * s) ∈ e '' closedBall 0 r ↔ s = k * (1 - r) := by
  let rho := 1 - s / k
  have hrho : r ≤ rho := by
    have hdiv : s / k ≤ 1 - r := (div_le_iff₀ hk).mpr (by nlinarith)
    dsimp [rho]
    linarith
  have hrho1 : rho ≤ 1 := sub_le_self _ (div_nonneg hs hk.le)
  have hrho0 : 0 < rho := hr.trans_le hrho
  have hnorm : ‖rho • (theta : E2)‖ = rho := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrho0,
      norm_eq_of_mem_sphere, mul_one]
  have hwindow : |‖rho • (theta : E2)‖ - 1| < delta := by
    rw [hnorm, abs_of_nonpos (sub_nonpos.mpr hrho1)]
    linarith
  obtain ⟨hsource, hformula⟩ := hnear (rho • (theta : E2)) hwindow
  have htime : k * (1 - rho) = s := by
    dsimp [rho]
    field_simp [hk.ne']
    ring
  rw [hnorm, circleDirection_smul theta hrho0, htime] at hformula
  rw [← hformula, e.injOn.mem_image_iff
    (fun _ hx => he (closedBall_subset_closedBall hr1.le hx)) hsource,
    mem_closedBall_zero_iff, hnorm]
  constructor
  · intro hle
    have heq : rho = r := le_antisymm hle hrho
    rw [heq] at htime
    exact htime.symm
  · intro hsaeq
    dsimp [rho]
    rw [hsaeq, mul_div_cancel_left₀ _ hk.ne']
    linarith

end PoincareConjecture.M25.Topology3D
