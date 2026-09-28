import PoincareConjecture.Proofs.M47.SeedBlowupVolumeScales
import PoincareConjecture.Proofs.M47.SeedCylinderClock
import PoincareConjecture.Proofs.M33.GuardedCylinders









set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_seed_blowup_volume_test {F : SurgeryFlowData.{u}}
    {t Q tau rho B : ℝ} (hQ : 0 < Q) (hrho : 0 < rho)
    (htime : rho ^ 2 ≤ tau) (hbound : B ≤ rho⁻¹ ^ 2)
    (x : (F.slice t).carrier)
    (e : SurgeryFlowCylinder F (F.slice t) t Q (Icc (-tau) 0)
      ((F.metric t).ball x (rho / Real.sqrt Q)))
    (hbase : ∀ h y, y ∈ (F.metric t).ball x (rho / Real.sqrt Q) →
      HEq (e.forward 0 h y) y)
    (hcurv : ∀ s hs y, y ∈ (F.metric t).ball x (rho / Real.sqrt Q) →
      (F.connection (t + s / Q)).curvatureTensorNorm (e.forward s hs y) ≤ B * Q) :
    ∃ test : SurgeryFlowCylinder F (F.slice t) t 1
        (Icc (-(rho / Real.sqrt Q) ^ 2) 0)
        ((F.metric t).ball x (rho / Real.sqrt Q)),
      (∀ h y, y ∈ (F.metric t).ball x (rho / Real.sqrt Q) →
        HEq (test.forward 0 h y) y) ∧
      (∀ s hs y, y ∈ (F.metric t).ball x (rho / Real.sqrt Q) →
        (F.connection (t + s / 1)).curvatureTensorNorm (test.forward s hs y) ≤
          (rho / Real.sqrt Q)⁻¹ ^ 2) ∧
      (F.metric t).ball x (rho / Real.sqrt Q) ⊆ m33RegularRegion F t := by
  have hmem : MapsTo (fun s : ℝ => Q * s)
      (Icc (-(rho / Real.sqrt Q) ^ 2) 0) (Icc (-tau) 0) := by
    intro s hs
    have h := PoincareConjecture.M47.limitNoncollapse_physical_time_range hQ 0 rho hs
    constructor <;> dsimp only at h <;> simp only [zero_add, zero_sub] at h
    · exact (neg_le_neg htime).trans h.1
    · exact h.2
  have hmono : StrictMonoOn (fun s : ℝ => Q * s)
      (Icc (-(rho / Real.sqrt Q) ^ 2) 0) := fun _ _ _ _ h => mul_lt_mul_of_pos_left h hQ
  have hclock : ∀ s ∈ Icc (-(rho / Real.sqrt Q) ^ 2) 0,
      t + s / 1 = t + (Q * s) / Q := by
    intro s _
    simp [hQ.ne']
  let test := seedCylinderReclock e zero_lt_one ordConnected_Icc
    (fun s => Q * s) hmem hmono hclock
  have htest : ∀ h y, y ∈ (F.metric t).ball x (rho / Real.sqrt Q) →
      HEq (test.forward 0 h y) y := by
    intro h y hy
    have he := seedCylinderReclock_forward_heq e zero_lt_one ordConnected_Icc
      (fun s => Q * s) hmem hmono hclock 0 h y
    have hb : ∀ s (hs : s ∈ Icc (-tau) 0), s = 0 → HEq (e.forward s hs y) y := by
      intro s hs hz
      subst s
      exact hbase hs y hy
    exact he.trans (hb (Q * 0) (hmem h) (mul_zero Q))
  refine ⟨test, htest, ?_, test.terminal_ball_regular x
    (div_pos hrho (Real.sqrt_pos.mpr hQ)) htest⟩
  intro s hs y hy
  have h := seedCylinderReclock_curvature e zero_lt_one ordConnected_Icc
    (fun s => Q * s) hmem hmono hclock hcurv s hs y hy
  exact h.trans (by
    rw [← PoincareConjecture.M47.limitNoncollapse_physical_curvature_threshold hQ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbound hQ.le)

end PoincareConjecture.Proofs.M47
