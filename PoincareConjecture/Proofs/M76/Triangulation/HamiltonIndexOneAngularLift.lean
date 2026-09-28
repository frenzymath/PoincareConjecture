import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Tactic











set_option autoImplicit false

open Set unitInterval

namespace PoincareConjecture.M76.HamiltonIndexOne

section GeneralPeriod

variable {L : ℝ}

local notation "Q" => AddCircle L






theorem exists_marked_annulus_angular_lift_period (hL : 0 < L)
    (rho : C(I × Q, Q))
    (hzero : ∀ z : Q, rho (0, z) = z)
    (hone : ∀ z : Q, rho (1, z) = z) :
    ∃ (theta : C(I × ℝ, ℝ)) (m : ℤ),
      (∀ p : I × ℝ, (theta p : Q) = rho (p.1, (p.2 : Q))) ∧
      (∀ t : ℝ, theta (0, t) = t) ∧
      (∀ t : ℝ, theta (1, t) = t + L * (m : ℝ)) ∧
      (∀ (s : I) (t : ℝ), theta (s, t + L) = theta (s, t) + L) ∧
      ∀ t : ℝ, theta (1, t - L * (m : ℝ)) = t := by
  let : Fact (0 < L) := ⟨hL⟩
  let q : C(ℝ, Q) := ⟨fun t => (t : Q), AddCircle.continuous_mk' L⟩
  let H : C(I × ℝ, Q) :=
    ⟨fun p => rho (p.1, (p.2 : Q)),
      rho.continuous.comp (continuous_fst.prodMk (q.continuous.comp continuous_snd))⟩
  have hH0 (t : ℝ) : H (0, t) = ((ContinuousMap.id ℝ) t : Q) := hzero _
  let cov := AddCircle.isCoveringMap_coe L
  let theta := cov.liftHomotopy H (ContinuousMap.id ℝ) hH0
  have htheta (p : I × ℝ) : (theta p : Q) = rho (p.1, (p.2 : Q)) :=
    congrFun (cov.liftHomotopy_lifts H (ContinuousMap.id ℝ) hH0) p
  have htheta0 (t : ℝ) : theta (0, t) = t :=
    cov.liftHomotopy_zero H (ContinuousMap.id ℝ) hH0 t
  have hend (t : ℝ) : (theta (1, t) : Q) = (t : Q) :=
    (htheta (1, t)).trans (hone _)
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff L).mp
    (by simpa only [AddCircle.coe_zero] using hend 0)
  have hm' : theta (1, 0) = L * (m : ℝ) := by
    rw [zsmul_eq_mul] at hm
    simpa only [mul_comm] using hm.symm
  have htheta1 (t : ℝ) : theta (1, t) = t + L * (m : ℝ) := by
    have heq := cov.eq_of_comp_eq
      (theta.continuous.comp (continuous_const.prodMk continuous_id))
      (continuous_id.add continuous_const)
      (g₁ := fun u : ℝ => theta (1, u))
      (g₂ := fun u : ℝ => u + L * (m : ℝ))
      (by
        funext u
        change (theta (1, u) : Q) = ((u + L * (m : ℝ) : ℝ) : Q)
        rw [hend, AddCircle.coe_add, ← hm']
        simp only [hend, AddCircle.coe_zero, add_zero])
      0 (by simpa only [zero_add] using hm')
    exact congrFun heq t
  have hperiod (s : I) (t : ℝ) : theta (s, t + L) = theta (s, t) + L := by
    have heq := cov.eq_of_comp_eq
      (theta.continuous.comp (continuous_id.prodMk continuous_const))
      ((theta.continuous.comp (continuous_id.prodMk continuous_const)).add
        continuous_const)
      (g₁ := fun a : I => theta (a, t + L))
      (g₂ := fun a : I => theta (a, t) + L)
      (by
        funext a
        change (theta (a, t + L) : Q) = ((theta (a, t) + L : ℝ) : Q)
        simp only [AddCircle.coe_add_period, htheta])
      0 (by rw [htheta0, htheta0])
    exact congrFun heq s
  refine ⟨theta, m, htheta, htheta0, htheta1, hperiod, ?_⟩
  intro t
  rw [htheta1]
  ring

end GeneralPeriod



theorem exists_marked_annulus_angular_lift
    (rho : C(I × AddCircle (8 : ℝ), AddCircle (8 : ℝ)))
    (hzero : ∀ z : AddCircle (8 : ℝ), rho (0, z) = z)
    (hone : ∀ z : AddCircle (8 : ℝ), rho (1, z) = z) :
    ∃ (theta : C(I × ℝ, ℝ)) (m : ℤ),
      (∀ p : I × ℝ, (theta p : AddCircle (8 : ℝ)) =
        rho (p.1, (p.2 : AddCircle (8 : ℝ)))) ∧
      (∀ t : ℝ, theta (0, t) = t) ∧
      (∀ t : ℝ, theta (1, t) = t + 8 * (m : ℝ)) ∧
      (∀ (s : I) (t : ℝ), theta (s, t + 8) = theta (s, t) + 8) ∧
      ∀ t : ℝ, theta (1, t - 8 * (m : ℝ)) = t :=
  exists_marked_annulus_angular_lift_period (by norm_num) rho hzero hone

end PoincareConjecture.M76.HamiltonIndexOne
