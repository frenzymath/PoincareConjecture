import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp



set_option autoImplicit false

open Set

theorem Set.Finite.exists_pos_height_perturbation_parameter
    {V : Type*} {S : Set V} (hS : S.Finite) (h rho : V → ℝ)
    (hfixed : ∀ v ∈ S, rho v = 0 → h v ≠ 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta ∈ Ioo (0 : ℝ) epsilon, ∀ v ∈ S, h v + delta * rho v ≠ 0 := by
  let bad : Set ℝ := (fun v => -(h v) / rho v) '' S
  have hbad : bad.Finite := hS.image _
  obtain ⟨delta, hdelta, hnot⟩ := (Ioo_infinite hepsilon).exists_notMem_finite hbad
  refine ⟨delta, hdelta, ?_⟩
  intro v hv he
  by_cases hrho : rho v = 0
  · apply hfixed v hv hrho
    simpa only [hrho, mul_zero, add_zero] using he
  · apply hnot
    refine ⟨v, hv, ?_⟩
    apply (div_eq_iff hrho).mpr
    linarith
