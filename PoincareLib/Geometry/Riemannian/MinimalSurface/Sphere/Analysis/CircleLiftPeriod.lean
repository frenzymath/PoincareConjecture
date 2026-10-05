import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The period of a lifted circle homeomorphism

Morgan-Tian Definition 18.17, printed p. 430, angular boundary
regularization. An injective map of the circle with a continuous strictly
monotone real lift advances one period exactly; a decreasing lift reverses
it. The proof uses interval injectivity of the angular exponential and
the intermediate value theorem.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M60

/-- A strictly increasing continuous lift of an injective circle map
advances exactly one angular period. Source: MT Definition 18.17,
p. 430, boundary-parameter derivation. -/
theorem circle_lift_add_two_pi_of_strictMono {e : Circle → Circle}
    (he : Function.Injective e) {H : ℝ → ℝ} (hcont : Continuous H) (hmono : StrictMono H)
    (hlift : ∀ t, Circle.exp (H t) = e (Circle.exp t)) (t : ℝ) :
    H (t + 2 * Real.pi) = H t + 2 * Real.pi := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hinc : H t < H (t + 2 * Real.pi) := hmono (by linarith)
  have heq : Circle.exp (H (t + 2 * Real.pi)) = Circle.exp (H t) := by
    rw [hlift, Circle.exp_add_two_pi, hlift]
  have hle : H t + 2 * Real.pi ≤ H (t + 2 * Real.pi) := by
    by_contra! hlt
    have hinj := Circle.exp_injOn_Ico (a := H t) (b := H t + 2 * Real.pi)
      (by linarith)
    have hequal := hinj ⟨hinc.le, hlt⟩ ⟨le_rfl, by linarith⟩ heq
    exact hinc.ne' hequal
  apply le_antisymm _ hle
  by_contra! hlt
  obtain ⟨s, hs, hval⟩ := intermediate_value_Icc (a := t) (b := t + 2 * Real.pi)
    (by linarith) hcont.continuousOn (show H t + 2 * Real.pi ∈
      Icc (H t) (H (t + 2 * Real.pi)) from ⟨by linarith, hlt.le⟩)
  have hslt : s < t + 2 * Real.pi := hmono.lt_iff_lt.mp (hval ▸ hlt)
  have hexp : Circle.exp s = Circle.exp t := he (by
    rw [← hlift, ← hlift, hval, Circle.exp_add_two_pi])
  have hst := Circle.exp_injOn_Ico (a := t) (b := t + 2 * Real.pi)
    (by linarith) ⟨hs.1, hslt⟩ ⟨le_rfl, by linarith⟩ hexp
  rw [hst] at hval
  linarith

/-- A strictly decreasing continuous lift of an injective circle map
reverses one angular period. Source: MT Definition 18.17, p. 430,
boundary-parameter derivation. -/
theorem circle_lift_add_two_pi_of_strictAnti {e : Circle → Circle}
    (he : Function.Injective e) {H : ℝ → ℝ} (hcont : Continuous H) (hanti : StrictAnti H)
    (hlift : ∀ t, Circle.exp (H t) = e (Circle.exp t)) (t : ℝ) :
    H (t + 2 * Real.pi) = H t - 2 * Real.pi := by
  have hmono : StrictMono (fun x => -H x) := fun x y hxy => neg_lt_neg (hanti hxy)
  have hinj : Function.Injective (fun z => (e z)⁻¹) := inv_injective.comp he
  have hnew : ∀ x, Circle.exp (-H x) = (e (Circle.exp x))⁻¹ := by
    intro x
    rw [Circle.exp_neg, hlift]
  have hperiod := circle_lift_add_two_pi_of_strictMono hinj hcont.neg hmono hnew t
  simp only [Pi.neg_apply] at hperiod
  linarith

end PoincareMT.M60
