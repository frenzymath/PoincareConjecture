import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
open Set

namespace AddCircle

variable {p : ℝ} [Fact (0 < p)]

theorem not_injective_of_continuous_real {f : AddCircle p → ℝ}
    (hf : Continuous f) : ¬ Function.Injective f := by
  let a : AddCircle p := (p / 2 : ℝ)
  have hp : 0 < p := Fact.out
  have ha : a ≠ 0 := by
    have hm : p / 2 ∈ Ico (0 : ℝ) p := ⟨by linarith, by linarith⟩
    have h := coe_eq_zero_iff_of_mem_Ico hm
    exact fun hz => (by linarith : p / 2 ≠ 0) (h.mp hz)
  have haa : a + a = 0 := by
    change (↑(p / 2) : AddCircle p) + ↑(p / 2) = 0
    rw [← coe_add, show p / 2 + p / 2 = p by ring, coe_period]
  have hshift : Continuous (fun x => f (x + a)) := hf.comp (continuous_id.add continuous_const)
  have hex : ∃ x, f x = f (x + a) := by
    rcases le_total (f 0) (f a) with h | h
    · exact intermediate_value_univ₂ hf hshift
        (a := 0) (b := a) (by simpa using h) (by simpa [haa] using h)
    · exact intermediate_value_univ₂ hf hshift
        (a := a) (b := 0) (by simpa [haa] using h) (by simpa using h)
  rintro hi
  obtain ⟨x, hx⟩ := hex
  exact ha (add_left_cancel (show x + a = x + 0 by simpa using (hi hx).symm))

theorem surjective_of_continuous_injective {f : AddCircle p → AddCircle p}
    (hf : Continuous f) (hi : Function.Injective f) : Function.Surjective f := by
  intro y
  by_contra hy
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y
  let J := openPartialHomeomorphCoe p a
  have htarget (x : AddCircle p) : f x ∈ J.target := by
    change f x ∈ ({(a : AddCircle p)}ᶜ : Set (AddCircle p))
    exact fun hx => hy ⟨x, hx⟩
  have hcont : Continuous (J.symm ∘ f) := J.continuousOn_symm.comp_continuous hf htarget
  apply not_injective_of_continuous_real hcont
  intro x z hxz
  apply hi
  exact (J.right_inv (htarget x)).symm.trans
    ((congrArg J hxz).trans (J.right_inv (htarget z)))

end AddCircle
