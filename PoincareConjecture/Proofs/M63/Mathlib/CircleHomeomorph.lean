import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

namespace AddCircle

theorem exists_homeomorph_of_strictMono {p : ℝ} (hp : 0 < p) {f : ℝ → ℝ}
    (hf : Continuous f) (hmono : StrictMono f) (hshift : ∀ x, f (x + p) = f x + p) :
    ∃ e : AddCircle p ≃ₜ AddCircle p, ∀ x : ℝ, e (x : AddCircle p) = (f x : AddCircle p) := by
  have : Fact (0 < p) := ⟨hp⟩
  have hperiod : Function.Periodic (fun x => (f x : AddCircle p)) p := by
    intro x
    change (f (x + p) : AddCircle p) = (f x : AddCircle p)
    rw [hshift, coe_add_period]
  let g : AddCircle p → AddCircle p := hperiod.lift
  have hg : Continuous g :=
    ((AddCircle.continuous_mk' p).comp hf).quotient_liftOn' _
  have hend : f p = f 0 + p := by simpa only [zero_add] using hshift 0
  have hmap {x : ℝ} (hx : x ∈ Set.Ico 0 (0 + p)) :
      f x ∈ Set.Ico (f 0) (f 0 + p) := by
    refine ⟨hmono.monotone hx.1, ?_⟩
    rw [← hend]
    exact hmono (by simpa only [zero_add] using hx.2)
  have hinj : Function.Injective g := by
    intro x y hxy
    apply (equivIco p 0).injective
    apply Subtype.ext
    apply hmono.injective
    apply (coe_eq_coe_iff_of_mem_Ico (hmap (equivIco p 0 x).property)
      (hmap (equivIco p 0 y).property)).mp
    change g ((equivIco p 0 x : ℝ) : AddCircle p) =
      g ((equivIco p 0 y : ℝ) : AddCircle p)
    simpa only [coe_equivIco] using hxy
  have hsurj : Function.Surjective g := by
    intro y
    let z := equivIco p (f 0) y
    have hz : (z : ℝ) ∈ Set.Icc (f 0) (f p) := by
      rw [hend]
      exact ⟨z.property.1, z.property.2.le⟩
    obtain ⟨x, _, hx⟩ := intermediate_value_Icc hp.le hf.continuousOn hz
    refine ⟨(x : AddCircle p), ?_⟩
    change (f x : AddCircle p) = y
    rw [hx]
    exact coe_equivIco
  let e : AddCircle p ≃ AddCircle p := Equiv.ofBijective g ⟨hinj, hsurj⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := e) hg, fun _ => rfl⟩

end AddCircle
