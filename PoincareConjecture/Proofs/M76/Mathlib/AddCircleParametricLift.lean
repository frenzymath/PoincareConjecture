import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.CompactOpen

set_option autoImplicit false

open Set Topology

namespace AddCircle

variable {p : ℝ} [Fact (0 < p)]

theorem liftIco_zero_coe_apply_Icc {Z : Type*} {f : ℝ → Z}
    (hf : f 0 = f p) {x : ℝ} (hx : x ∈ Icc 0 p) :
    liftIco p 0 f (x : AddCircle p) = f x := by
  by_cases hxp : x < p
  · exact liftIco_zero_coe_apply ⟨hx.1, hxp⟩
  · have hxeq : x = p := le_antisymm hx.2 (not_lt.mp hxp)
    rw [hxeq, coe_period]
    have hzero := liftIco_zero_coe_apply (f := f)
      (show (0 : ℝ) ∈ Ico 0 p from ⟨le_rfl, Fact.out⟩)
    have hz : liftIco p 0 f (0 : AddCircle p) = f 0 := by
      simpa only [coe_zero] using hzero
    exact hz.trans hf

theorem isQuotientMap_coe_Icc :
    IsQuotientMap (fun x : Icc (0 : ℝ) p => ((x : ℝ) : AddCircle p)) := by
  let q : Icc (0 : ℝ) p → AddCircle p := fun x => ((x : ℝ) : AddCircle p)
  have hc : Continuous q := (AddCircle.continuous_mk' p).comp continuous_subtype_val
  have hs : Function.Surjective q := by
    intro z
    have hcover : ((↑) : ℝ → AddCircle p) '' Icc 0 p = univ := by
      simpa only [zero_add] using coe_image_Icc_eq p 0
    have hz : z ∈ ((↑) : ℝ → AddCircle p) '' Icc 0 p := by
      rw [hcover]
      exact mem_univ z
    obtain ⟨x, hx, he⟩ := hz
    exact ⟨⟨x, hx⟩, he⟩
  exact hc.isClosedMap.isQuotientMap hc hs

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
  [LocallyCompactSpace Y]

theorem continuous_parametric_liftIco (f : ℝ × Y → Z)
    (hf : Continuous (fun q : Icc (0 : ℝ) p × Y => f (q.1, q.2)))
    (hend : ∀ y, f (0, y) = f (p, y)) :
    Continuous (fun q : AddCircle p × Y => liftIco p 0 (fun s => f (s, q.2)) q.1) := by
  apply isQuotientMap_coe_Icc.continuous_lift_prod_left
  apply hf.congr
  intro q
  exact (liftIco_zero_coe_apply_Icc (f := fun s => f (s, q.2))
    (hend q.2) q.1.property).symm

end AddCircle
