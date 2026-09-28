import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Real

open Set Filter
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X] [T1Space X] [LocallyConnectedSpace X]

theorem mem_interior_sublevel_component_or_eq_singleton_of_strict_extremum
    {f : X → ℝ} {O : Set X} (hO : IsOpen O) (hf : ContinuousOn f O)
    {p x : X} {b : ℝ} (hx : x ∈ connectedComponentIn (O ∩ f ⁻¹' Iic b) p)
    (hext : (∀ᶠ y in 𝓝 x, y ≠ x → f x < f y) ∨
      (∀ᶠ y in 𝓝 x, y ≠ x → f y < f x)) :
    x ∈ interior (connectedComponentIn (O ∩ f ⁻¹' Iic b) p) ∨
      connectedComponentIn (O ∩ f ⁻¹' Iic b) p = {x} := by
  have hxbase := connectedComponentIn_subset _ _ hx
  have hinterior (hbase : O ∩ f ⁻¹' Iic b ∈ 𝓝 x) :
      x ∈ interior (connectedComponentIn (O ∩ f ⁻¹' Iic b) p) := by
    rw [connectedComponentIn_eq hx]
    exact mem_interior_iff_mem_nhds.mpr (connectedComponentIn_mem_nhds hbase)
  by_cases hxb : f x < b
  · left
    apply hinterior
    filter_upwards [hO.mem_nhds hxbase.1,
      ((hf x hxbase.1).continuousAt (hO.mem_nhds hxbase.1)).eventually
        (eventually_lt_nhds hxb)] with y hyO hyf
    exact ⟨hyO, hyf.le⟩
  have hxb : f x = b := le_antisymm hxbase.2 (le_of_not_gt hxb)
  rcases hext with hmin | hmax
  · right
    obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hmin
    have hlocal : ∀ y ∈ connectedComponentIn (O ∩ f ⁻¹' Iic b) p, y ∈ U → y = x := by
      intro y hy hyU
      by_contra hyx
      have hlt := hUsub hyU hyx
      have hle : f y ≤ b := (connectedComponentIn_subset _ _ hy).2
      exact (not_lt_of_ge hle) (hxb ▸ hlt)
    apply subset_antisymm _ (singleton_subset_iff.mpr hx)
    intro y hy
    by_contra hyx
    have hyx' : y ≠ x := by simpa only [mem_singleton_iff] using hyx
    obtain ⟨z, _, hzx, hzU⟩ := isPreconnected_closed_iff.mp
      isPreconnected_connectedComponentIn {x} Uᶜ isClosed_singleton hU.isClosed_compl
      (fun z hz => by
        by_cases hzx : z = x
        · exact Or.inl (mem_singleton_iff.mpr hzx)
        · exact Or.inr (fun hzU => hzx (hlocal z hz hzU)))
      ⟨x, hx, mem_singleton x⟩ ⟨y, hy, fun hyU => hyx' (hlocal y hy hyU)⟩
    exact hzU (mem_singleton_iff.mp hzx ▸ hxU)
  · left
    apply hinterior
    filter_upwards [hO.mem_nhds hxbase.1, hmax] with y hyO hyf
    refine ⟨hyO, ?_⟩
    by_cases hyx : y = x
    · simpa only [hyx] using hxbase.2
    · exact (hyf hyx).le.trans hxbase.2

end Poincare.Topology
