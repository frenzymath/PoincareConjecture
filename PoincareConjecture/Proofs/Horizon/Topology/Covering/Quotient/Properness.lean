import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set Topology

variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [Group G] [MulAction G E] {p : E → X}

namespace IsQuotientCoveringMap

theorem locallyFinite_graph [T2Space X] (hp : IsQuotientCoveringMap p G) :
    LocallyFinite (fun g : G => {z : E × E | g • z.1 = z.2}) := by
  let : ContinuousConstSMul G E := hp.toContinuousConstSMul
  rintro ⟨x, y⟩
  by_cases hxy : p y = p x
  · obtain ⟨g, rfl⟩ := hp.apply_eq_iff_mem_orbit.mp hxy
    obtain ⟨U, hxU, hU⟩ := hp.disjoint x
    refine ⟨U ×ˢ ((fun z : E => g⁻¹ • z) ⁻¹' U), ?_, ?_⟩
    · have hV : U ∈ 𝓝 (g⁻¹ • (g • x)) := by simpa using hxU
      exact prod_mem_nhds hxU
        ((continuous_const_smul g⁻¹).continuousAt.preimage_mem_nhds hV)
    · apply (finite_singleton g).subset
      rintro d ⟨⟨a, b⟩, hab, ha, hb⟩
      have hd : g⁻¹ * d = 1 := hU _ ⟨g⁻¹ • b, ⟨a, ha, by
        change (g⁻¹ * d) • a = g⁻¹ • b
        rw [mul_smul, hab]⟩, hb⟩
      exact (inv_mul_eq_one.mp hd).symm
  · obtain ⟨U, V, hU, hV, hxU, hyV, hdis⟩ := t2_separation (Ne.symm hxy)
    refine ⟨(p ⁻¹' U) ×ˢ (p ⁻¹' V),
      prod_mem_nhds (hp.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU))
        (hp.continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds hyV)), ?_⟩
    apply finite_empty.subset
    rintro d ⟨⟨a, b⟩, hab, ha, hb⟩
    change d • a = b at hab
    change p b ∈ V at hb
    exact (Set.disjoint_left.mp hdis ha (by
      simpa only [← hab, hp.map_smul] using hb)).elim

theorem properlyDiscontinuousSMul [T2Space X] (hp : IsQuotientCoveringMap p G) :
    ProperlyDiscontinuousSMul G E := by
  constructor
  intro K L hK hL
  have hfin := hp.locallyFinite_graph.finite_nonempty_inter_compact (hK.prod hL)
  apply hfin.subset
  rintro d ⟨y, ⟨x, hx, rfl⟩, hy⟩
  exact ⟨(x, d • x), rfl, hx, hy⟩

end IsQuotientCoveringMap
