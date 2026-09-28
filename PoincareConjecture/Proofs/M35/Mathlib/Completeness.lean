import Mathlib.Topology.EMetricSpace.Basic









set_option autoImplicit false

open Filter
open scoped ENNReal Topology



theorem EMetricSpace.completeSpace_of_topology_eq_edist_le
    {X : Type*} (d₀ d₁ : EMetricSpace X)
    (hcomplete : @CompleteSpace X d₀.toUniformSpace)
    (htop : d₀.toUniformSpace.toTopologicalSpace = d₁.toUniformSpace.toTopologicalSpace)
    {C : ℝ}
    (hbound : ∀ x y, d₀.edist x y ≤ ENNReal.ofReal C * d₁.edist x y) :
    @CompleteSpace X d₁.toUniformSpace := by
  let : EMetricSpace X := d₁
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  have hucauchy := EMetric.cauchySeq_iff.mp hu
  have hlimit : ∃ x, Tendsto u atTop (@nhds X d₀.toUniformSpace.toTopologicalSpace x) := by
    let : EMetricSpace X := d₀
    let : CompleteSpace X := hcomplete
    apply cauchySeq_tendsto_of_complete
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hucauchy (ε / ENNReal.ofReal C)
      (ENNReal.div_pos hε.ne' ENNReal.ofReal_ne_top)
    refine ⟨N, ?_⟩
    intro m hm k hk
    exact (hbound (u m) (u k)).trans_lt
      (ENNReal.mul_lt_of_lt_div' (hN m hm k hk))
  change ∃ x, Tendsto u atTop (@nhds X d₁.toUniformSpace.toTopologicalSpace x)
  rw [← htop]
  exact hlimit
