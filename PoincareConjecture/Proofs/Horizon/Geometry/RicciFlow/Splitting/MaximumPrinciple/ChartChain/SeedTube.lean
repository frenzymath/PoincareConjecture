import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.ChartChain.Geometry

noncomputable section
open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple.ChartChain

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]

theorem exists_initial_ball_seed {D : Set M} (α : M)
    (hchart : D ⊆ (chartAt H α).source) {v : M → ℝ}
    (hv : ContinuousOn v D) {p : M} (hp : p ∈ interior D) (hpos : 0 < v p) :
    ∃ ε rho : ℝ, 0 < ε ∧ 0 < rho ∧
      ∀ x ∈ D, ‖extChartAt I α x - extChartAt I α p‖ < rho → ε ≤ v x := by
  have hps : p ∈ (extChartAt I α).source := by
    simpa only [extChartAt_source] using hchart (interior_subset hp)
  have hpt := (extChartAt I α).map_source hps
  have hvc : ContinuousAt v p :=
    (hv p (interior_subset hp)).continuousAt (mem_interior_iff_mem_nhds.mp hp)
  have hsymm : ContinuousAt (extChartAt I α).symm (extChartAt I α p) :=
    ((continuousOn_extChartAt_symm α) _ hpt).continuousAt
      (extChartAt_target_mem_nhds' hpt)
  have hc : ContinuousAt (v ∘ (extChartAt I α).symm) (extChartAt I α p) := by
    have hv' : ContinuousAt v ((extChartAt I α).symm (extChartAt I α p)) := by
      simpa only [(extChartAt I α).left_inv hps] using hvc
    exact hv'.comp hsymm
  have hev : ∀ᶠ y in 𝓝 (extChartAt I α p), v p / 2 < v ((extChartAt I α).symm y) :=
    hc.eventually (lt_mem_nhds (by
      simpa only [Function.comp_apply, (extChartAt I α).left_inv hps] using
        (show v p / 2 < v p by linarith)))
  obtain ⟨rho, hrho, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨v p / 2, rho, half_pos hpos, hrho, ?_⟩
  intro x hx hdist
  have hxs : x ∈ (extChartAt I α).source := by
    simpa only [extChartAt_source] using hchart hx
  have h := hball (show dist (extChartAt I α x) (extChartAt I α p) < rho by
    simpa only [dist_eq_norm] using hdist)
  simpa only [(extChartAt I α).left_inv hxs] using h.le

omit [I.Boundaryless] in

theorem exists_lateral_clearance {D : Set M} (hD : IsCompact D) (α : M)
    (hchart : D ⊆ (chartAt H α).source) {a b : ℝ}
    {gamma : ℝ → E} (hg : Continuous gamma)
    (hpath : ∀ t ∈ Icc a b, ∃ x ∈ interior D, extChartAt I α x = gamma t) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ x ∈ D, x ∉ interior D → ∀ t ∈ Icc a b,
      rho ≤ ‖extChartAt I α x - gamma t‖ := by
  let S := (D \ interior D) ×ˢ Icc a b
  let F := fun z : M × ℝ => ‖extChartAt I α z.1 - gamma z.2‖
  have hS : IsCompact S := (hD.diff isOpen_interior).prod isCompact_Icc
  have hFc : ContinuousOn F S := by
    apply ContinuousOn.norm
    apply ContinuousOn.sub
    · exact (continuousOn_extChartAt α).comp continuous_fst.continuousOn
        (fun z hz => by simpa only [extChartAt_source] using hchart hz.1.1)
    · exact (hg.comp continuous_snd).continuousOn
  obtain ⟨rho, hrho, hbound⟩ := hS.exists_forall_le' hFc (a := 0) (by
    intro z hz
    apply norm_pos_iff.mpr
    intro heq
    obtain ⟨x, hx, hxt⟩ := hpath z.2 hz.2
    have hzchart : z.1 ∈ (extChartAt I α).source := by
      simpa only [extChartAt_source] using hchart hz.1.1
    have hxchart : x ∈ (extChartAt I α).source := by
      simpa only [extChartAt_source] using hchart (interior_subset hx)
    have heqx : z.1 = x := (extChartAt I α).injOn hzchart hxchart
      ((sub_eq_zero.mp heq).trans hxt.symm)
    exact hz.1.2 (heqx ▸ hx))
  exact ⟨rho, hrho, fun x hx hn t ht => hbound (x, t) ⟨⟨hx, hn⟩, ht⟩⟩

end PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple.ChartChain
