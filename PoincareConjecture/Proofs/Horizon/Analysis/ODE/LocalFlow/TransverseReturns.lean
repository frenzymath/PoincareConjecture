import PoincareConjecture.Proofs.Horizon.Analysis.ODE.LocalFlow.FlowBox
import PoincareConjecture.Proofs.Horizon.Analysis.ODE.Uniqueness.Open
import Mathlib.Topology.MetricSpace.ProperSpace











noncomputable section

namespace Poincare.ODE.LocalFlow

open Set Filter Metric Bornology
open scoped ContDiff Topology

private theorem transverse_eq_of_flowBox_visit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → E} (hV : ContDiff ℝ ∞ V) {γ : ℝ → E}
    (hγ : ∀ t ≥ 0, HasDerivAt γ (V (γ t)) t)
    (e : OpenPartialHomeomorph (ℝ × ℝ) E)
    (he : ∀ s t, (s, t) ∈ e.source →
      HasDerivAt (fun r => e (s, r)) (V (e (s, t))) t)
    {ε : ℝ} (hε : 0 < ε)
    (hbox : Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source)
    {n s u : ℝ} (hn : 2 * ε < n) (hs : s ∈ Ioo (-ε) ε)
    (hu : u ∈ Ioo (-ε) ε) (hvisit : γ n = e (s, u)) :
    γ (n - u) = e (s, 0) := by
  let α : ℝ → E := fun t => γ (n + t - u)
  have hα : ∀ t ∈ Ioo (-ε) ε,
      α t ∈ (univ : Set E) ∧ HasDerivAt α (V (α t)) t := by
    intro t ht
    refine ⟨mem_univ _, ?_⟩
    have htime : 0 ≤ n + t - u := by linarith [ht.1, hu.2]
    simpa only [α, Function.comp_def, one_smul, id_eq] using
      (hγ (n + t - u) htime).scomp t (((hasDerivAt_id t).const_add n).sub_const u)
  have hη : ∀ t ∈ Ioo (-ε) ε,
      e (s, t) ∈ (univ : Set E) ∧
        HasDerivAt (fun r => e (s, r)) (V (e (s, t))) t :=
    fun t ht => ⟨mem_univ _, he s t (hbox ⟨hs, ht⟩)⟩
  have hinit : α u = e (s, u) := by simpa only [α, add_sub_cancel_right] using hvisit
  have heq := Poincare.ODE.eqOn_of_hasDerivAt isOpen_univ hV.contDiffOn
    isOpen_Ioo (convex_Ioo (-ε) ε).isPreconnected hα hη hu hinit
  simpa only [α, add_zero] using heq (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩)





theorem exists_flowBox_transverse_returns
    {V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hV : ContDiff ℝ ∞ V) (hne : ∀ p, V p ≠ 0)
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hγ : ∀ t ≥ 0, HasDerivAt γ (V (γ t)) t)
    (hbounded : IsBounded (γ '' Ici 0)) :
    ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2))) (ε : ℝ),
      0 < ε ∧ Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source ∧
      MapClusterPt (e (0, 0)) atTop γ ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ s t, (s, t) ∈ e.source →
        HasDerivAt (fun r => e (s, r)) (V (e (s, t))) t) ∧
      ∀ T : ℝ, ∃ t > T, ∃ s ∈ Ioo (-ε) ε,
        (s, 0) ∈ e.source ∧ γ t = e (s, 0) := by
  have hcompact : IsCompact (closure (γ '' Ici 0)) := hbounded.isCompact_closure
  have hmem : ∀ᶠ t : ℝ in atTop, γ t ∈ closure (γ '' Ici 0) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact subset_closure (mem_image_of_mem γ ht)
  obtain ⟨p, _, hp⟩ := hcompact.exists_mapClusterPt_of_frequently hmem.frequently
  obtain ⟨e, he0, hep, _, he, hei, hflow⟩ :=
    exists_smooth_planar_flowBox isOpen_univ hV.contDiffOn (mem_univ p) (hne p)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_source (0, 0) he0
  have hbox : Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source := by
    rintro ⟨s, u⟩ ⟨hs, hu⟩
    apply hball
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero,
      max_lt_iff]
    exact ⟨abs_lt.mpr hs, abs_lt.mpr hu⟩
  let O : Set (EuclideanSpace ℝ (Fin 2)) :=
    e.target ∩ e.symm ⁻¹' (Ioo (-ε) ε ×ˢ Ioo (-ε) ε)
  have hO : IsOpen O :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target (isOpen_Ioo.prod isOpen_Ioo)
  have hpO : p ∈ O := by
    have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
    rw [← hep]
    refine ⟨e.map_source he0, ?_⟩
    change e.symm (e (0, 0)) ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε
    rw [e.left_inv he0]
    exact ⟨hzero, hzero⟩
  refine ⟨e, ε, hε, hbox, hep.symm ▸ hp, he, hei, hflow, ?_⟩
  intro T
  have hlate : ∃ᶠ n : ℝ in atTop, γ n ∈ O :=
    (mapClusterPt_iff_frequently.mp hp) O (hO.mem_nhds hpO)
  obtain ⟨n, hnO, hn⟩ :=
    (hlate.and_eventually (eventually_gt_atTop (max T 0 + 3 * ε))).exists
  let s : ℝ := (e.symm (γ n)).1
  let u : ℝ := (e.symm (γ n)).2
  have hs : s ∈ Ioo (-ε) ε := hnO.2.1
  have hu : u ∈ Ioo (-ε) ε := hnO.2.2
  have hvisit : γ n = e (s, u) := (e.right_inv hnO.1).symm
  have hnε : 2 * ε < n := by linarith [le_max_right T 0]
  have hreturn : γ (n - u) = e (s, 0) :=
    transverse_eq_of_flowBox_visit hV hγ e hflow hε hbox hnε hs hu hvisit
  refine ⟨n - u, ?_, s, hs, hbox ⟨hs, ⟨by linarith, hε⟩⟩, hreturn⟩
  linarith [le_max_left T 0, hu.2]

end Poincare.ODE.LocalFlow
