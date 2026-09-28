import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.TerminalCompleteness
import PoincareConjecture.Statements.Ch05.Compactness
import PoincareConjecture.Definitions.Ch11.BlowupLimits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space

noncomputable def retainedClosedBlowupLimit
    {T tau B : ℝ} (htau : 0 < tau) (htauT : tau < T)
    {S : PointedFlowSequence 3 (-T / 2) (T / 2)}
    (G : PointedGeometricConvergence S)
    (Fsrc : ∀ k, RicciFlow 3 (S.carrier k).carrier (Icc (-T) 0))
    (F : RicciFlow 3 G.limitCarrier.carrier (Icc (-tau) 0))
    (hpast : ∀ t ∈ Ico (-tau) 0,
      F.metric t = G.limitFlow.flow.metric (t + T / 2))
    (hcomplete : ∀ s ∈ Ioo (-T / 2) (T / 2),
      G.limitCarrier.metricComplete (G.limitFlow.metricAt s))
    (hcurv : ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc (-tau) 0,
      ∀ x : (S.carrier k).carrier,
        ((Fsrc k).connection t).curvatureTensorNorm x ≤ B)
    (hnormalized : ∀ᶠ k : ℕ in atTop,
      ((Fsrc k).connection 0).scalarCurvature (S.flow k).base = 1)
    (hreadout : ∀ t ∈ Icc (-tau) 0, ∀ x : G.limitCarrier.carrier,
      Tendsto (fun k => ((Fsrc (G.subsequence k)).connection t).scalarCurvature
        (((G.embedding k).toFun (0, x)).2)) atTop
        (𝓝 ((F.connection t).scalarCurvature x)) ∧
      Tendsto (fun k => ((Fsrc (G.subsequence k)).connection t).curvatureTensorNorm
        (((G.embedding k).toFun (0, x)).2)) atTop
        (𝓝 ((F.connection t).curvatureTensorNorm x)) ∧
      (F.connection t).NonnegativeCurvatureOperator x) :
    BlowupLimitFlow.{0} (Icc (-tau) 0) := by
  let K : ℝ := max B 0
  have hK : 0 ≤ K := le_max_right B 0
  have hbound (t : ℝ) (ht : t ∈ Icc (-tau) 0) (x : G.limitCarrier.carrier) :
      (F.connection t).curvatureTensorNorm x ≤ K := by
    apply le_trans _ (le_max_left B 0)
    apply le_of_tendsto (hreadout t ht x).2.1
    filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually hcurv] with k hk
    exact hk t ht (((G.embedding k).toFun (0, x)).2)
  have hzero : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨by linarith, le_rfl⟩
  have hbase (k : ℕ) : ((G.embedding k).toFun (0, G.limitFlow.base)).2 =
      (S.flow (G.subsequence k)).base := congrArg Prod.snd (G.base_preserving k)
  have hone : Tendsto
      (fun k => ((Fsrc (G.subsequence k)).connection 0).scalarCurvature
        (((G.embedding k).toFun (0, G.limitFlow.base)).2)) atTop (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually hnormalized] with k hk
    rw [hbase]
    exact hk.symm
  have hnormalizedLimit : (F.connection 0).scalarCurvature G.limitFlow.base = 1 :=
    tendsto_nhds_unique (hreadout 0 hzero G.limitFlow.base).1 hone
  have hpastComplete (t : ℝ) (ht : t ∈ Ico (-tau) 0) :
      G.limitCarrier.metricComplete (F.metric t) := by
    rw [hpast t ht]
    exact hcomplete (t + T / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hterminal : G.limitCarrier.metricComplete (F.metric 0) :=
    metricComplete_terminal_of_closed_slab_curvature_bound G.limitCarrier F G.limitFlow.base
      (show -tau ≤ 0 by linarith) (Subset.refl _)
      (hpastComplete (-tau) ⟨le_rfl, by linarith⟩)
      (fun _ _ => ⟨K, hK, fun t ht x _ => hbound t ht x⟩)
  exact {
    carrier := G.limitCarrier
    connectedSpace := connectedSpace_iff_univ.mpr G.limitCarrier.connected
    base := G.limitFlow.base
    flow := F
    zero_mem := hzero
    scalar_normalized := hnormalizedLimit
    complete := by
      intro t ht
      by_cases ht0 : t = 0
      · subst t
        exact hterminal
      · exact hpastComplete t ⟨ht.1, lt_of_le_of_ne ht.2 ht0⟩
    nonnegative_curvature_operator := fun t ht x => (hreadout t ht x).2.2
    curvature_locally_bounded_in_time := by
      intro I _hI hIJ
      refine ⟨K, hK, fun t ht x => ?_⟩
      rw [abs_of_nonneg (show 0 ≤ (F.connection t).curvatureTensorNorm x from
        Real.sqrt_nonneg _)]
      exact hbound t (hIJ ht) x }

end PoincareConjecture.M30
