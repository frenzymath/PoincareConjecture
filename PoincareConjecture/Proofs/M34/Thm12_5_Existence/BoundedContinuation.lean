import PoincareConjecture.Proofs.M34.Thm12_5_Existence.TerminalRestart
import PoincareConjecture.Proofs.M34.Standard.JoinedFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

theorem partialFlow_extension_exists_of_curvature_bound
    (P : M34StandardCapPredecessors) {g0 : StandardInitialMetric}
    (E0 : StandardCapEstimate g0) (F : PartialStandardCapFlow g0)
    {B : ℝ} (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 F.lifetime, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B) :
    ∃ T : ℝ, Nonempty (PartialStandardCapFlowExtension F T) := by
  obtain ⟨L⟩ := partialFlowTerminalJets_nonempty P.curvature E0 F
    F.lifetime_pos le_rfl hB hfull
  let gS := L.metric P.curvature E0 F.lifetime_pos le_rfl hB hfull
  obtain ⟨τ, K, hτ, _hK, H, hinit, _hD, _hcomplete, hcurv⟩ :=
    L.forward_flow_exists P E0 F.lifetime_pos le_rfl hB hfull gS.euclideanLeviCivitaData
  let G := L.closedFlow P.curvature E0 F.lifetime_pos le_rfl hB hfull
  have hmatch : H.metric 0 = G.metric F.lifetime :=
    hinit.trans (L.closedMetric_terminal P.curvature E0 F.lifetime_pos le_rfl hB hfull).symm
  let J := FlowJoining.flow G H F.lifetime_pos hτ hmatch
  have hpair (t : ℝ) (ht : t < F.lifetime) :
      (⟨J.metric t, J.connection t⟩ :
        Σ g : RiemannianMetric 3 StandardCapSpace, LeviCivitaData g) =
      ⟨F.flow.metric t, F.flow.connection t⟩ := by
    change FlowJoining.metricConnection G H t = ⟨F.flow.metric t, F.flow.connection t⟩
    exact (FlowJoining.metricConnection_of_lt G H ht).trans
      (L.closedMetricConnection_of_lt P.curvature E0 F.lifetime_pos le_rfl hB hfull ht)
  have hG : ∀ t ∈ Icc 0 F.lifetime, ∀ x : StandardCapSpace,
      |(G.connection t).curvatureTensorNorm x| ≤ B := by
    intro t ht x
    rw [abs_of_nonneg (show 0 ≤ (G.connection t).curvatureTensorNorm x from Real.sqrt_nonneg _)]
    exact L.closedFlow_curvatureTensorNorm_le P.curvature E0
      F.lifetime_pos le_rfl hB hfull ht x
  have hbound : ∀ t ∈ Ico 0 (F.lifetime + τ), ∀ x : StandardCapSpace,
      |(J.connection t).curvatureTensorNorm x| ≤ max B K :=
    fun _ ht x => FlowJoining.flow_abs_curvature_le G H F.lifetime_pos hτ hmatch hG hcurv ht x
  refine ⟨F.lifetime + τ, ⟨{
    lifetime_gt := lt_add_of_pos_right F.lifetime hτ
    flow := J
    initial_metric := ?_
    initial_connection := ?_
    agrees_on_old_domain := ?_
    agrees_on_connection := ?_
    curvature_locally_bounded := ?_ }⟩⟩
  · exact (Sigma.mk.inj_iff.mp (hpair 0 F.lifetime_pos)).1.trans F.initial_metric
  · exact (Sigma.mk.inj_iff.mp (hpair 0 F.lifetime_pos)).2.trans F.initial_connection
  · exact fun _ ht => (Sigma.mk.inj_iff.mp (hpair _ ht.2)).1
  · exact fun _ ht => (Sigma.mk.inj_iff.mp (hpair _ ht.2)).2
  · intro T _hT hTend
    refine ⟨max B K, hB.le.trans (le_max_left _ _), ?_⟩
    exact fun t ht x => hbound t ⟨ht.1, ht.2.trans_lt hTend⟩ x

theorem maximalFlow_curvature_unbounded (P : M34StandardCapPredecessors)
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : MaximalStandardCapFlow g0) (B : ℝ) :
    ∃ t ∈ Ico 0 F.base.lifetime, ∃ x : StandardCapSpace,
      B < (F.connection t).curvatureTensorNorm x := by
  by_contra hnot
  push Not at hnot
  have hpos : 0 < max B 0 + 1 := by positivity
  obtain ⟨T, hE⟩ := partialFlow_extension_exists_of_curvature_bound P E0 F.base hpos
    (fun t ht x => (hnot t ht x).trans
      ((le_max_left B 0).trans (by linarith)))
  exact F.maximal T hE

theorem maximalFlow_curvature_unbounded_near_lifetime (P : M34StandardCapPredecessors)
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : MaximalStandardCapFlow g0) {t0 : ℝ} (ht0 : t0 ∈ Ico 0 F.base.lifetime)
    (B : ℝ) :
    ∃ t ∈ Ioo t0 F.base.lifetime, ∃ x : StandardCapSpace,
      B < (F.connection t).curvatureTensorNorm x := by
  obtain ⟨K, _hK, hbound⟩ := F.base.curvature_locally_bounded t0 ht0.1 ht0.2
  obtain ⟨t, ht, x, hbig⟩ := maximalFlow_curvature_unbounded P E0 F (max B K)
  have hlate : t0 < t := by
    by_contra hnt
    have hle := (le_abs_self _).trans (hbound t ⟨ht.1, not_lt.mp hnt⟩ x)
    exact (not_lt_of_ge (hle.trans (le_max_right B K))) hbig
  exact ⟨t, ⟨hlate, ht.2⟩, x, (le_max_left B K).trans_lt hbig⟩

end PoincareConjecture.M34
