import PoincareConjecture.Proofs.M30.Thm11_8.CofinalHorizonConvergence
import PoincareConjecture.Proofs.M30.Thm11_8.UniformTerminalScalar
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteSourcePrefixControl
import PoincareConjecture.Proofs.M30.Thm11_8.HorizonContinuation
import PoincareConjecture.Proofs.M30.Thm11_8.SeedFiniteLongConvergence
import PoincareConjecture.Statements.M30Providers











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

private theorem harnack_bound_on_prefix
    {Q t U T s : ℝ} (hQ : 0 ≤ Q) (ht : 0 ≤ t)
    (htU : t < U) (hUT : U ≤ T) (hs : -t ≤ s) :
    Q * T / (s + T) ≤ Q * U / (U - t) := by
  have hU : 0 < U := ht.trans_lt htU
  have hden : 0 < s + T := by linarith
  apply (div_le_div_iff₀ hden (sub_pos.mpr htU)).mpr
  have hfirst : 0 ≤ Q * U * (s + t) :=
    mul_nonneg (mul_nonneg hQ hU.le) (by linarith)
  have hsecond : 0 ≤ Q * t * (T - U) :=
    mul_nonneg (mul_nonneg hQ ht) (sub_nonneg.mpr hUT)
  nlinarith only [hfirst, hsecond]




theorem exists_backward_convergence_of_cofinal_finite_limits
    (P : M30ControlledBlowupPredecessors.{u})
    {S : GeneralizedBlowupSequence.{u}} {T0 Tstar : ℝ≥0∞}
    {epsilon C kappa r0 mu : ℝ}
    (H : M30LongBlowupControls S epsilon C kappa r0 mu T0)
    (Hshort : ShortControlledBlowupHypotheses S kappa r0)
    (hbound : GeneralizedBlowupBoundedDistance S)
    (hstar : 0 < Tstar) (hstarT0 : Tstar ≤ T0)
    (hlimits : ∀ r : ℝ, 0 < r → ENNReal.ofReal r < Tstar →
      ∃ T : ℝ, r < T ∧ ENNReal.ofReal T < Tstar ∧
        Nonempty (GeneralizedBlowupConvergence S (Ioc (-T) 0))) :
    Nonempty (GeneralizedBlowupConvergence S (blowupBackwardInterval Tstar)) := by
  obtain ⟨T, hTmono, hT, hcofinal, _hcompactTime⟩ :=
    exists_strictMono_backward_time_exhaustion hstar
  let Q : ℝ := 9 * Hshort.curvature_bound
  have hQ : 0 ≤ Q := mul_nonneg (by norm_num) Hshort.curvature_bound_nonneg
  let scalarBound (j : ℕ) : ℝ := Q * T (j + 1) / (T (j + 1) - T j)
  let B (j : ℕ) : ℝ := 13 * max 4 (scalarBound j + 1)
  have hB (j : ℕ) : 0 ≤ B j :=
    mul_nonneg (by norm_num) ((by norm_num : (0 : ℝ) ≤ 4).trans (le_max_left _ _))
  have hprefix : ∀ n : ℕ, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ j : ℕ, j ≤ n → ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
        ∀ᶠ k : ℕ in atTop,
          Nonempty (ControlledBlowupCylinder S (phi k) A (T j) (B j) eta) := by
    intro n
    obtain ⟨V, hTV, hVTstar, ⟨G⟩⟩ := hlimits (T (n + 1))
      (hT (n + 1)).1 (hT (n + 1)).2
    have hV : 0 < V := (hT (n + 1)).1.trans hTV
    have hVT0 : ENNReal.ofReal V < T0 := hVTstar.trans_le hstarT0
    obtain ⟨Tplus, _hTplusNonneg, hVTplus, hTplusT0⟩ :=
      ENNReal.lt_iff_exists_real_btwn.mp hVT0
    have hTplus : 0 < Tplus := ENNReal.ofReal_pos.mp
      ((ENNReal.ofReal_pos.mpr hV).trans hVTplus)
    have hVTplus' : V < Tplus :=
      (ENNReal.ofReal_lt_ofReal_iff hTplus).mp hVTplus
    have hterminal : ∀ x, (G.limit.flow.connection 0).scalarCurvature x ≤ Q :=
      generalized_limit_terminal_scalar_le_of_short_controls Hshort G
    refine ⟨G.subsequence, G.subsequence_strictMono, ?_⟩
    intro j hj
    have hjnext : T j < T (j + 1) := hTmono (Nat.lt_succ_self j)
    have hjV : T (j + 1) ≤ V :=
      (hTmono.monotone (Nat.add_le_add_right hj 1)).trans hTV.le
    have hscalar : ∀ s ∈ Icc (-(T j)) 0, ∀ x,
        (G.limit.flow.connection s).scalarCurvature x ≤ scalarBound j := by
      intro s hs x
      have hsG : s ∈ Ioc (-V) 0 :=
        ⟨(neg_lt_neg (hjnext.trans_le hjV)).trans_le hs.1, hs.2⟩
      exact (finite_limit_scalar_le_of_terminal_bound P.m04 P.m06
        G.limit hterminal s hsG x).trans
          (harnack_bound_on_prefix hQ (hT j).1.le hjnext hjV hs.1)
    exact eventually_controlled_prefix_of_finite_scalar_bound P.m04
      H.toM30CommonBlowupControls G hVTplus'
      (H.slabs Tplus hTplus hTplusT0) (hT j).1 (hjnext.trans_le hjV) hscalar
  obtain ⟨rho, v, hrho, hv, hvolume⟩ :=
    exists_eventually_terminal_volume_lower_bound P.m04 H.toM30CommonBlowupControls hbound
  apply exists_backward_convergence_of_finite_prefixes
    P.m04.local_derivative_estimates_small withinFlowJetBoundsService.{0, 0}
    withinBilinearFlowService.{0} spatialSliceJetConvergenceService.{0, 0, 0, 0, 0}
    S hstar hrho hv H.balls_compact hvolume T B hB ?_ hprefix
  intro t _ht htstar
  obtain ⟨j, hj⟩ := (hcofinal t htstar).exists
  exact ⟨j, hj.le⟩




theorem exists_backward_convergence_of_finite_extension
    (P : M30ControlledBlowupPredecessors.{u})
    {S : GeneralizedBlowupSequence.{u}} {T0 : ℝ≥0∞}
    {epsilon C kappa r0 mu : ℝ}
    (H : M30LongBlowupControls S epsilon C kappa r0 mu T0)
    (Hshort : ShortControlledBlowupHypotheses S kappa r0)
    (hbound : GeneralizedBlowupBoundedDistance S)
    (hstep : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T0 →
      ∀ _G : GeneralizedBlowupConvergence S (Ioc (-T) 0),
        ∃ T' : ℝ, T < T' ∧ ENNReal.ofReal T' < T0 ∧
          Nonempty (GeneralizedBlowupConvergence S (Ioc (-T') 0))) :
    Nonempty (GeneralizedBlowupConvergence S (blowupBackwardInterval T0)) := by
  classical
  apply horizon_of_seed_cofinal_closure_and_extension
    (fun U => Nonempty (GeneralizedBlowupConvergence S (blowupBackwardInterval U)))
  · obtain ⟨T, hT, hTT0, hG⟩ :=
      exists_seed_finite_long_convergence_of_short_controls P S
        H.toM30CommonBlowupControls hbound Hshort H.horizon_pos
    refine ⟨ENNReal.ofReal T, ENNReal.ofReal_pos.mpr hT, hTT0.le, ?_⟩
    simpa only [blowupBackwardInterval_ofReal hT] using hG
  · intro U hU hUT0 hcofinal
    by_cases hdone : Nonempty (GeneralizedBlowupConvergence S (blowupBackwardInterval U))
    · exact hdone
    apply exists_backward_convergence_of_cofinal_finite_limits
      P H Hshort hbound hU hUT0
    intro r hr hrU
    obtain ⟨V, hrV, hVU, hGV⟩ := hcofinal (ENNReal.ofReal r) hrU
    have hVU' : V < U := lt_of_le_of_ne hVU (by
      intro heq
      subst V
      exact hdone hGV)
    have hVfinite : V ≠ ⊤ := (hVU'.trans_le le_top).ne
    have hVpos : 0 < V := (ENNReal.ofReal_pos.mpr hr).trans hrV
    have hT : 0 < V.toReal := ENNReal.toReal_pos hVpos.ne' hVfinite
    have hvalue : ENNReal.ofReal V.toReal = V := ENNReal.ofReal_toReal hVfinite
    refine ⟨V.toReal, ?_, hvalue.trans_lt hVU', ?_⟩
    · exact (ENNReal.ofReal_lt_ofReal_iff hT).mp (hrV.trans_eq hvalue.symm)
    · have hdomain : blowupBackwardInterval V = Ioc (-V.toReal) 0 :=
        (congrArg blowupBackwardInterval hvalue.symm).trans
          (blowupBackwardInterval_ofReal hT)
      exact hdomain ▸ hGV
  · intro U hU hUT0 hGU
    have hUfinite : U ≠ ⊤ := (hUT0.trans_le le_top).ne
    have hT : 0 < U.toReal := ENNReal.toReal_pos hU.ne' hUfinite
    have hvalue : ENNReal.ofReal U.toReal = U := ENNReal.ofReal_toReal hUfinite
    have hG : Nonempty (GeneralizedBlowupConvergence S (Ioc (-U.toReal) 0)) := by
      have hdomain : blowupBackwardInterval U = Ioc (-U.toReal) 0 :=
        (congrArg blowupBackwardInterval hvalue.symm).trans
          (blowupBackwardInterval_ofReal hT)
      exact hdomain ▸ hGU
    obtain ⟨G⟩ := hG
    obtain ⟨T', hTT', hT'T0, hG'⟩ :=
      hstep U.toReal hT (hvalue.trans_lt hUT0) G
    have hT' : 0 < T' := hT.trans hTT'
    refine ⟨ENNReal.ofReal T', ?_, hT'T0.le, ?_⟩
    · exact hvalue.symm.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hT').mpr hTT')
    · simpa only [blowupBackwardInterval_ofReal hT'] using hG'

end PoincareConjecture.M30
