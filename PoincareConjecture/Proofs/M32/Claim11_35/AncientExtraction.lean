import PoincareConjecture.Proofs.M32.Claim11_32.Controls
import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.LongControls
import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.LimitCurvatureBound
import PoincareConjecture.Proofs.M32.Claim11_34.TerminalAnnuli
import PoincareConjecture.Proofs.M32.Claim11_34.LimitLine
import PoincareConjecture.Proofs.M32.Claim11_35.TerminalAncientCylinder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem terminalBlowupSequence_exists_normalized_ancientCylinder
    (P : RepairedHornSelectionPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ epsilon C Banalytic Kcut : ℝ,
        0 < epsilon → epsilon ≤ epsilon₀ → 0 < C → 0 < Banalytic → 0 < Kcut →
      ∀ A_top : RepairedNeckCapTopologyTheory.{u},
        terminalAccuracyFactor * epsilon ≤ A_top.epsilon₀ →
      ∀ {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
        [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
        [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
        [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
        [∀ k, SecondCountableTopology (M k)]
        {F : ℕ → GeneralizedRicciFlowData.{u}} {terminal : ℕ → ℝ}
        (H : ∀ k, SingularTimeAssumptions (F k) (terminal k) (M k))
        (Q : ∀ k, SingularLimitConclusion (H k))
        (x : ∀ k, ((Q k).extension.extended.slice (terminal k)).carrier)
        (hpos : ∀ k, 0 < ((Q k).extension.extended.connection
          (terminal k)).scalarCurvature (x k))
        (hdiv : Tendsto (fun k => ((Q k).extension.extended.connection
          (terminal k)).scalarCurvature (x k)) atTop atTop),
        (∀ k, (H k).epsilon = epsilon) →
        (∀ k, (H k).constant = C) →
        (∀ k, (H k).analytic_constant = Banalytic) →
        (∀ k, (H k).r₀⁻¹ ^ 2 < Kcut) →
        (∀ k, (H k).r₀⁻¹ ^ 2 <
          4 * (terminalBlowupSequence H Q x hpos hdiv).scale k) →
      ∀ horn : ∀ k, StrongHorn (Q k).extension (terminalAccuracyFactor * (H k).epsilon),
        (∀ k, x k ∈ (horn k).carrier) →
        (∀ k, ∀ y ∈ (horn k).boundary_sphere,
          ((Q k).extension.extended.connection (terminal k)).scalarCurvature y ≤ Kcut) →
        ∃ (phi : ℕ → ℕ) (hphi : StrictMono phi)
          (G : RepairedLongControlledBlowupConclusion
            (blowupSequenceComp (terminalBlowupSequence H Q x hpos hdiv) phi hphi)
            neckNoncollapseConstant 1 ⊤)
          (Phi : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯
            G.convergence.limit.carrier.carrier) (q : UnitTwoSphere),
          Phi (q, 0) = G.convergence.limit.base ∧
            ∀ t ≤ 0, roundCylinderPullback (G.convergence.limit.flow.metric t) Phi =
              EvolvingRoundCylinderMetric t := by
  classical
  obtain ⟨epsilonStages, hStagesPos, hStagesSmall, hstages⟩ :=
    terminalBlowupSequence_longControls_after_initial_limit P
  obtain ⟨epsilonAnnuli, hAnnuliPos, _hAnnuliSmall, hannuli⟩ :=
    terminalBlowupSequence_eventually_horn_annulus_separation.{u}
  let epsilon29 := Classical.choose P.m29.constants
  let epsilon30 := Classical.choose P.m30.limits
  let epsilon₀ := min epsilon29
    (min epsilon30 (min (epsilonStages / terminalAccuracyFactor)
      (epsilonAnnuli / terminalAccuracyFactor)))
  have hPos : 0 < epsilon₀ :=
    lt_min (Classical.choose_spec P.m29.constants).1
      (lt_min (Classical.choose_spec P.m30.limits).1
        (lt_min (div_pos hStagesPos terminalAccuracyFactor_pos)
          (div_pos hAnnuliPos terminalAccuracyFactor_pos)))
  have hSmall : epsilon₀ ≤ 1 / 200 :=
    (min_le_left _ _).trans (Classical.choose_spec P.m29.constants).2.1
  refine ⟨epsilon₀, hPos, hSmall, ?_⟩
  intro epsilon C Banalytic Kcut hEpsilon hEpsilonSmall hCpos hBanalytic hKcut A_top hTop
    M _ _ _ _ _ _ _ _ F terminal H Q x hpos hdiv
    hepsilon hC hanalytic hcutoff hscale horn hx hboundary
  let S := terminalBlowupSequence H Q x hpos hdiv
  have hEpsilon29 : epsilon ≤ epsilon29 :=
    hEpsilonSmall.trans (min_le_left _ _)
  have hTail : epsilon ≤ min epsilon30
      (min (epsilonStages / terminalAccuracyFactor)
        (epsilonAnnuli / terminalAccuracyFactor)) :=
    hEpsilonSmall.trans (min_le_right _ _)
  have hEpsilon30 : epsilon ≤ epsilon30 := hTail.trans (min_le_left _ _)
  have hTerminal : epsilon ≤ min (epsilonStages / terminalAccuracyFactor)
      (epsilonAnnuli / terminalAccuracyFactor) := hTail.trans (min_le_right _ _)
  have hAlphaStages : terminalAccuracyFactor * epsilon ≤ epsilonStages :=
    (le_div_iff₀' terminalAccuracyFactor_pos).mp (hTerminal.trans (min_le_left _ _))
  have hAlphaAnnuli : terminalAccuracyFactor * epsilon ≤ epsilonAnnuli :=
    (le_div_iff₀' terminalAccuracyFactor_pos).mp (hTerminal.trans (min_le_right _ _))
  have hHalf : terminalAccuracyFactor * epsilon < 1 / 2 :=
    (hAlphaStages.trans hStagesSmall).trans_lt (by norm_num)
  have hAccuracyStages (k : ℕ) :
      terminalAccuracyFactor * (H k).epsilon ≤ epsilonStages := by
    simpa only [hepsilon k] using hAlphaStages
  have hAccuracyAnnuli (k : ℕ) :
      terminalAccuracyFactor * (H k).epsilon ≤ epsilonAnnuli := by
    simpa only [hepsilon k] using hAlphaAnnuli
  have hAccuracyTop (k : ℕ) :
      terminalAccuracyFactor * (H k).epsilon ≤ A_top.epsilon₀ := by
    simpa only [hepsilon k] using hTop
  let hornFixed (k : ℕ) : StrongHorn (Q k).extension (terminalAccuracyFactor * epsilon) :=
    (hepsilon k) ▸ horn k
  have hCarrier (k : ℕ) : (hornFixed k).carrier = (horn k).carrier := by
    dsimp only [hornFixed]
    generalize hepsilon k = h
    cases h
    rfl
  have hBoundary (k : ℕ) : (hornFixed k).boundary_sphere = (horn k).boundary_sphere := by
    dsimp only [hornFixed]
    generalize hepsilon k = h
    cases h
    rfl
  have hxFixed (k : ℕ) : x k ∈ (hornFixed k).carrier := by
    rw [hCarrier]
    exact hx k
  have hboundaryFixed (k : ℕ) (y) (hy : y ∈ (hornFixed k).boundary_sphere) :
      ((Q k).extension.extended.connection (terminal k)).scalarCurvature y ≤ Kcut := by
    rw [hBoundary] at hy
    exact hboundary k y hy
  let common : M30CommonBlowupControls S epsilon C neckNoncollapseConstant 1 (1 / 2) :=
    terminalBlowupSequence_commonControls H Q x hpos hdiv P.m04 P.m29
      hEpsilon hEpsilon29 hHalf hCpos hKcut hBanalytic hepsilon hC hanalytic
      hcutoff hscale hornFixed hxFixed hboundaryFixed
  obtain ⟨short⟩ := terminalBlowupSequence_short_limit H Q x hpos hdiv P.m04 P.m29 P.m30
    hEpsilon hEpsilon29 hEpsilon30 hHalf hCpos hKcut hBanalytic hepsilon hC hanalytic
    hcutoff hscale hornFixed hxFixed hboundaryFixed
  obtain ⟨G0⟩ := short.convergence
  let phi := G0.subsequence
  have hphi : StrictMono phi := G0.subsequence_strictMono
  let S0 := blowupSequenceComp S phi hphi
  obtain ⟨Mbound, Bstage, c, hMbound, _hBstage, hc, _hcEq, hstage, ⟨longControls⟩⟩ :=
    hstages H Q x hpos hdiv A_top hKcut hBanalytic hCpos hcutoff hanalytic
      (fun k => (hC k).le) hAccuracyStages hAccuracyTop horn hx hboundary G0 common
  obtain ⟨G⟩ := (Classical.choose_spec P.m30.limits).2.2.2
    S0 epsilon C neckNoncollapseConstant 1 (1 / 2) ⊤ hEpsilon30 longControls
  have hscalarStages : ∀ n : ℕ, ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      ∃ e : ControlledBlowupCylinder S0 k A ((n : ℝ) * c) Bstage 1,
        ∀ s hs y, y ∈ S0.baseBall k A →
          (S0.flow k).scalar (e.embedding.pointMap s hs y) ≤ Mbound * S0.scale k := by
    intro n A hA
    filter_upwards [hstage n A hA 1 zero_lt_one] with k hk
    obtain ⟨e, hscalar, _hnoncollapse⟩ := hk
    exact ⟨e, hscalar⟩
  have _hFinalScalar : ∀ t ≤ 0, ∀ y,
      (G.convergence.limit.flow.connection t).scalarCurvature y ≤ Mbound := by
    intro t ht y
    exact blowup_scalar_le_of_step_cylinders G.convergence hc hscalarStages
      t ⟨ht, ENNReal.ofReal_lt_top⟩ y
  have hFinalCurvature : ∀ t ≤ 0, ∀ y,
      (G.convergence.limit.flow.connection t).curvatureTensorNorm y ≤ Mbound := by
    intro t ht y
    exact blowup_curvatureTensorNorm_le_of_step_cylinders G.convergence hc hscalarStages
      t ⟨ht, ENNReal.ofReal_lt_top⟩ y

  choose N hcenter using fun k => (horn (phi k)).every_point_neck (x (phi k)) (hx (phi k))
  obtain ⟨hSphere, hAnnulus⟩ := hannuli
    (M := fun k => M (phi k)) (F := fun k => F (phi k))
    (T := fun k => terminal (phi k))
    (fun k => H (phi k)) (fun k => Q (phi k)) (fun k => x (phi k))
    (fun k => hpos (phi k)) (hdiv.comp hphi.tendsto_atTop) P.m04 A_top
    hKcut hBanalytic (fun k => hcutoff (phi k)) (fun k => hanalytic (phi k))
    (fun k => hAccuracyAnnuli (phi k)) (fun k => hAccuracyTop (phi k))
    (fun k => horn (phi k)) (fun k => hx (phi k)) (fun k => hboundary (phi k))
    N hcenter longControls.balls_compact
  let Sigma : ∀ k, Set ((S0.flow k).slice (S0.base k).1).carrier :=
    fun k => (N k).central_sphere
  obtain ⟨_hcompact, gamma, _hcontinuous, hGamma, _hanchor, _htails⟩ :=
    blowup_exists_minimizing_line_and_compact_separator G.convergence Sigma
      (D := 2 * Real.pi + 1) (R₀ := 2 * Real.pi + 3)
      (by positivity) (Filter.Eventually.of_forall hSphere) (by positivity) hAnnulus
  obtain ⟨Phi, q, hbase, hmetric⟩ :=
    terminalLongBlowupConclusion_exists_normalized_evolvingCylinder P
      (M := fun k => M (phi k)) (F := fun k => F (phi k))
      (T := fun k => terminal (phi k))
      (fun k => H (phi k)) (fun k => Q (phi k)) (fun k => x (phi k))
      (fun k => hpos (phi k)) (hdiv.comp hphi.tendsto_atTop) G
      hKcut hBanalytic (fun k => hcutoff (phi k)) (fun k => hanalytic (phi k))
      (fun k => horn (phi k)) (fun k => hx (phi k)) (fun k => hboundary (phi k))
      hMbound.le hFinalCurvature gamma hGamma
  exact ⟨phi, hphi, G, Phi, q, hbase, hmetric⟩

end PoincareConjecture.M32
