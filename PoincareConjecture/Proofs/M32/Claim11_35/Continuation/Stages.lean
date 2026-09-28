import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.StageStep
import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.SeedScalar
import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.SeedNecks
import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.Seed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

local macro "stage[" S:term "," T:term "," M:term "," B:term "]" : term =>
  `(∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
    ∃ e : ControlledBlowupCylinder $S k A $T $B eta,
      (∀ s hs y, y ∈ ($S).baseBall k A →
        (($S).flow k).scalar (e.embedding.pointMap s hs y) ≤ $M * ($S).scale k) ∧
      (∀ s hs y, y ∈ ($S).baseBall k A → GeneralizedKappaNoncollapsedAt
        (($S).flow k) (e.embedding.pointMap s hs y) neckNoncollapseConstant 1))

theorem terminalBlowupSequence_exists_cofinal_controlled_stages
    (P : RepairedHornSelectionPredecessors.{u}) :
    ∃ epsilonStages : ℝ, 0 < epsilonStages ∧ epsilonStages ≤ 1 / 200 ∧
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
          (terminal k)).scalarCurvature (x k)) atTop atTop)
        (A_top : RepairedNeckCapTopologyTheory.{u}) {Kcut Banalytic Ccap : ℝ},
        0 < Kcut → 0 < Banalytic → 0 < Ccap →
        (∀ k, (H k).r₀⁻¹ ^ 2 < Kcut) →
        (∀ k, (H k).analytic_constant = Banalytic) →
        (∀ k, (H k).constant ≤ Ccap) →
        (∀ k, terminalAccuracyFactor * (H k).epsilon ≤ epsilonStages) →
        (∀ k, terminalAccuracyFactor * (H k).epsilon ≤ A_top.epsilon₀) →
      ∀ horn : ∀ k, StrongHorn (Q k).extension (terminalAccuracyFactor * (H k).epsilon),
        (∀ k, x k ∈ (horn k).carrier) →
        (∀ k, ∀ y ∈ (horn k).boundary_sphere,
          ((Q k).extension.extended.connection (terminal k)).scalarCurvature y ≤ Kcut) →
        BlowupBaseBallsCompact (terminalBlowupSequence H Q x hpos hdiv) →
      ∀ {J0 : Set ℝ} (G0 : GeneralizedBlowupConvergence
        (terminalBlowupSequence H Q x hpos hdiv) J0),
        let S0 := blowupSequenceComp (terminalBlowupSequence H Q x hpos hdiv)
          G0.subsequence G0.subsequence_strictMono
        ∃ Mbound B c : ℝ, 0 < Mbound ∧ 0 < B ∧ 0 < c ∧ c = 1 / (4 * Mbound) ∧
          ∀ n : ℕ, stage[S0, (n : ℝ) * c, Mbound, B] := by
  obtain ⟨epsilonStep, Kstep, hStep, hStepSmall, hKstep, hstep⟩ :=
    exists_terminalBlowupSequence_noncollapsed_stage_step P
  obtain ⟨epsilonSeed, Kseed, hSeed, _hSeedSmall, hKseed, hseed⟩ :=
    exists_controlled_seed_of_terminal_strongNecks P.m04
  refine ⟨min epsilonStep epsilonSeed, lt_min hStep hSeed,
    (min_le_left _ _).trans hStepSmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ F terminal H Q x hpos hdiv A_top Kcut Banalytic Ccap
    hKcut hBanalytic hCcap hcutoff hanalytic hconstant hepsilon htop horn hx hboundary
    hballs J0 G0
  let S := terminalBlowupSequence H Q x hpos hdiv
  let S0 := blowupSequenceComp S G0.subsequence G0.subsequence_strictMono
  obtain ⟨Mbound, hM, hscalar⟩ := blowup_exists_uniform_terminal_scalar_bound G0
  let B := max Kseed Kstep * Mbound
  let c := 1 / (4 * Mbound)
  have hB : 0 < B := mul_pos (hKseed.trans_le (le_max_left _ _)) hM
  have hc : 0 < c := by dsimp [c]; positivity
  have hKMseed : Kseed * Mbound ≤ B := mul_le_mul_of_nonneg_right (le_max_left _ _) hM.le
  have hKMstep : Kstep * Mbound ≤ B := mul_le_mul_of_nonneg_right (le_max_right _ _) hM.le
  have hballs0 : BlowupBaseBallsCompact S0 :=
    fun A hA => G0.subsequence_strictMono.tendsto_atTop.eventually (hballs A hA)
  have hbranch : ∀ k, generalizedPinchedOrNonnegative (S0.flow k) := fun k =>
    extension_pinchedOrNonnegative P.m04 (H (G0.subsequence k)) (Q (G0.subsequence k)).extension
  have hseedNecks : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ closure (S0.baseBall k A), ∃ epsilon, epsilon ≤ epsilonSeed ∧
        ∃ N : GeneralizedStrongNeck (S0.flow k) (S0.base k).1 epsilon, N.center = y := by
    intro A hA
    filter_upwards [G0.subsequence_strictMono.tendsto_atTop.eventually
      (terminalBlowupSequence_eventually_closure_strongNecks H Q x hpos hdiv P.m04
        hKcut hBanalytic hcutoff hanalytic horn hx hboundary A hA)] with k hk y hy
    obtain ⟨N, hcenter⟩ := hk y hy
    exact ⟨terminalAccuracyFactor * (H (G0.subsequence k)).epsilon,
      (hepsilon _).trans (min_le_right _ _), N, hcenter⟩
  have hseedStage : stage[S0, c, Mbound, B] := by
    intro A hA eta heta
    exact (hseed hM hB.le hKMseed hc le_rfl hbranch hballs0 hscalar hseedNecks A hA eta heta).mono
      fun _ hk => hk.1
  have hnext (T : ℝ) (hcT : c ≤ T) (hstage : stage[S0, T, Mbound, B]) :
      stage[S0, T + c, Mbound, B] := by
    exact hstep hM hB.le hKMstep hc le_rfl hcT
      (M := fun k => M (G0.subsequence k)) (F := fun k => F (G0.subsequence k))
      (terminal := fun k => terminal (G0.subsequence k))
      (fun k => H (G0.subsequence k)) (fun k => Q (G0.subsequence k))
      (fun k => x (G0.subsequence k)) (fun k => hpos (G0.subsequence k))
      (hdiv.comp G0.subsequence_strictMono.tendsto_atTop) A_top hKcut hBanalytic hCcap
      (fun k => hcutoff (G0.subsequence k)) (fun k => hanalytic (G0.subsequence k))
      (fun k => hconstant (G0.subsequence k))
      (fun k => (hepsilon _).trans (min_le_left _ _)) (fun k => htop (G0.subsequence k))
      (fun k => horn (G0.subsequence k)) (fun k => hx (G0.subsequence k))
      (fun k => hboundary (G0.subsequence k)) hballs0 hstage
  have hpositiveStages : ∀ n : ℕ, stage[S0, ((n + 1 : ℕ) : ℝ) * c, Mbound, B] := by
    intro n
    induction n with
    | zero =>
      have heq : ((0 + 1 : ℕ) : ℝ) * c = c := by norm_num
      rw [heq]
      exact hseedStage
    | succ n ih =>
      have hcT : c ≤ ((n + 1 : ℕ) : ℝ) * c := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        push_cast
        nlinarith
      have h := hnext (((n + 1 : ℕ) : ℝ) * c) hcT ih
      have heq : ((n + 1 : ℕ) : ℝ) * c + c = ((n.succ + 1 : ℕ) : ℝ) * c := by
        push_cast
        ring
      rwa [heq] at h
  have hzeroStage : stage[S0, 0, Mbound, B] := by
    intro A hA eta heta
    filter_upwards [hseedStage A hA eta heta] with k hk
    obtain ⟨e, hscalarE, hnoncollapseE⟩ := hk
    let e0 := restrictControlledBlowupCylinderTime (T' := 0) e hc.le
    have htime : Icc (-(0 : ℝ)) 0 ⊆ Icc (-c) 0 :=
      Icc_subset_Icc (neg_le_neg hc.le) le_rfl
    exact ⟨e0, fun s hs y hy => hscalarE s (htime hs) y hy,
      fun s hs y hy => hnoncollapseE s (htime hs) y hy⟩
  refine ⟨Mbound, B, c, hM, hB, hc, rfl, ?_⟩
  intro n
  cases n with
  | zero =>
    have heq : ((0 : ℕ) : ℝ) * c = 0 := by norm_num
    rw [heq]
    exact hzeroStage
  | succ n => exact hpositiveStages n

end PoincareConjecture.M32
