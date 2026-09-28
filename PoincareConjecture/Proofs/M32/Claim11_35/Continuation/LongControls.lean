import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.Stages
import PoincareConjecture.Proofs.M32.Claim11_35.FiniteSlabs















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




theorem terminalBlowupSequence_longControls_after_initial_limit
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
      ∀ {J0 : Set ℝ} (G0 : GeneralizedBlowupConvergence
          (terminalBlowupSequence H Q x hpos hdiv) J0) {epsilon C : ℝ},
        M30CommonBlowupControls (terminalBlowupSequence H Q x hpos hdiv)
          epsilon C neckNoncollapseConstant 1 (1 / 2) →
        let S0 := blowupSequenceComp (terminalBlowupSequence H Q x hpos hdiv)
          G0.subsequence G0.subsequence_strictMono
        ∃ Mbound B c : ℝ, 0 < Mbound ∧ 0 < B ∧ 0 < c ∧ c = 1 / (4 * Mbound) ∧
          (∀ n : ℕ, stage[S0, (n : ℝ) * c, Mbound, B]) ∧
          Nonempty (M30LongBlowupControls S0 epsilon C neckNoncollapseConstant 1 (1 / 2) ⊤) := by
  obtain ⟨epsilonStages, hEpsilon, hSmall, hstages⟩ :=
    terminalBlowupSequence_exists_cofinal_controlled_stages P
  refine ⟨epsilonStages, hEpsilon, hSmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ F terminal H Q x hpos hdiv A_top Kcut Banalytic Ccap
    hKcut hBanalytic hCcap hcutoff hanalytic hconstant hepsilon htop horn hx hboundary
    J0 G0 epsilon C common
  let S := terminalBlowupSequence H Q x hpos hdiv
  let S0 := blowupSequenceComp S G0.subsequence G0.subsequence_strictMono
  obtain ⟨Mbound, B, c, hM, hB, hc, hcEq, hstage⟩ :=
    hstages H Q x hpos hdiv A_top hKcut hBanalytic hCcap hcutoff hanalytic hconstant
      hepsilon htop horn hx hboundary common.balls_compact G0
  have hslabs : ∀ n : ℕ, ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      Nonempty (M30FiniteHorizonSlab S0 k A ((n : ℝ) * c) neckNoncollapseConstant 1) := by
    intro n A hA
    filter_upwards [hstage n A hA 1 zero_lt_one] with k hk
    obtain ⟨e, _hscalar, hnoncollapse⟩ := hk
    exact ⟨{
      embedding := restrictCylinderTime e.embedding Ioc_subset_Icc_self
      zero_identity := fun hs y hy => e.zero_identity (Ioc_subset_Icc_self hs) y hy
      noncollapsed := fun s hs y hy => hnoncollapse s (Ioc_subset_Icc_self hs) y hy }⟩
  exact ⟨Mbound, B, c, hM, hB, hc, hcEq, hstage,
    ⟨longControls_of_step_slabs
      (blowupSequenceComp_commonControls S G0.subsequence G0.subsequence_strictMono common)
      hc hslabs⟩⟩

end PoincareConjecture.M32
