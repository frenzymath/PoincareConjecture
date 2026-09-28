import PoincareConjecture.Proofs.M32.Claim11_35.AncientExtraction
import PoincareConjecture.Proofs.M32.Claim11_35.Transfer.HornNecks
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M32

theorem exists_uniform_terminalHorn_pointwise_neck_height
    (P : RepairedHornSelectionPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
      ∀ r₀ C Banalytic rho delta hUpper : ℝ,
        0 < r₀ → 0 < C → 0 < Banalytic → 0 < rho → 0 < delta → 0 < hUpper →
      ∀ A_top : RepairedNeckCapTopologyTheory.{u},
        terminalAccuracyFactor * epsilon ≤ A_top.epsilon₀ →
      ∃ h : ℝ, 0 < h ∧ h ≤ hUpper ∧
        ∀ {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
          {M : Type u} [TopologicalSpace M]
          [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
          [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
          [T2Space M] [T3Space M] [SecondCountableTopology M]
          (H : SingularTimeAssumptions F T M),
          H.r₀ = r₀ → H.epsilon = epsilon → H.constant = C →
          H.analytic_constant = Banalytic →
        ∀ (Q : SingularLimitConclusion H)
          (horn : StrongHorn Q.extension (terminalAccuracyFactor * H.epsilon)),
          HornBoundaryBelow horn (rho / (2 * H.constant)) →
          ∀ x ∈ horn.carrier,
            h⁻¹ ^ 2 ≤ (Q.extension.extended.connection T).scalarCurvature x →
            ∃ N : TerminalStrongNeck Q.extension delta,
              N.center = x ∧ N.carrier ⊆ horn.carrier := by
  classical
  obtain ⟨epsilon₀, hEpsilonPos, hEpsilonSmall, hancient⟩ :=
    terminalBlowupSequence_exists_normalized_ancientCylinder P
  refine ⟨epsilon₀, hEpsilonPos, hEpsilonSmall, ?_⟩
  intro epsilon hepsilon hsmall r₀ C Banalytic rho delta hUpper
    hradius hC hBanalytic _hrho hdelta hUpperPos A_top hTop
  by_contra hNoHeight
  have hbad (h : ℝ) (hh : 0 < h) (hhUpper : h ≤ hUpper) :
      ∃ (ref : GeneralizedSliceCarrier.{u}) (F : GeneralizedRicciFlowData.{u})
        (T : ℝ) (H : SingularTimeAssumptions F T ref.carrier)
        (Q : SingularLimitConclusion H)
        (horn : StrongHorn Q.extension (terminalAccuracyFactor * H.epsilon))
        (x : (Q.extension.extended.slice T).carrier),
        H.r₀ = r₀ ∧ H.epsilon = epsilon ∧ H.constant = C ∧
        H.analytic_constant = Banalytic ∧
        HornBoundaryBelow horn (rho / (2 * H.constant)) ∧ x ∈ horn.carrier ∧
        h⁻¹ ^ 2 ≤ (Q.extension.extended.connection T).scalarCurvature x ∧
        ¬ ∃ N : TerminalStrongNeck Q.extension delta,
          N.center = x ∧ N.carrier ⊆ horn.carrier := by
    by_contra hnone
    push Not at hnone
    apply hNoHeight
    refine ⟨h, hh, hhUpper, ?_⟩
    intro F T M _ _ _ _ _ _ _ _ H hr he hc ha Q horn hb x hx hR
    let ref : GeneralizedSliceCarrier.{u} := {
      carrier := M
      topologicalSpace := inferInstance
      measurableSpace := inferInstance
      borelSpace := inferInstance
      chartedSpace := inferInstance
      isManifold := inferInstance
      t2Space := inferInstance
      t3Space := inferInstance
      secondCountable := inferInstance }
    exact hnone ref F T H Q horn x hr he hc ha hb hx hR
  let height (n : ℕ) : ℝ := min hUpper (min (r₀ / 2) (1 / ((n : ℝ) + 1)))
  have hHeightPos (n : ℕ) : 0 < height n :=
    lt_min hUpperPos (lt_min (half_pos hradius) (by positivity))
  have hHeightUpper (n : ℕ) : height n ≤ hUpper := min_le_left _ _
  have hHeightRadius (n : ℕ) : height n ≤ r₀ / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hHeightSmall (n : ℕ) : height n ≤ 1 / ((n : ℝ) + 1) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have _hHeightZero : Tendsto height atTop (𝓝 0) :=
    squeeze_zero (fun n => (hHeightPos n).le) hHeightSmall
      tendsto_one_div_add_atTop_nhds_zero_nat
  choose ref F terminal H Q horn x hRadius hEpsilon hConstant hAnalytic
    hBoundary hx hScalar hFailure using
      fun n => hbad (height n) (hHeightPos n) (hHeightUpper n)

  let M (n : ℕ) : Type u := (ref n).carrier
  let : ∀ n, TopologicalSpace (M n) := fun n => (ref n).topologicalSpace
  let : ∀ n, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M n) :=
    fun n => (ref n).chartedSpace
  let : ∀ n, IsManifold (𝓡 3) ∞ (M n) := fun n => (ref n).isManifold
  let : ∀ n, MeasurableSpace (M n) := fun n => (ref n).measurableSpace
  let : ∀ n, BorelSpace (M n) := fun n => (ref n).borelSpace
  let : ∀ n, T2Space (M n) := fun n => (ref n).t2Space
  let : ∀ n, T3Space (M n) := fun n => (ref n).t3Space
  let : ∀ n, SecondCountableTopology (M n) := fun n => (ref n).secondCountable
  let scalar (n : ℕ) :=
    ((Q n).extension.extended.connection (terminal n)).scalarCurvature (x n)
  have hpos (n : ℕ) : 0 < scalar n :=
    (sq_pos_of_pos (inv_pos.mpr (hHeightPos n))).trans_le (hScalar n)
  have hscale (n : ℕ) : (H n).r₀⁻¹ ^ 2 < 4 * scalar n := by
    rw [hRadius n]
    have hlt : height n < r₀ := (hHeightRadius n).trans_lt (half_lt_self hradius)
    have hinv : r₀⁻¹ < (height n)⁻¹ :=
      (inv_lt_inv₀ hradius (hHeightPos n)).mpr hlt
    have hsq : r₀⁻¹ ^ 2 < (height n)⁻¹ ^ 2 :=
      pow_lt_pow_left₀ hinv (inv_nonneg.mpr hradius.le) (by norm_num)
    have hltScalar : r₀⁻¹ ^ 2 < scalar n := hsq.trans_le (hScalar n)
    linarith [hpos n]
  have hNatLeScalar (n : ℕ) : (n : ℝ) ≤ scalar n := by
    have hinv : (1 / ((n : ℝ) + 1))⁻¹ ≤ (height n)⁻¹ :=
      (inv_le_inv₀ (by positivity) (hHeightPos n)).mpr (hHeightSmall n)
    have hn : (n : ℝ) + 1 ≤ (height n)⁻¹ := by
      simpa only [one_div, inv_inv] using hinv
    have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) hn 2
    have hle : ((n : ℝ) + 1) ^ 2 ≤ scalar n := hsq.trans (hScalar n)
    nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]
  have hdiv : Tendsto scalar atTop atTop :=
    tendsto_atTop_mono hNatLeScalar tendsto_natCast_atTop_atTop
  let Kcut : ℝ := max (r₀⁻¹ ^ 2 + 1) ((rho / (2 * C))⁻¹ ^ 2)
  have hKcut : 0 < Kcut :=
    (by positivity : 0 < r₀⁻¹ ^ 2 + 1).trans_le (le_max_left _ _)
  have hcutoff (n : ℕ) : (H n).r₀⁻¹ ^ 2 < Kcut := by
    rw [hRadius n]
    exact (lt_add_one _).trans_le (le_max_left _ _)
  have hboundary (n : ℕ) (y) (hy : y ∈ (horn n).boundary_sphere) :
      ((Q n).extension.extended.connection (terminal n)).scalarCurvature y ≤ Kcut := by
    have hb := hBoundary n y hy
    rw [hConstant n] at hb
    exact hb.trans (le_max_right _ _)
  obtain ⟨phi, hphi, G, Phi, q, hcenter, hmodel⟩ :=
    hancient epsilon C Banalytic Kcut hepsilon hsmall hC hBanalytic hKcut A_top hTop
      (M := M) (F := F) (terminal := terminal) H Q x hpos hdiv
      hEpsilon hConstant hAnalytic hcutoff hscale horn hx hboundary
  have hJI : Icc (-1 : ℝ) 0 ⊆ blowupBackwardInterval ⊤ :=
    fun _ hs => ⟨hs.2, ENNReal.ofReal_lt_top⟩
  have hnecks := terminalBlowupConvergence_eventually_strongNecks_in_horns
    (M := fun k => M (phi k)) (F := fun k => F (phi k))
    (T := fun k => terminal (phi k))
    (fun k => H (phi k)) (fun k => Q (phi k)) (fun k => x (phi k))
    (fun k => hpos (phi k)) (hdiv.comp hphi.tendsto_atTop)
    G.convergence hJI Phi q hcenter hdelta (fun t ht => hmodel t ht.2)
    P.m04 hKcut hBanalytic (fun k => hcutoff (phi k)) (fun k => hAnalytic (phi k))
    (fun k => horn (phi k)) (fun k => hx (phi k)) (fun k => hboundary (phi k))
  obtain ⟨k, hk⟩ := hnecks.exists
  exact hFailure (phi (G.convergence.subsequence k)) hk

end PoincareConjecture.M32
