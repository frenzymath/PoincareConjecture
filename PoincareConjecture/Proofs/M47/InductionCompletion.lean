import PoincareConjecture.Proofs.M47.InductionMaximalCounterexample
import PoincareConjecture.Proofs.M47.InductionAncientContradiction
import PoincareConjecture.Proofs.M47.InductionFiniteContradiction
import PoincareConjecture.Proofs.M47.Induction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ENNReal

universe u

namespace PoincareConjecture.M47

theorem canonicalExtension
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (N : RepairedNoncollapseInductionData S)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    Nonempty (SurgeryCanonicalExtension p (Classical.choice (N.induction p hp))) := by
  classical
  by_contra hno
  obtain ⟨kappa, hkappa, r, F, O, t, W, history, ht, x, hPositive, hDiverges,
    data, capBudget, rho, hrho, hdec, controls, ⟨G⟩⟩ :=
    exists_maximal_regular_counterexample P S B N p hp hno
  let V := regularHistoryBlowupSequence F W history t ht x hPositive hDiverges
  let D := terminalCommonInterval_reindex V rho hrho
  choose old hBase hPinched hPast hFloor hbad hvolume hOverlap using data
  have hInitial (k : ℕ) : (F k).standard_initial = S.setup.standard_initial := by
    rw [(old k).standard_initial_eq, hp.setup_eq]
  have hParameters (k : ℕ) : (F k).parameters.epsilon = S.setup.epsilon ∧
      (F k).parameters.C = S.setup.C := by
    constructor
    · rw [(old k).epsilon_eq, hp.setup_eq]
    · rw [(old k).C_eq, hp.setup_eq]
  by_cases htop : terminalCommonIntervalHorizon D = ⊤
  · exact Proofs.M47.firstFailure_infinite_controls_false P S
      F W history t ht x hPositive hDiverges rho hrho (htop ▸ controls)
      (by norm_num : (0 : ℝ) < 1 / 128) hkappa
      (fun k => (hBase k).1) hParameters (Filter.Eventually.of_forall hvolume) hbad
  · obtain ⟨theta, htheta, T, hT, hlarge, hslab⟩ :=
      induction_exists_finite_horizon_extension
        (fun k => F (rho k)) (fun k => W (rho k)) (fun k => history (rho k))
        (t ∘ rho) (fun k => ht (rho k)) (fun k => x (rho k))
        (fun k => hPositive (rho k)) (hDiverges.comp hrho.tendsto_atTop) G
        (fun k => hbad (rho k))
        (capBudget (rho ∘ G.subsequence) (hrho.comp G.subsequence_strictMono))
        P S B controls (fun _ => p) (fun k => O (rho k)) htop
        (fun k => hInitial (rho k)) (fun k => (old (rho k)).local_constants_eq)
        (fun k => hParameters (rho k)) (fun k => hBase (rho k))
        (fun k => hPinched (rho k)) (r ∘ rho) (fun k => hFloor (rho k))
        (fun k => hPast (rho k)) (fun k => hOverlap (rho k))
    have hH : terminalCommonIntervalHorizon D < ENNReal.ofReal T := by
      rw [← ENNReal.ofReal_toReal htop]
      exact (ENNReal.ofReal_lt_ofReal_iff hT).mpr hlarge
    exact limitFinite_longer_slab_false hdec htheta hH hslab

theorem canonicalInduction
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S) :
    Nonempty (RepairedCanonicalInductionData S N) := by
  let PA : M47ComponentAnalyticPredecessors.{u} := {
    tensor_calculus := P.m04.tensor_calculus 3
    scalar_regular := P.m04.scalar_regular 3
    scalar_evolution := P.m04.scalar_evolution 3
    local_derivative_estimates := P.m04.local_derivative_estimates 3
    metric_comparison := P.m04.metric_comparison 3 }
  obtain ⟨B⟩ := componentAnalyticBounds P PA S.setup.C S.setup.C_large
  exact ⟨{ induction := fun p hp => canonicalExtension P S B N p hp }⟩

end PoincareConjecture.M47
