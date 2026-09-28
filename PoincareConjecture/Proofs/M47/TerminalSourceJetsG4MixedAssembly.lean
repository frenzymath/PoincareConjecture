import PoincareConjecture.Proofs.M47.TerminalSourceJetsG4Assembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

theorem terminalSourceJetsG4_eventually_mixed
    {α : Type v} (l : Filter α)
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants)
    (P : M46Predecessors.{u})
    {τ R L eta ρ : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ) (hρR : 2 * ρ < R)
    (hsmall : ∀ s : ℝ, |s| ≤ 2 * ρ →
      ((13 * max (4 * L / 3) 1) * s ^ 2) *
        Real.exp (max 1 ((13 * max (4 * L / 3) 1) * s ^ 2)) ≤ 3)
    (F₀ : α → SurgeryFlowData.{u})
    (O : ∀ k, SurgeryObservation (F₀ k))
    (W : ∀ k, M33RegularHistoryWindow (F₀ k))
    (H : ∀ k, M33RegularHistoryData (W k))
    (C₀ : α → GeneralizedSliceCarrier.{u})
    (base Q rNext : α → ℝ)
    (U : ∀ k, TopologicalSpace.Opens (C₀ k).carrier)
    (e : ∀ k, GeneralizedFlowCylinder (H k).generalized (C₀ k)
      (base k) (Q k) (Icc (-τ) 0) (U k : Set (C₀ k).carrier))
    (F : ∀ k, RicciFlow 3 (U k) (Icc (-τ) 0))
    (C : ∀ k, TerminalSourceChart ((F k).metric 0) R)
    (hGood : ∀ᶠ k in l,
      TerminalSourceJetsG4Good S B p (O k) (H k) (U k) (e k) (F k)
        (τ := τ) (base := base k) (Q := Q k) (rNext := rNext k)
        (R := R) (L := L) (eta := eta) (C k))
    (fminus : α → ℝ × E → V)
    (hactual : ∀ᶠ k in l, EqOn (fminus k)
      (fun q : ℝ × E => ((F k).metric q.1).pullbackCoefficients (C k).chart q.2)
      (Ioo (-τ) 0 ×ˢ Metric.ball 0 R))
    {K : Set E} (hK : K ⊆ Metric.closedBall 0 ρ) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ k in l,
      ∀ t ∈ Ioo (-(τ / 2)) 0, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (fminus k) (t, x)‖ ≤ D := by
  have hG4 := terminalSourceJetsG4_eventually_raw l S B p P hτ F₀ O W H C₀
    base Q rNext U e F C hGood
  have hH : 0 < 13 * max (4 * L / 3) 1 :=
    mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  exact terminalSourceJetsG4_same_chart_mixed l (fun k => (U k : Type u)) P.m04
    hτ hH hρ hρR hsmall F C hG4 fminus hactual hK m

end PoincareConjecture.M47
