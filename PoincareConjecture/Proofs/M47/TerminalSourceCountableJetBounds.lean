import PoincareConjecture.Proofs.M47.TerminalSourceCountableNegative
import PoincareConjecture.Proofs.M47.TerminalSourceJetsG4MixedAssembly











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ



theorem terminalSourceCountable_g4_jet_bounds (j : ℕ)
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (P : M46Predecessors.{u})
    {tau R L eta rho : ℝ} (htau : 0 < tau) (hrho : 0 < rho)
    (hrhoR : 2 * rho < R)
    (hsmall : ∀ s : ℝ, |s| ≤ 2 * rho →
      ((13 * max (4 * L / 3) 1) * s ^ 2) *
        Real.exp (max 1 ((13 * max (4 * L / 3) 1) * s ^ 2)) ≤ 3)
    (F0 : {k : ℕ // j ≤ k} → SurgeryFlowData.{u})
    (O : ∀ a, SurgeryObservation (F0 a))
    (W : ∀ a, M33RegularHistoryWindow (F0 a))
    (H : ∀ a, M33RegularHistoryData (W a))
    (C0 : {k : ℕ // j ≤ k} → GeneralizedSliceCarrier.{u})
    (base Q rNext : {k : ℕ // j ≤ k} → ℝ)
    (U : ∀ a, Opens (C0 a).carrier)
    (e : ∀ a, GeneralizedFlowCylinder (H a).generalized (C0 a)
      (base a) (Q a) (Icc (-tau) 0) (U a : Set (C0 a).carrier))
    (F : ∀ a, RicciFlow 3 (U a) (Icc (-tau) 0))
    (C : ∀ a, TerminalSourceChart ((F a).metric 0) R)
    (hGood : ∀ᶠ a in Filter.comap
        (Subtype.val : {k : ℕ // j ≤ k} → ℕ) atTop,
      TerminalSourceJetsG4Good S B p (O a) (H a) (U a) (e a) (F a)
        (τ := tau) (base := base a) (Q := Q a) (rNext := rNext a)
        (R := R) (L := L) (eta := eta) (C a))
    (f0 : ℕ → E → V)
    (hread : ∀ a, EqOn (f0 a.val)
      (((F a).metric 0).pullbackCoefficients (C a).chart)
      (Metric.ball 0 (rho / 2))) :
    (∀ m : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ k in atTop,
      ∀ x ∈ Metric.ball (0 : E) (rho / 2),
        ‖iteratedFDeriv ℝ m (f0 k) x‖ ≤ D) ∧
      (∀ m : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ k in atTop,
        ∀ t ∈ Ioo (-(tau / 2)) 0, ∀ x ∈ Metric.closedBall (0 : E) rho,
          ‖iteratedFDeriv ℝ m
            (terminalSourceCountableNegative j (fun a => (U a : Type u)) F C f0 k)
            (t, x)‖ ≤ D) := by
  let l := Filter.comap (Subtype.val : {k : ℕ // j ≤ k} → ℕ) atTop
  have hraw := terminalSourceJetsG4_eventually_raw l S B p P htau
    F0 O W H C0 base Q rNext U e F C hGood
  have hcurv : 0 < 13 * max (4 * L / 3) 1 :=
    mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hsmallBall : Metric.ball (0 : E) (rho / 2) ⊆ Metric.closedBall 0 rho :=
    (Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall
  constructor
  · intro m
    obtain ⟨D, hD, hbound⟩ :=
      terminalSourceJets_spatial P.m04 htau hcurv hrho hrhoR hsmall m
    have hrawNat := Filter.eventually_comap.mp hraw
    refine ⟨D, hD, ?_⟩
    filter_upwards [hrawNat, eventually_ge_atTop j] with k hk hjk x hx
    let a : {k : ℕ // j ≤ k} := ⟨k, hjk⟩
    have hjet := terminalSourceCountable_coefficient_jets
      (fun _ => terminalSourceCountableDomain rho) (i := 0) (hread a) m hx
    rw [hjet]
    exact hbound (F a) (C a) (hk a rfl) 0 ⟨by linarith, le_rfl⟩
      x (hsmallBall hx) m le_rfl
  · intro m
    obtain ⟨D, hD, hbound⟩ := terminalSourceJetsG4_eventually_mixed l S B p P
      htau hrho hrhoR hsmall F0 O W H C0 base Q rNext U e F C hGood
      (fun a q => ((F a).metric q.1).pullbackCoefficients (C a).chart q.2)
      (Filter.Eventually.of_forall (fun _ _ _ => rfl))
      (K := Metric.closedBall 0 rho) (Subset.refl _) m
    have hboundNat := Filter.eventually_comap.mp hbound
    refine ⟨D, hD, ?_⟩
    filter_upwards [hboundNat, eventually_ge_atTop j] with k hk hjk t ht x hx
    rw [terminalSourceCountableNegative_good_jets j (fun a => (U a : Type u))
      F C f0 hjk]
    exact hk ⟨k, hjk⟩ rfl t ht x hx

end PoincareConjecture.M47
