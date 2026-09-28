import PoincareConjecture.Proofs.M47.TerminalSourceCountableJetBounds
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

private theorem time_difference_bound {tau D : ℝ} (htau : 0 < tau)
    {U : Set E} (hU : IsOpen U) (f : ℝ × E → V)
    (hf : ContDiffOn ℝ ∞ f (Icc (-tau) 0 ×ˢ U))
    (hbound : ∀ t ∈ Ioo (-(tau / 2)) 0, ∀ x ∈ U,
      ‖iteratedFDeriv ℝ 1 f (t, x)‖ ≤ D) :
    ∀ t ∈ Ioo (-(tau / 2)) 0, ∀ x ∈ U,
      ‖f (t, x) - f (0, x)‖ ≤ D * |t| := by
  intro t ht x hx
  have hopen : ContDiffOn ℝ ∞ f (Ioo (-tau) 0 ×ˢ U) :=
    hf.mono (prod_mono Ioo_subset_Icc_self (Subset.refl _))
  have hcontinuous : ContinuousOn (fun s : ℝ => f (s, x)) (Icc t 0) :=
    hf.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨⟨by linarith [ht.1, hs.1], hs.2⟩, hx⟩)
  have hderiv (s : ℝ) (hs : s ∈ Ico t 0) :
      HasDerivWithinAt (fun u : ℝ => f (u, x))
        (fderiv ℝ f (s, x) (1, 0)) (Ici s) s := by
    have hp : (s, x) ∈ Ioo (-tau) 0 ×ˢ U :=
      ⟨⟨by linarith [ht.1, hs.1], hs.2⟩, hx⟩
    have hd := (hopen.contDiffAt ((isOpen_Ioo.prod hU).mem_nhds hp)).differentiableAt
      (by simp)
    exact (hd.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))).hasDerivWithinAt
  have hnorm (s : ℝ) (hs : s ∈ Ico t 0) :
      ‖fderiv ℝ f (s, x) (1, 0)‖ ≤ D := by
    have hb : ‖fderiv ℝ f (s, x)‖ ≤ D := by
      simpa only [norm_iteratedFDeriv_one] using
        hbound s ⟨ht.1.trans_le hs.1, hs.2⟩ x hx
    have hn : ‖((1 : ℝ), (0 : E))‖ = 1 := by simp
    exact ((fderiv ℝ f (s, x)).le_opNorm (1, 0)).trans
      (by simpa only [hn, mul_one] using hb)
  have h := norm_image_sub_le_of_norm_deriv_right_le_segment
    hcontinuous hderiv hnorm 0 ⟨ht.2.le, le_rfl⟩
  calc
    _ = ‖f (0, x) - f (t, x)‖ := norm_sub_rev _ _
    _ ≤ D * (0 - t) := h
    _ = D * |t| := by rw [zero_sub, abs_of_neg ht.2]

theorem terminalSourceCountable_g4_closed_bounds (j : ℕ)
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
    let f := terminalSourceCountableNegative j (fun a => (U a : Type u)) F C f0
    (∀ᶠ k in atTop, ∀ t ∈ Icc (-tau) 0, ∀ x ∈ Metric.ball (0 : E) (rho / 2), ∀ v,
      terminalSourceLower (13 * max (4 * L / 3) 1) tau * ‖v‖ ^ 2 ≤ f k (t, x) v v) ∧
      ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ k in atTop,
        ∀ t ∈ Ioo (-(tau / 2)) 0, ∀ x ∈ Metric.ball (0 : E) (rho / 2),
          ‖f k (t, x) - f0 k x‖ ≤ D * |t| := by
  let f := terminalSourceCountableNegative j (fun a => (U a : Type u)) F C f0
  let l := Filter.comap (Subtype.val : {k : ℕ // j ≤ k} → ℕ) atTop
  have hraw := Filter.eventually_comap.mp (terminalSourceJetsG4_eventually_raw
    l S B p P htau F0 O W H C0 base Q rNext U e F C hGood)
  have hcurv : 0 < 13 * max (4 * L / 3) 1 :=
    mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hball : Metric.ball (0 : E) (rho / 2) ⊆ Metric.closedBall 0 rho :=
    (Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall
  constructor
  · filter_upwards [hraw, eventually_ge_atTop j] with k hk hjk t ht x hx v
    rw [terminalSourceCountableNegative_good j (fun a => (U a : Type u)) F C f0 hjk]
    exact ((C ⟨k, hjk⟩).closed_bounds htau hcurv.le (F ⟨k, hjk⟩)
      hrhoR hsmall (hk ⟨k, hjk⟩ rfl) ht
      (Metric.closedBall_subset_closedBall (by linarith) (hball hx)) v).1
  · obtain ⟨D, hD, hbound⟩ := (terminalSourceCountable_g4_jet_bounds j S B p P
      htau hrho hrhoR hsmall F0 O W H C0 base Q rNext U e F C hGood f0 hread).2 1
    refine ⟨D, hD, ?_⟩
    filter_upwards [hbound, eventually_ge_atTop j] with k hk hjk
    have hsmooth : ContDiffOn ℝ ∞ (f k)
        (Icc (-tau) 0 ×ˢ Metric.ball (0 : E) (rho / 2)) := by
      dsimp only [f]
      rw [terminalSourceCountableNegative_good j (fun a => (U a : Type u)) F C f0 hjk]
      exact (M44.contDiffOn_pullbackCoefficients_within (F ⟨k, hjk⟩)
        Metric.isOpen_ball (C ⟨k, hjk⟩).smooth).mono
          (prod_mono (Subset.refl _) (Metric.ball_subset_ball (by linarith)))
    have hz : ∀ x ∈ Metric.ball (0 : E) (rho / 2), f k (0, x) = f0 k x := by
      intro x hx
      dsimp only [f]
      rw [terminalSourceCountableNegative_good j (fun a => (U a : Type u)) F C f0 hjk]
      exact (hread ⟨k, hjk⟩ hx).symm
    intro t ht x hx
    rw [← hz x hx]
    exact time_difference_bound htau Metric.isOpen_ball (f k) hsmooth
      (fun s hs y hy => hk s hs y (hball hy)) t ht x hx

end PoincareConjecture.M47
