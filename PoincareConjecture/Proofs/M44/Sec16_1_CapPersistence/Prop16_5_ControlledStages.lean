import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_PreparedCounterexamples
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_SampleRestriction
import Mathlib.Order.Filter.AtTopBot.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

variable {constants : MetricSurgeryConstants} {setup : SurgeryControlSetup constants}
  {start rNext A eta theta cutoff Rinner : ℝ}

structure ControlledCapSample
    (X : PreparedCapCounterexample.{u} setup start rNext A eta theta cutoff Rinner)
    (R T K : ℝ) where

  outer : MaximalCapSample setup.standard_initial X.data.flow X.data.time
    X.data.is_surgery X.data.cap X.data.assignedDuration

  radius_eq : outer.radius = R

  eta_eq : outer.eta = X.sample.eta

  comparison_eq : outer.comparison.map = X.sample.comparison.map

  survival : min X.sample.lifetime T ≤ outer.lifetime

  curvature : ∀ t ∈ Ico (0 : ℝ) (min X.sample.lifetime T), ∀ y,
    (outer.ordinary.flow.connection t).curvatureTensorNorm y ≤ K

namespace ControlledCapSample

variable {X : PreparedCapCounterexample.{u} setup start rNext A eta theta cutoff Rinner}
  {R T K : ℝ}

noncomputable def restricted (D : ControlledCapSample X R T K) (hT : 0 < T) :
    CylinderCompactnessSample setup.standard_initial X.data.flow X.data.time
      X.data.is_surgery X.data.cap :=
  D.outer.toCylinderCompactnessSample.restrictLifetime
    (lt_min X.sample.lifetime_pos hT) D.survival

def mono (D : ControlledCapSample X R T K) {T' K' : ℝ}
    (hT : T' ≤ T) (hK : K ≤ K') : ControlledCapSample X R T' K' where
  outer := D.outer
  radius_eq := D.radius_eq
  eta_eq := D.eta_eq
  comparison_eq := D.comparison_eq
  survival := (min_le_min_left _ hT).trans D.survival
  curvature t ht y := (D.curvature t
    ⟨ht.1, ht.2.trans_le (min_le_min_left _ hT)⟩ y).trans hK

end ControlledCapSample

def CapSequenceStage {cutoffs : ℕ → ℝ}
    (X : ∀ n, PreparedCapCounterexample.{u} setup start rNext A eta theta (cutoffs n) Rinner)
    (R0 T K : ℝ) : Prop :=
  ∀ R : ℝ, R0 ≤ R → ∀ᶠ n in atTop, Nonempty (ControlledCapSample (X n) R T K)

namespace CapSequenceStage

variable {cutoffs : ℕ → ℝ}
  {X : ∀ n, PreparedCapCounterexample.{u} setup start rNext A eta theta (cutoffs n) Rinner}
  {R0 T K : ℝ}

theorem subsequence (h : CapSequenceStage X R0 T K) {sigma : ℕ → ℕ}
    (hsigma : StrictMono sigma) :
    CapSequenceStage (fun n => X (sigma n)) R0 T K :=
  fun R hR => hsigma.tendsto_atTop.eventually (h R hR)

theorem mono (h : CapSequenceStage X R0 T K) {R1 T1 K1 : ℝ}
    (hR : R0 ≤ R1) (hT : T1 ≤ T) (hK : K ≤ K1) :
    CapSequenceStage X R1 T1 K1 := by
  intro R hRR
  filter_upwards [h R (hR.trans hRR)] with n hn
  exact hn.map fun D => D.mono hT hK

theorem diagonal (h : CapSequenceStage X R0 T K) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      Nonempty (∀ n, ControlledCapSample (X (sigma n)) (R0 + (n : ℝ) + 1) T K) := by
  have hfixed (n : ℕ) : ∀ᶠ k in atTop,
      Nonempty (ControlledCapSample (X k) (R0 + (n : ℝ) + 1) T K) :=
    h _ (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  obtain ⟨sigma, hsigma, hsample⟩ := extraction_forall_of_eventually hfixed
  exact ⟨sigma, hsigma, ⟨fun n => Classical.choice (hsample n)⟩⟩

end CapSequenceStage

end PoincareConjecture.M44
