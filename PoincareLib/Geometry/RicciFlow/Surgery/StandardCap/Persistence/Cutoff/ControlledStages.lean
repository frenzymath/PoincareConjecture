import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Cutoff.PreparedCounterexamples
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Coordinates.SampleRestriction
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Controlled finite stages of the actual cap sequence

Every-fixed-radius control gives genuine growing-radius samples by
an explicit strictly increasing extraction. Their exact restricted
lifetimes preserve birth, curvature control and the comparison map.
Morgan--Tian, Lemma 16.8 and Corollary 16.9, pp. 372-373;
M44 derivations 98 and 104.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M44

variable {constants : MetricSurgeryConstants} {setup : SurgeryControlSetup constants}
  {start rNext A eta theta cutoff Rinner : ℝ}

/-- Actual outer-cylinder control through one time level of the
inner counterexample. Source: Lemma 16.8, pp. 372-373;
M44 derivation 104. -/
structure ControlledCapSample
    (X : PreparedCapCounterexample.{u} setup start rNext A eta theta cutoff Rinner)
    (R T K : ℝ) where
  /-- An actual maximal sample of the same physical cap. -/
  outer : MaximalCapSample setup.standard_initial X.data.flow X.data.time
    X.data.is_surgery X.data.cap X.data.assignedDuration
  /-- The fixed radius requested at this stage. -/
  radius_eq : outer.radius = R
  /-- The actual M36 tolerance is retained. -/
  eta_eq : outer.eta = X.sample.eta
  /-- The literal M36 comparison map is retained. -/
  comparison_eq : outer.comparison.map = X.sample.comparison.map
  /-- The outer cylinder survives through the controlled time level. -/
  survival : min X.sample.lifetime T ≤ outer.lifetime
  /-- The geometric curvature bound holds on its whole target. -/
  curvature : ∀ t ∈ Ico (0 : ℝ) (min X.sample.lifetime T), ∀ y,
    (outer.ordinary.flow.connection t).curvatureTensorNorm y ≤ K

namespace ControlledCapSample

variable {X : PreparedCapCounterexample.{u} setup start rNext A eta theta cutoff Rinner}
  {R T K : ℝ}

/-- Restrict to the exact controlled time level; no endpoint is
added. Source: Lemma 16.8, pp. 372-373; M44 derivation 104. -/
noncomputable def restricted (D : ControlledCapSample X R T K) (hT : 0 < T) :
    CylinderCompactnessSample setup.standard_initial X.data.flow X.data.time
      X.data.is_surgery X.data.cap :=
  D.outer.toCylinderCompactnessSample.restrictLifetime
    (lt_min X.sample.lifetime_pos hT) D.survival

/-- Lowering the time level or enlarging the common ceiling
preserves actual control. Source: Lemma 16.8, pp. 372-373;
M44 derivation 104. -/
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

/-- Every fixed outer radius eventually has an actual controlled
sample, with constants preceding the radius. Source: Lemma 16.8,
pp. 372-373; M44 derivation 104. -/
def CapSequenceStage {cutoffs : ℕ → ℝ}
    (X : ∀ n, PreparedCapCounterexample.{u} setup start rNext A eta theta (cutoffs n) Rinner)
    (R0 T K : ℝ) : Prop :=
  ∀ R : ℝ, R0 ≤ R → ∀ᶠ n in atTop, Nonempty (ControlledCapSample (X n) R T K)

namespace CapSequenceStage

variable {cutoffs : ℕ → ℝ}
  {X : ∀ n, PreparedCapCounterexample.{u} setup start rNext A eta theta (cutoffs n) Rinner}
  {R0 T K : ℝ}

/-- Every fixed-radius stage persists along any strictly increasing
subsequence. Source: Corollary 16.9, p. 373; M44 derivation 104. -/
theorem subsequence (h : CapSequenceStage X R0 T K) {sigma : ℕ → ℕ}
    (hsigma : StrictMono sigma) :
    CapSequenceStage (fun n => X (sigma n)) R0 T K :=
  fun R hR => hsigma.tendsto_atTop.eventually (h R hR)

/-- Increasing the minimum radius or curvature ceiling and lowering
the time level preserves a stage. Source: Lemma 16.8, pp. 372-373;
M44 derivation 104. -/
theorem mono (h : CapSequenceStage X R0 T K) {R1 T1 K1 : ℝ}
    (hR : R0 ≤ R1) (hT : T1 ≤ T) (hK : K ≤ K1) :
    CapSequenceStage X R1 T1 K1 := by
  intro R hRR
  filter_upwards [h R (hR.trans hRR)] with n hn
  exact hn.map fun D => D.mono hT hK

/-- Explicit extraction realizes growing radii from eventual
control on every fixed radius. Source: Corollary 16.9, p. 373;
M44 derivation 104. -/
theorem diagonal (h : CapSequenceStage X R0 T K) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      Nonempty (∀ n, ControlledCapSample (X (sigma n)) (R0 + (n : ℝ) + 1) T K) := by
  have hfixed (n : ℕ) : ∀ᶠ k in atTop,
      Nonempty (ControlledCapSample (X k) (R0 + (n : ℝ) + 1) T K) :=
    h _ (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  obtain ⟨sigma, hsigma, hsample⟩ := extraction_forall_of_eventually hfixed
  exact ⟨sigma, hsigma, ⟨fun n => Classical.choice (hsample n)⟩⟩

end CapSequenceStage

end PoincareMT.M44
