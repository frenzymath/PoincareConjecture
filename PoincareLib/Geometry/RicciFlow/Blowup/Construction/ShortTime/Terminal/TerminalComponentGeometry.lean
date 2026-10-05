import PoincareLib.Geometry.RicciFlow.Blowup.Construction.PartialLimits.BasedComponent
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.Terminal.TerminalDerivatives
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.Terminal.TerminalVolume
import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration

/-!
# The actual terminal component supplies static compactness geometry

Morgan--Tian Corollary 11.4 and Claim 11.5, p. 270. On the basepoint
component of each scaled terminal slice, compact balls, curvature
derivative bounds and a fixed positive base volume are inherited from the
generalized source. The bounds remain local in radius and derivative order.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

/-- The connected terminal component used in Claim 11.5, p. 270. -/
noncomputable def terminalComponentCarrier (S : GeneralizedBlowupSequence.{u}) (k : ℕ) :
    FlowCarrier.{u} 3 :=
  basedSliceCarrier ((S.flow k).slice (S.base k).1) (S.base k).2

/-- The original basepoint in its terminal component (Claim 11.5, p. 270). -/
def terminalComponentBase (S : GeneralizedBlowupSequence.{u}) (k : ℕ) :
    (terminalComponentCarrier S k).carrier :=
  ⟨(S.base k).2, mem_connectedComponent⟩

/-- The scaled terminal metric restricted to the actual basepoint component
(Definition 3.40 and Claim 11.5, pp. 61 and 270). -/
noncomputable def terminalComponentMetric (S : GeneralizedBlowupSequence.{u}) (k : ℕ) :
    (terminalComponentCarrier S k).metric :=
  basedSliceMetric ((S.flow k).slice (S.base k).1) (S.base k).2
    (M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
      (S.scale k) (S.base_scalar_pos k))

/-- Actual component balls project onto the frozen normalized source balls
(Claim 11.5, p. 270). -/
theorem terminalComponentMetric_image_ball (S : GeneralizedBlowupSequence.{u})
    (k : ℕ) (A : ℝ) :
    Subtype.val '' (terminalComponentMetric S k).ball (terminalComponentBase S k) A =
      S.baseBall k A := by
  exact (basedSliceMetric_image_ball ((S.flow k).slice (S.base k).1) (S.base k).2
    _ (terminalComponentBase S k) A).trans (scaled_terminal_ball_eq_baseBall S k A)

/-- Each fixed component ball eventually has compact closure
(Claim 11.5 and Theorem 5.9, pp. 270 and 88--89). -/
theorem eventually_terminalComponent_compact_ball
    {S : GeneralizedBlowupSequence.{u}} {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (A : ℝ) (hA : 0 < A) :
    ∀ᶠ k in atTop,
      IsCompact (closure ((terminalComponentMetric S k).ball (terminalComponentBase S k) A)) := by
  filter_upwards [H.balls_compact A hA] with k hk
  apply basedSliceMetric_isCompact_closure_ball
  simpa only [terminalComponentBase, scaled_terminal_ball_eq_baseBall] using hk

/-- Every fixed radius and covariant derivative order have an eventual
uniform bound on the actual component (Corollary 11.4, p. 270). -/
theorem eventually_terminalComponent_curvatureDerivativeNorm_le
    (hC : RicciFlowCurvatureTheory.{u}) {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (hbound : GeneralizedBlowupBoundedDistance S) (A : ℝ) (hA : 0 < A) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k in atTop,
      ∀ x ∈ (terminalComponentMetric S k).ball (terminalComponentBase S k) A,
        (terminalComponentMetric S k).leviCivitaData.curvatureDerivativeNorm m x ≤ D := by
  obtain ⟨D, hD, htail⟩ := eventually_terminal_curvatureDerivativeNorm_le hC H hbound A hA m
  refine ⟨D, hD, htail.mono fun k hk x hx => ?_⟩
  have hx' : x.val ∈ S.baseBall k A := by
    rw [← terminalComponentMetric_image_ball S k A]
    exact mem_image_of_mem Subtype.val hx
  let g : RiemannianMetric 3 ((S.flow k).slice (S.base k).1).carrier :=
    M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
      (S.scale k) (S.base_scalar_pos k)
  exact (basedSliceMetric_curvatureDerivativeNorm ((S.flow k).slice (S.base k).1)
    (S.base k).2 g g.leviCivitaData m x).trans_le (hk x.val hx')

/-- One fixed positive base radius and volume lower bound hold on the
actual component before extraction (Claim 11.5, p. 270). -/
theorem exists_eventually_terminalComponent_volume_lower_bound
    (hC : RicciFlowCurvatureTheory.{u}) {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (hbound : GeneralizedBlowupBoundedDistance S) :
    ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ k in atTop,
      ENNReal.ofReal v ≤ (terminalComponentMetric S k).volumeMeasure
        ((terminalComponentMetric S k).ball (terminalComponentBase S k) rho) := by
  obtain ⟨rho, v, hrho, hv, htail⟩ :=
    exists_eventually_scaled_terminal_volume_lower_bound hC H hbound
  refine ⟨rho, v, hrho, hv, htail.mono fun k hk => ?_⟩
  rw [calibratedMetricVolume_eq_volumeMeasure] at hk
  exact hk.trans_eq (basedSliceMetric_volume_ball ((S.flow k).slice (S.base k).1)
    (S.base k).2 (M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
      (S.scale k) (S.base_scalar_pos k)) (terminalComponentBase S k) rho).symm

end PoincareMT.M30
