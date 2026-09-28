import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.BasedComponent
import PoincareConjecture.Proofs.M30.Thm11_1.TerminalDerivatives
import PoincareConjecture.Proofs.M30.Thm11_1.TerminalVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable


noncomputable def terminalComponentCarrier (S : GeneralizedBlowupSequence.{u}) (k : ℕ) :
    FlowCarrier.{u} 3 :=
  basedSliceCarrier ((S.flow k).slice (S.base k).1) (S.base k).2


def terminalComponentBase (S : GeneralizedBlowupSequence.{u}) (k : ℕ) :
    (terminalComponentCarrier S k).carrier :=
  ⟨(S.base k).2, mem_connectedComponent⟩



noncomputable def terminalComponentMetric (S : GeneralizedBlowupSequence.{u}) (k : ℕ) :
    (terminalComponentCarrier S k).metric :=
  basedSliceMetric ((S.flow k).slice (S.base k).1) (S.base k).2
    (M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
      (S.scale k) (S.base_scalar_pos k))



theorem terminalComponentMetric_image_ball (S : GeneralizedBlowupSequence.{u})
    (k : ℕ) (A : ℝ) :
    Subtype.val '' (terminalComponentMetric S k).ball (terminalComponentBase S k) A =
      S.baseBall k A := by
  exact (basedSliceMetric_image_ball ((S.flow k).slice (S.base k).1) (S.base k).2
    _ (terminalComponentBase S k) A).trans (scaled_terminal_ball_eq_baseBall S k A)



theorem eventually_terminalComponent_compact_ball
    {S : GeneralizedBlowupSequence.{u}} {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (A : ℝ) (hA : 0 < A) :
    ∀ᶠ k in atTop,
      IsCompact (closure ((terminalComponentMetric S k).ball (terminalComponentBase S k) A)) := by
  filter_upwards [H.balls_compact A hA] with k hk
  apply basedSliceMetric_isCompact_closure_ball
  simpa only [terminalComponentBase, scaled_terminal_ball_eq_baseBall] using hk



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

end PoincareConjecture.M30
