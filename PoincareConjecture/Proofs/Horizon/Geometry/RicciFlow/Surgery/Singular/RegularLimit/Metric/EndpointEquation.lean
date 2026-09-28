import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.Ricci
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.TimeFamily
import Mathlib.Analysis.Calculus.FDeriv.Extend

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem terminalMetricFamily_inner_of_ne
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {t : ℝ} (ht : t ≠ T) (x : H.regularRegion P04)
    (v w : TangentSpace (𝓡 3) x) :
    (H.terminalMetricFamily P04 t).inner x v w =
      (H.reference.flow.metric t).inner (x : M) v w := by
  rw [H.terminalMetricFamily_of_ne P04 ht, RicciFlow.restrictToOpen_inner,
    Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
  rfl

theorem terminalMetricFamily_hasDerivAt_of_lt
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {t : ℝ} (ht : t ∈ Ioo H.reference.tMinus T)
    (x : H.regularRegion P04) (v w : TangentSpace (𝓡 3) x) :
    HasDerivAt (fun s => (H.terminalMetricFamily P04 s).inner x v w)
      (-2 * (H.reference.flow.connection t).ricci (x : M) v w) t := by
  apply ((H.reference.flow.equation t ⟨ht.1.le, ht.2⟩ (x : M) v w).hasDerivAt
    (Ico_mem_nhds_iff.mpr ht)).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ht.2] with s hs
  exact H.terminalMetricFamily_inner_of_ne P04 (ne_of_lt hs) x v w

theorem terminalMetricFamily_endpoint_equation
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04) (v w : TangentSpace (𝓡 3) x) :
    HasDerivWithinAt (fun s => (H.terminalMetricFamily P04 s).inner x v w)
      (-2 * (H.terminalConnection P04).ricci x v w) (Ioc H.reference.tMinus T) T := by
  let f : ℝ → ℝ := fun s => (H.terminalMetricFamily P04 s).inner x v w
  have hlimit : Tendsto f (𝓝[<] T) (𝓝 (f T)) := by
    have h := H.tendsto_terminalMetricBilinear_apply P04 x.property v w
    have heq : f =ᶠ[𝓝[<] T] (fun t => (H.reference.flow.metric t).inner (x : M) v w) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact H.terminalMetricFamily_inner_of_ne P04 (ne_of_lt ht) x v w
    have hT : f T = H.terminalMetricBilinear P04 x.property v w := by
      dsimp only [f]
      rw [H.terminalMetricFamily_at_terminal P04]
      rfl
    rw [hT]
    exact h.congr' heq.symm
  have hderiv : Tendsto (deriv f) (𝓝[<] T)
      (𝓝 (-2 * (H.terminalConnection P04).ricci x v w)) := by
    have h := (tendsto_const_nhds (x := (-2 : ℝ))).mul
      (H.tendsto_terminal_ricci P04 x v w)
    apply h.congr'
    filter_upwards [Ioo_mem_nhdsLT H.reference.tMinus_lt] with t ht
    exact (H.terminalMetricFamily_hasDerivAt_of_lt P04 ht x v w).deriv.symm
  exact (hasDerivWithinAt_Iic_of_tendsto_deriv
    (fun t ht => (H.terminalMetricFamily_hasDerivAt_of_lt P04 ht x v w).differentiableAt.differentiableWithinAt)
    (hlimit.mono_left (nhdsWithin_mono T Ioo_subset_Iio_self))
    (Ioo_mem_nhdsLT H.reference.tMinus_lt) hderiv).mono Ioc_subset_Iic_self

end PoincareConjecture.SingularTimeAssumptions
