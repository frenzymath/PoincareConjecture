import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.Flow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Tensor.FlowRiemannRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem terminalFlow_curvatureTensor_of_ne
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {t : ℝ} (ht : t ≠ T) (x : H.regularRegion P04)
    (u v w z : TangentSpace (𝓡 3) x) :
    ((H.terminalFlow P04).connection t).curvatureTensor x u v w z =
      (H.reference.flow.connection t).curvatureTensor (x : M) u v w z := by
  have h := ((H.terminalFlow P04).connection t).curvatureTensor_eq_of_local_isometry
    (H.reference.flow.connection t) (f := Subtype.val) isOpen_univ
    ((contMDiff_subtype_val (n := ∞)).contMDiffOn)
    (fun y _ a b => by
      rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
      exact H.terminalMetricFamily_inner_of_ne P04 ht y a b)
    (mem_univ x) u v w z
  simp only [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal] at h
  exact h

theorem terminalFlow_curvatureTensor_at_terminal
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04) (u v w z : TangentSpace (𝓡 3) x) :
    ((H.terminalFlow P04).connection T).curvatureTensor x u v w z =
      (H.terminalConnection P04).curvatureTensor x u v w z :=
  congrArg (fun g : RiemannianMetric 3 (H.regularRegion P04) =>
    g.leviCivitaData.curvatureTensor x u v w z) (H.terminalMetricFamily_at_terminal P04)

theorem tendsto_terminal_curvatureTensor
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04) (u v w z : TangentSpace (𝓡 3) x) :
    Tendsto (fun t => (H.reference.flow.connection t).curvatureTensor (x : M) u v w z)
      (𝓝[<] T) (𝓝 ((H.terminalConnection P04).curvatureTensor x u v w z)) := by
  have hc := (RicciFlowAnalysis.contDiffOn_curvatureTensor_timeSlice
    (H.terminalFlow P04) x u v w z).continuousOn T ⟨H.reference.tMinus_lt, le_rfl⟩
  have hfilter : 𝓝[<] T ≤ 𝓝[Ioc H.reference.tMinus T] T :=
    nhdsWithin_le_of_mem (Ioc_mem_nhdsLT H.reference.tMinus_lt)
  have h := hc.tendsto.mono_left hfilter
  rw [H.terminalFlow_curvatureTensor_at_terminal P04] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact H.terminalFlow_curvatureTensor_of_ne P04 (ne_of_lt ht) x u v w z

end PoincareConjecture.SingularTimeAssumptions
