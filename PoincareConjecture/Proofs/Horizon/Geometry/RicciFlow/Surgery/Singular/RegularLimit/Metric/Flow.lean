import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.EndpointEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem terminalMetricFamily_ricci_of_ne
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {t : ℝ} (ht : t ≠ T) (x : H.regularRegion P04)
    (v w : TangentSpace (𝓡 3) x) :
    (H.terminalMetricFamily P04 t).leviCivitaData.ricci x v w =
      (H.reference.flow.connection t).ricci (x : M) v w := by
  have h := (H.terminalMetricFamily P04 t).leviCivitaData.ricci_eq_of_local_isometry
    (H.reference.flow.connection t) (f := Subtype.val) isOpen_univ
    ((Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) (H.regularRegion P04)).contMDiff.contMDiffOn)
    (fun y _ a b => by
      rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
      exact H.terminalMetricFamily_inner_of_ne P04 ht y a b)
    (mem_univ x) v w
  simp only [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal] at h
  exact h

def terminalFlow (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) :
    RicciFlow 3 (H.regularRegion P04) (Ioc H.reference.tMinus T) where
  metric := H.terminalMetricFamily P04
  connection t := (H.terminalMetricFamily P04 t).leviCivitaData
  interval := ordConnected_Ioc
  nontrivial := ⟨(2 * H.reference.tMinus + T) / 3,
    ⟨by linarith [H.reference.tMinus_lt], by linarith [H.reference.tMinus_lt]⟩,
    T, ⟨H.reference.tMinus_lt, le_rfl⟩, by linarith [H.reference.tMinus_lt]⟩
  smooth := H.terminalMetricFamily_isSmoothFamilyOn P04
  equation t ht x v w := by
    by_cases h : t = T
    · subst t
      have hRicci : (H.terminalMetricFamily P04 T).leviCivitaData.ricci x v w =
          (H.terminalConnection P04).ricci x v w :=
        congrArg (fun g : RiemannianMetric 3 (H.regularRegion P04) =>
          g.leviCivitaData.ricci x v w) (H.terminalMetricFamily_at_terminal P04)
      rw [hRicci]
      exact H.terminalMetricFamily_endpoint_equation P04 x v w
    · rw [H.terminalMetricFamily_ricci_of_ne P04 h]
      exact (H.terminalMetricFamily_hasDerivAt_of_lt P04
        ⟨ht.1, lt_of_le_of_ne ht.2 h⟩ x v w).hasDerivWithinAt

theorem terminalFlow_metric_at_terminal
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u}) :
    (H.terminalFlow P04).metric T = H.terminalMetric P04 :=
  H.terminalMetricFamily_at_terminal P04

theorem terminalFlow_metric_of_lt
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {t : ℝ} (ht : t < T) :
    (H.terminalFlow P04).metric t =
      (H.reference.flow.restrictToOpen (H.regularRegion P04)).metric t :=
  H.terminalMetricFamily_of_ne P04 (ne_of_lt ht)

end PoincareConjecture.SingularTimeAssumptions
