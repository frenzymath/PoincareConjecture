import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.Terminal
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.Family
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Coordinates.SpacetimeLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Restriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set Filter Manifold
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

def terminalMetricFamily (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (t : ℝ) :
    RiemannianMetric 3 (H.regularRegion P04) :=
  if t = T then H.terminalMetric P04
  else (H.reference.flow.restrictToOpen (H.regularRegion P04)).metric t

@[simp] theorem terminalMetricFamily_at_terminal (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) :
    H.terminalMetricFamily P04 T = H.terminalMetric P04 := by
  simp [terminalMetricFamily]

theorem terminalMetricFamily_of_ne (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {t : ℝ} (ht : t ≠ T) :
    H.terminalMetricFamily P04 t =
      (H.reference.flow.restrictToOpen (H.regularRegion P04)).metric t := by
  simp only [terminalMetricFamily, if_neg ht]

theorem terminalMetricFamily_chartCoefficients_eqOn
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (q : H.regularRegion P04) (p : ℝ × EuclideanSpace ℝ (Fin 3))
    (hp : p.2 ∈ (extChartAt (𝓡 3) q).target) :
    (H.terminalMetricFamily P04 p.1).pullbackCoefficients
        (extChartAt (𝓡 3) q).symm p.2 =
      H.extendedCoordinateCoefficients P04 (q : M) p := by
  by_cases ht : p.1 = T
  · simp only [terminalMetricFamily, extendedCoordinateCoefficients, ht]
    exact H.regularRegion_chartCoefficients_eqOn P04 q hp
  · rw [H.terminalMetricFamily_of_ne P04 ht]
    simp only [extendedCoordinateCoefficients, if_neg ht]
    ext v w
    change ((H.reference.flow.restrictToOpen (H.regularRegion P04)).metric p.1).inner
      ((extChartAt (𝓡 3) q).symm p.2)
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm p.2 v)
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm p.2 w) = _
    rw [RicciFlow.restrictToOpen_inner,
      Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
    change (H.reference.flow.metric p.1).inner ((extChartAt (𝓡 3) q).symm p.2 : M)
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm p.2 v)
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm p.2 w) =
      (H.reference.flow.metric p.1).inner ((extChartAt (𝓡 3) (q : M)).symm p.2)
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (q : M)).symm p.2 v)
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (q : M)).symm p.2 w)
    rw [H.regularRegion_chart_inverse P04 q hp, H.regularRegion_chart_mfderiv P04 q hp]
    rfl

theorem terminalMetricFamily_isSmoothFamilyOn
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u}) :
    RiemannianMetric.IsSmoothFamilyOn (H.terminalMetricFamily P04)
      (Ioc H.reference.tMinus T) := by
  apply SingularRegularLimit.isSmoothFamilyOn_of_chartCoefficients
  intro t ht q
  let p := extChartAt (𝓡 3) q q
  by_cases htT : t = T
  · subst t
    obtain ⟨s, r, _, hsT, hr, _, _, hcoeff⟩ :=
      H.exists_smooth_terminal_spacetime_coordinates P04 q.property
    have hpoint : (T, p) ∈ Ioc s T ×ˢ Metric.ball (extChartAt (𝓡 3) (q : M) q) r :=
      ⟨⟨hsT, le_rfl⟩, Metric.mem_ball_self hr⟩
    have hlocal : Ioc s T ×ˢ Metric.ball (extChartAt (𝓡 3) (q : M) q) r ∈
        𝓝[Ioc H.reference.tMinus T ×ˢ univ] (T, p) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds
          (continuousAt_fst.preimage_mem_nhds (Ioi_mem_nhds hsT)),
        mem_nhdsWithin_of_mem_nhds
          (continuousAt_snd.preimage_mem_nhds (Metric.ball_mem_nhds p hr))]
        with z hz hzs hzr
      exact ⟨⟨hzs, hz.1.2⟩, hzr⟩
    apply ((hcoeff (T, p) hpoint).mono_of_mem_nhdsWithin hlocal).congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds
        (continuousAt_snd.preimage_mem_nhds (extChartAt_target_mem_nhds (I := 𝓡 3) q))]
        with z hz
      exact H.terminalMetricFamily_chartCoefficients_eqOn P04 q z hz
    · exact H.terminalMetricFamily_chartCoefficients_eqOn P04 q (T, p)
        (mem_extChartAt_target q)
  · have htlt : t < T := lt_of_le_of_ne ht.2 htT
    let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow
      (H.reference.flow.restrictToOpen (H.regularRegion P04))
      (Ioo_subset_Ico_self : Ioo H.reference.tMinus T ⊆ Ico H.reference.tMinus T)
      ordConnected_Ioo ⟨t, ⟨ht.1, htlt⟩, (t + T) / 2,
        ⟨by linarith [ht.1], by linarith⟩, by linarith⟩
    have hsmooth := G.contDiffOn_pullbackCoefficients isOpen_Ioo
      (isOpen_extChartAt_target q) (contMDiffOn_extChartAt_symm q)
    have hpoint : (t, p) ∈ Ioo H.reference.tMinus T ×ˢ (extChartAt (𝓡 3) q).target :=
      ⟨⟨ht.1, htlt⟩, mem_extChartAt_target q⟩
    apply ContDiffAt.contDiffWithinAt
    apply (hsmooth.contDiffAt
      ((isOpen_Ioo.prod (isOpen_extChartAt_target q)).mem_nhds hpoint)).congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.preimage_mem_nhds (Iio_mem_nhds htlt)] with z hz
    rw [H.terminalMetricFamily_of_ne P04 (ne_of_lt hz)]
    rfl

end PoincareConjecture.SingularTimeAssumptions
