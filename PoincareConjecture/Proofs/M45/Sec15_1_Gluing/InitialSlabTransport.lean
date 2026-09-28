import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.InitialFlowExistence
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderEventSmooth
import PoincareConjecture.Proofs.M13.Volume
import PoincareConjecture.Proofs.M08.ActionBounds

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M45

theorem initialSlab_metric_eq (F : SurgeryFlowData.{u})
    (hunique : RicciFlowUniqueness 3 (F.slice 0).carrier)
    (G : RicciFlow 3 (F.slice 0).carrier (Icc 0 (1 / 16 : ℝ)))
    (hG : G.metric 0 = F.metric 0) {b : ℝ} (hb : b ≤ 1 / 16)
    (S : SurgeryRegularSlab F.slice F.metric 0 b) :
    EqOn S.flow.metric G.metric (Icc 0 b) := by
  have heq := hunique (Icc 0 b) (Icc 0 (1 / 16 : ℝ)) S.flow G
    ⟨⟨le_rfl, S.ordered.le⟩, fun _ ht => ht.1⟩
    ⟨by norm_num, fun _ ht => ht.1⟩
    ((M44.regularSlab_initial_metric F S).trans hG.symm)
  intro t ht
  exact heq ⟨ht, ht.1, ht.2.trans hb⟩

theorem initialSlab_curvature_eq (F : SurgeryFlowData.{u})
    (hunique : RicciFlowUniqueness 3 (F.slice 0).carrier)
    (G : RicciFlow 3 (F.slice 0).carrier (Icc 0 (1 / 16 : ℝ)))
    (hG : G.metric 0 = F.metric 0) {b : ℝ} (hb : b ≤ 1 / 16)
    (S : SurgeryRegularSlab F.slice F.metric 0 b) (t : Icc 0 b)
    (x : (F.slice 0).carrier) :
    (F.connection t.1).curvatureTensorNorm (S.identify t x) =
      (G.connection t.1).curvatureTensorNorm x := by
  have htransport := M13.homothety_curvatureTensorNorm_eq
    (S.flow.metric t.1) (F.metric t.1) (S.identify t) 1 zero_lt_one
    (M44.regularSlab_metricHomothety F S t)
    (S.flow.connection t.1) (F.connection t.1) x
  simpa only [div_one,
    curvatureNorm_eq_of_metric_eq (S.flow.connection t.1) (G.connection t.1)
      (initialSlab_metric_eq F hunique G hG hb S t.2)] using htransport

theorem initialSlab_ball_volume_eq (F : SurgeryFlowData.{u})
    (hunique : RicciFlowUniqueness 3 (F.slice 0).carrier)
    (G : RicciFlow 3 (F.slice 0).carrier (Icc 0 (1 / 16 : ℝ)))
    (hG : G.metric 0 = F.metric 0) {b : ℝ} (hb : b ≤ 1 / 16)
    (S : SurgeryRegularSlab F.slice F.metric 0 b) (t : Icc 0 b)
    (x : (F.slice 0).carrier) (r : ℝ) :
    calibratedMetricVolume (F.metric t.1) ((F.metric t.1).ball (S.identify t x) r) =
      calibratedMetricVolume (G.metric t.1) ((G.metric t.1).ball x r) := by
  have hhom := M44.regularSlab_metricHomothety F S t
  have hball := M13.homothety_ball_image (S.flow.metric t.1) (F.metric t.1)
    (S.identify t) 1 zero_lt_one hhom x r
  have hvolume := M13.homothety_volume_image (S.flow.metric t.1) (F.metric t.1)
    (S.identify t) 1 zero_lt_one hhom ((S.flow.metric t.1).ball x r)
  have hscale : Real.rpow 1 (((3 : ℕ) : ℝ) / 2) = 1 := Real.one_rpow _
  rw [hball] at hvolume
  rw [hscale, ENNReal.ofReal_one, one_mul] at hvolume
  simpa only [Real.sqrt_one, one_mul,
    initialSlab_metric_eq F hunique G hG hb S t.2] using hvolume

theorem scalar_le_eighteen_of_curvature_le_two
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (x : M)
    (h : D.curvatureTensorNorm x ≤ 2) : |D.scalarCurvature x| ≤ 18 := by
  have hs := M08.scalarCurvature_abs_le_tensorNorm D x
  norm_num at hs
  linarith

end PoincareConjecture.M45
