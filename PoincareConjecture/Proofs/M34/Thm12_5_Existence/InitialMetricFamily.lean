import PoincareConjecture.Proofs.M34.Thm12_5_Existence.InitialEndpointEvolution
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.Coordinates










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.InteriorCoefficientLimit

open SpacetimeBounds

variable {g0 : StandardInitialMetric} {A : CompactCapApproximation g0}
  (G : InteriorCoefficientLimit A)



theorem closedCoefficients_symm (t : ℝ) (x u v : StandardCapSpace) :
    G.closedCoefficients (t, x) u v = G.closedCoefficients (t, x) v u := by
  by_cases ht : t ∈ Ioo 0 A.time
  · simpa only [G.closedCoefficients_of_mem ht] using G.coefficients_symm ht x u v
  · simp only [closedCoefficients, ht, if_false]
    convert! g0.metric.symm x u v



theorem closedCoefficients_pos (P : RicciFlowCurvatureTheory.{0})
    (t : ℝ) (x v : StandardCapSpace) (hv : v ≠ 0) :
    0 < G.closedCoefficients (t, x) v v := by
  by_cases ht : t ∈ Ioo 0 A.time
  · simpa only [G.closedCoefficients_of_mem ht] using G.coefficients_pos P ht x v hv
  · simp only [closedCoefficients, ht, if_false]
    convert! g0.metric.pos x v hv



noncomputable def limitMetricConnection (P : RicciFlowCurvatureTheory.{0}) (t : ℝ) :
    Σ g : RiemannianMetric 3 StandardCapSpace, LeviCivitaData g :=
  if t ∈ Ioo 0 A.time then
    let g := RiemannianMetric.ofEuclideanCoefficients
      (fun x => G.closedCoefficients (t, x)) (G.contDiff_closedCoefficients_slice t)
      (G.closedCoefficients_symm t) (G.closedCoefficients_pos P t)
    ⟨g, g.euclideanLeviCivitaData⟩
  else ⟨g0.metric, g0.connection⟩



noncomputable def limitMetric (P : RicciFlowCurvatureTheory.{0}) (t : ℝ) :
    RiemannianMetric 3 StandardCapSpace := (G.limitMetricConnection P t).1



noncomputable def limitConnection (P : RicciFlowCurvatureTheory.{0}) (t : ℝ) :
    LeviCivitaData (G.limitMetric P t) := (G.limitMetricConnection P t).2



theorem limitMetric_coefficients (P : RicciFlowCurvatureTheory.{0}) (t : ℝ) :
    (G.limitMetric P t).euclideanCoefficients = fun x => G.closedCoefficients (t, x) := by
  by_cases ht : t ∈ Ioo 0 A.time
  · simp only [limitMetric, limitMetricConnection, ht, if_true]
    rfl
  · simp only [limitMetric, limitMetricConnection, ht, if_false, closedCoefficients]


theorem limitMetric_zero (P : RicciFlowCurvatureTheory.{0}) :
    G.limitMetric P 0 = g0.metric := by
  simp [limitMetric, limitMetricConnection]



theorem limitConnection_zero (P : RicciFlowCurvatureTheory.{0}) :
    HEq (G.limitConnection P 0) g0.connection := by
  have hpair : G.limitMetricConnection P 0 = ⟨g0.metric, g0.connection⟩ := by
    simp [limitMetricConnection]
  exact (Sigma.mk.inj_iff.mp hpair).2



theorem limitMetric_smooth (P : RicciFlowCurvatureTheory.{0}) :
    RiemannianMetric.IsSmoothFamilyOn (G.limitMetric P) (Ico 0 A.time) := by
  apply RiemannianMetric.isSmoothFamilyOn_of_constant_chart (fun _ _ => rfl)
    (G.limitMetric P) G.closedCoefficients
  · have hmap : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ × StandardCapSpace) ∞
        (fun p : ℝ × StandardCapSpace => (p.1, p.2)) :=
      contMDiff_fst.prodMk_space contMDiff_snd
    exact (G.contDiffOn_closedCoefficients P).contMDiffOn.comp hmap.contMDiffOn
      (fun _ hp => hp)
  · intro t _ht x u v
    exact congrArg (fun B => B x u v) (G.limitMetric_coefficients P t)

end PoincareConjecture.M34.InteriorCoefficientLimit
