import PoincareConjecture.Proofs.M03.Existence.FrameCoordinateJetNative









set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Manifold ContDiff Bundle BigOperators Topology

noncomputable section

universe u

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem chartMetricCoefficients_contDiffOn (g : RiemannianMetric n M)
    (p : M) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z => chartMetricCoefficients g p z i j)
      (extChartAt (𝓡 n) p).target := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hpair : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => g.inner y (chartFrame p i y) (chartFrame p j y))
      (chartAt E p).source :=
    (chartFrame_contMDiffOn p i).inner_bundle (chartFrame_contMDiffOn p j)
  have hcomp := hpair.comp (contMDiffOn_extChartAt_symm p)
    (fun z hz => show (extChartAt (𝓡 n) p).symm z ∈ (chartAt E p).source from
      by simpa only [extChartAt_source] using (extChartAt (𝓡 n) p).map_target hz)
  exact hcomp.contDiffOn

theorem chartMetricCoefficients_symm (g : RiemannianMetric n M)
    (p : M) (z : E) (i j : Fin n) :
    chartMetricCoefficients g p z i j = chartMetricCoefficients g p z j i :=
  g.symm _ _ _

theorem chartMetricCoefficients_posDef (g : RiemannianMetric n M)
    (p : M) {z : E} (hz : z ∈ (extChartAt (𝓡 n) p).target) :
    (chartMetricCoefficients g p z).PosDef := by
  have hy : (extChartAt (𝓡 n) p).symm z ∈ (chartAt E p).source := by
    simpa only [extChartAt_source] using (extChartAt (𝓡 n) p).map_target hz
  exact frameMetricJet_value_posDef g (chartFrame p) _ (chartFrameBasis p _ hy)
    (chartFrame_eq_basis p _ hy)

theorem chartMetricJet_second_spatial_comm (g : RiemannianMetric n M)
    (p : M) {z : E} (hz : z ∈ (extChartAt (𝓡 n) p).target)
    (a b i j : Fin n) :
    (coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n))
      (chartMetricCoefficients g p) z).second a b i j =
    (coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n))
      (chartMetricCoefficients g p) z).second b a i j := by
  exact coordinateMetricJet_second_spatial_comm _ _ (isOpen_extChartAt_target p)
    (chartMetricCoefficients_contDiffOn g p) hz a b i j

theorem chartMetricJet_second_metric_symm (g : RiemannianMetric n M)
    (p : M) {z : E} (hz : z ∈ (extChartAt (𝓡 n) p).target)
    (a b i j : Fin n) :
    (coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n))
      (chartMetricCoefficients g p) z).second a b i j =
    (coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n))
      (chartMetricCoefficients g p) z).second a b j i := by
  exact coordinateMetricJet_second_metric_symm _ _ (isOpen_extChartAt_target p)
    (chartMetricCoefficients_contDiffOn g p)
    (fun w _ => chartMetricCoefficients_symm g p w) hz a b i j

theorem ricciDeTurckSource_coordinateMetric_quasilinear
    (g : RiemannianMetric n M) (p : M) (background : MetricJet2 (n := n))
    {z : E} (hz : z ∈ (extChartAt (𝓡 n) p).target) (i j : Fin n) :
    ricciDeTurckSource background
        (coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n))
          (chartMetricCoefficients g p) z) i j =
      (∑ a, ∑ b, (chartMetricCoefficients g p z)⁻¹ a b *
        (coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n))
          (chartMetricCoefficients g p) z).second a b i j) +
        ricciDeTurckSource background
          (eraseSecondJet (coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n))
            (chartMetricCoefficients g p) z)) i j := by
  apply ricciDeTurckSource_quasilinear
  · exact Matrix.IsSymm.ext fun a b => chartMetricCoefficients_symm g p z b a
  · exact ne_of_gt (chartMetricCoefficients_posDef g p hz).det_pos
  · exact chartMetricJet_second_metric_symm g p hz
  · exact chartMetricJet_second_spatial_comm g p hz

end PoincareConjecture.DeTurckNative

end
