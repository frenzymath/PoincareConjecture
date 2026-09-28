import PoincareConjecture.Proofs.M10.EndpointCoordinates
import PoincareConjecture.Proofs.M10.SmoothMetric
import PoincareConjecture.Proofs.M10.ActionPotential









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}


noncomputable def coordinateScalarCurvature (F : RicciFlow n M J) (T : ℝ) (q₀ : M)
    (w : EuclideanSpace ℝ (Fin n) × ℝ) : ℝ :=
  (F.connection (T - w.2)).scalarCurvature ((extChartAt (𝓡 n) q₀).symm w.1)

set_option backward.isDefEq.respectTransparency false in

theorem coordinate_action_horizontal (G : LExponentialGeometry F T τmax p)
    (q₀ : M) (z : TangentSpace (𝓡 n) p × ℝ)
    (hz : z ∈ univ ×ˢ Ioo 0 τmax)
    (hq : G.gamma z.1 z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source)
    (h : TangentSpace (𝓡 n) p) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    fderiv ℝ (fun w : TangentSpace (𝓡 n) p × ℝ ↦
      G.toLExponentialFamily.action w.1 w.2) z (h, 0) =
        2 * Real.sqrt z.2 * coordinateBackwardMetric F T q₀
          (endpointCoordinates G q₀ z, z.2)
          (fderiv ℝ (endpointCoordinates G q₀) z (0, 1))
          (fderiv ℝ (endpointCoordinates G q₀) z (h, 0)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have hA := (G.action_smooth.contDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)).differentiableAt (by simp)
  rw [fderiv_horizontal_eq hA h,
    G.action_initial_differential z.1 z.2 hz.2.1 hz.2.2 h,
    endpointCoordinates_horizontal G q₀ z hz hq h,
    endpointCoordinates_time G q₀ z hz hq]
  dsimp only [coordinateBackwardMetric, endpointCoordinates]
  rw [(extChartAt (𝓡 n) q₀).left_inv (by simpa only [extChartAt_source] using hq),
    backwardMetricCoordinates_apply q₀ (G.gamma z.1 z.2, z.2) hq]

set_option backward.isDefEq.respectTransparency false in

theorem coordinate_action_time (G : LExponentialGeometry F T τmax p)
    (q₀ : M) (z : TangentSpace (𝓡 n) p × ℝ)
    (hz : z ∈ univ ×ˢ Ioo 0 τmax)
    (hq : G.gamma z.1 z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    fderiv ℝ (fun w : TangentSpace (𝓡 n) p × ℝ ↦
      G.toLExponentialFamily.action w.1 w.2) z (0, 1) =
        Real.sqrt z.2 *
          (coordinateScalarCurvature F T q₀ (endpointCoordinates G q₀ z, z.2) +
            coordinateBackwardMetric F T q₀ (endpointCoordinates G q₀ z, z.2)
              (fderiv ℝ (endpointCoordinates G q₀) z (0, 1))
              (fderiv ℝ (endpointCoordinates G q₀) z (0, 1))) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have hA := (G.action_smooth.contDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)).differentiableAt (by simp)
  have ht := (hasDerivAt_time_slice hA).unique
    (G.action_time_derivative z.1 z.2 hz.2.1 hz.2.2)
  rw [ht]
  unfold backwardLIntegrand
  rw [endpointCoordinates_time G q₀ z hz hq]
  dsimp only [coordinateScalarCurvature, coordinateBackwardMetric, endpointCoordinates]
  rw [(extChartAt (𝓡 n) q₀).left_inv (by simpa only [extChartAt_source] using hq),
    backwardMetricCoordinates_apply q₀ (G.gamma z.1 z.2, z.2) hq]

set_option backward.isDefEq.respectTransparency false in

theorem coordinateScalarCurvature_contDiffAt_of_noncritical
    (hwindow : Icc (T - τmax) T ⊆ J)
    (G : LExponentialGeometry F T τmax p)
    (z : TangentSpace (𝓡 n) p × ℝ) (hz : z ∈ univ ×ˢ Ioo 0 τmax)
    (hcrit : Function.Bijective (G.toLExponentialFamily.sliceDifferential z.1 z.2)) :
    ContDiffAt ℝ ∞ (coordinateScalarCurvature F T (G.gamma z.1 z.2))
      (extChartAt (𝓡 n) (G.gamma z.1 z.2) (G.gamma z.1 z.2), z.2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
  let q₀ := G.gamma z.1 z.2
  have hq : G.gamma z.1 z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source :=
    mem_chart_source _ _
  refine potential_contDiffAt_of_action (z₀ := z)
    (endpointCoordinates_contDiffAt G q₀ z hz hq)
    (G.action_smooth.contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz))
    (coordinateBackwardMetric_contDiffAt (F := F) hwindow q₀ hz.2.1 hz.2.2) hz.2.1
    (endpointCoordinates_horizontal_bijective G q₀ z hz hq hcrit) ?_
  have hγ := (G.gamma_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)).continuousAt
  filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds hz,
    hγ ((chartAt (EuclideanSpace ℝ (Fin n)) q₀).open_source.mem_nhds hq)] with w hw hqw
  exact coordinate_action_time G q₀ w hw hqw

end PoincareConjecture.M10
