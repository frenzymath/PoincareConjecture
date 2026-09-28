import PoincareConjecture.Proofs.M10.BranchODE
import PoincareConjecture.Proofs.M10.CoordinateAction
import PoincareConjecture.Proofs.M10.MetricPositive









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem noncritical_branch_solves
    (hwindow : Icc (T - τmax) T ⊆ J) (G : LExponentialGeometry F T τmax p)
    (q₀ : M) (z : TangentSpace (𝓡 n) p × ℝ)
    (hz : z ∈ univ ×ˢ Ioo 0 τmax) (hend : G.gamma z.1 z.2 = q₀)
    (hcrit : Function.Bijective (G.toLExponentialFamily.sliceDifferential z.1 z.2)) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    ∀ᶠ t in 𝓝 z.2,
      HasDerivAt
        (actionBranchPhase (endpointCoordinates G q₀) (coordinateBackwardMetric F T q₀) z.1)
        (phaseField (coordinateBackwardMetric F T q₀) (coordinateScalarCurvature F T q₀)
          (actionBranchPhase (endpointCoordinates G q₀)
            (coordinateBackwardMetric F T q₀) z.1 t)) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
  subst q₀
  let q := G.gamma z.1 z.2
  have hq : G.gamma z.1 z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source :=
    mem_chart_source _ _
  have htarget : extChartAt (𝓡 n) q q ∈ (extChartAt (𝓡 n) q).target :=
    (extChartAt (𝓡 n) q).map_source (mem_extChartAt_source q)
  have hB := coordinateBackwardMetric_contDiffAt (F := F) hwindow q hz.2.1 hz.2.2
  have hR := coordinateScalarCurvature_contDiffAt_of_noncritical hwindow G z hz hcrit
  have hγ := (G.gamma_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)).continuousAt
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ univ ×ˢ Ioo 0 τmax ∧
      G.gamma w.1 w.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds hz,
      hγ ((chartAt (EuclideanSpace ℝ (Fin n)) q).open_source.mem_nhds hq)]
      with w hw hwq
    exact ⟨hw, hwq⟩
  apply eventually_hasDerivAt_actionBranchPhase
    (A := fun w ↦ G.toLExponentialFamily.action w.1 w.2)
    (endpointCoordinates_contDiffAt G q z hz hq)
    (G.action_smooth.contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz))
    hB hR hz.2.1 (coordinateBackwardMetric_isInvertible q _ htarget)
  · filter_upwards [continuous_fst.continuousAt
      (extChartAt_target_mem_nhds (I := 𝓡 n) q)] with w hw
    exact coordinateBackwardMetric_symm q w hw
  · filter_upwards [hnear] with w hw
    exact coordinate_action_horizontal G q w hw.1 hw.2
  · filter_upwards [hnear] with w hw
    exact coordinate_action_time G q w hw.1 hw.2
  · exact endpointCoordinates_horizontal_bijective G q z hz hq hcrit

end PoincareConjecture.M10
