import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.TimeDerivative
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.IndexedCovering

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture

namespace NormalChartCover

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : ℝ → RiemannianMetric n M} {p : M} {T' T A R ρ a b : ℝ} {N : ℕ}

theorem image_mem_zeroBall
    (C : NormalChartCover g p T' T A R ρ a b N)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (i : Fin (N + 1))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball 0 R) :
    C.chart i x ∈ (g 0).ball p (A + R) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(g 0).toRiemannianMetric⟩
  have hxp : C.chart i x ∈ (g 0).ball (C.centre i) R := by
    rw [← C.target i]
    exact (C.chart i).map_source ((C.source i).symm ▸ hx)
  change (g 0).edist p (C.chart i x) < ENNReal.ofReal (A + R)
  rw [ENNReal.ofReal_add hA hR]
  exact Manifold.riemannianEDist_triangle.trans_lt
    (ENNReal.add_lt_add (C.centre_mem i) hxp)

theorem norm_pullbackCoefficients_le
    (C : NormalChartCover g p T' T A R ρ a b N) (hb : 0 ≤ b)
    (i : Fin (N + 1)) {t : ℝ} (ht : t ∈ Ioo T' T)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.closedBall 0 (2 * ρ)) :
    ‖(g t).pullbackCoefficients (C.chart i) x‖ ≤ b := by
  apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ hb
  · intro u v
    exact (g t).symm _ _ _
  · intro v
    have hnonneg : 0 ≤ (g t).pullbackCoefficients (C.chart i) x v v := by
      let w := mfderiv (𝓡 n) (𝓡 n) (C.chart i) x v
      change 0 ≤ (g t).inner (C.chart i x) w w
      by_cases hw : w = 0
      · simp [hw]
      · exact ((g t).pos _ _ hw).le
    rw [abs_of_nonneg hnonneg]
    exact (C.coefficients i t ht x hx v).2

end NormalChartCover

namespace PointedRicciFlowCompactnessHypotheses

theorem eventually_normalChartCover_time_derivative_bound
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    {A R ρ a b : ℝ} {N : ℕ} (hA : 0 < A) (hρ : 0 < ρ)
    (hρR : 2 * ρ < R) (hb : 0 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ cover : NormalChartCover F.metricAt F.base T' T A R ρ a b N,
        ∀ i, ∀ t ∈ Ioo T' T, ∀ x ∈ Metric.closedBall 0 (2 * ρ),
          ‖deriv (fun s => (F.metricAt s).pullbackCoefficients (cover.chart i) x) t‖ ≤ B := by
  have hR : 0 < R := lt_trans (by positivity : 0 < 2 * ρ) hρR
  obtain ⟨K, hK, hcurv⟩ := H.all_time_curvature_control_on_zero_ball (A + R) (by positivity)
  refine ⟨2 * (n : ℝ) ^ 3 * K * b, by positivity, ?_⟩
  filter_upwards [hcurv] with k hk
  let C := H.sequence.carrier k
  let F := H.sequence.flow k
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : T2Space C.carrier := C.t2Space
  dsimp only
  intro cover i t ht x hx
  have hx' : x ∈ Metric.ball 0 R := Metric.closedBall_subset_ball hρR hx
  apply F.flow.norm_deriv_pullbackCoefficients_le isOpen_Ioo Metric.isOpen_ball
    (by simpa only [cover.source i] using (cover.chart i).contMDiffOn)
    ht hx' hb hK
  · intro v
    exact (cover.coefficients i t ht x hx v).2
  · exact hk t ht _ (cover.image_mem_zeroBall hA.le hR.le i hx')

theorem eventually_normalChartCover_time_lipschitz_bound
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    {A R ρ a b : ℝ} {N : ℕ} (hA : 0 < A) (hρ : 0 < ρ)
    (hρR : 2 * ρ < R) (hb : 0 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ cover : NormalChartCover F.metricAt F.base T' T A R ρ a b N,
        ∀ i, ∀ s ∈ Ioo T' T, ∀ t ∈ Ioo T' T, ∀ x ∈ Metric.closedBall 0 (2 * ρ),
          ‖(F.metricAt t).pullbackCoefficients (cover.chart i) x -
            (F.metricAt s).pullbackCoefficients (cover.chart i) x‖ ≤ B * |t - s| := by
  obtain ⟨B, hB, hbound⟩ := H.eventually_normalChartCover_time_derivative_bound
    (a := a) (N := N) hA hρ hρR hb
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound] with k hk
  let C := H.sequence.carrier k
  let F := H.sequence.flow k
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  dsimp only
  intro cover i s hs t ht x hx
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (cover.chart i) (Metric.ball 0 R) := by
    simpa only [cover.source i] using (cover.chart i).contMDiffOn
  have hdiff : ∀ u ∈ Ioo T' T,
      DifferentiableAt ℝ (fun s => (F.metricAt s).pullbackCoefficients (cover.chart i) x) u := by
    intro u hu
    exact F.flow.differentiableAt_pullbackCoefficients_time isOpen_Ioo Metric.isOpen_ball
      he hu (Metric.closedBall_subset_ball hρR hx)
  have hderiv : ∀ u ∈ Ioo T' T,
      ‖deriv (fun s => (F.metricAt s).pullbackCoefficients (cover.chart i) x) u‖ ≤ B :=
    fun u hu => hk cover i u hu x hx
  simpa only [Real.norm_eq_abs] using
    (convex_Ioo T' T).norm_image_sub_le_of_norm_deriv_le hdiff hderiv hs ht

end PointedRicciFlowCompactnessHypotheses
end PoincareConjecture
