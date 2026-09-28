import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.SpatialEvolution
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Gronwall
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.NormalCharts
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.InteriorDerivativeControl










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.PointedRicciFlowCompactnessHypotheses

theorem eventually_normalChartCover_spatial_bounds_on_interval_of_local_derivative_estimates
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hShi : LocalCurvatureDerivativeEstimates.{0})
    {l r : ℝ} (h0 : (0 : ℝ) ∈ Icc l r) (hJ : Icc l r ⊆ Ioo T' T)
    {A R ρ a b : ℝ} {N : ℕ} (hA : 0 < A) (hρ : 0 < ρ)
    (hρR : 2 * ρ < R) (ha : 0 < a) (hb : 0 ≤ b) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ cover : NormalChartCover F.metricAt F.base T' T A R ρ a b N,
        ∀ i, ∀ t ∈ Icc l r, ∀ x ∈ Metric.closedBall 0 ρ, ∀ j ≤ m,
          ‖iteratedFDeriv ℝ j ((F.metricAt t).pullbackCoefficients (cover.chart i)) x‖ ≤ B := by
  have hR : 0 < R := lt_trans (by positivity : 0 < 2 * ρ) hρR
  induction m with
  | zero =>
      refine ⟨b, hb, Filter.Eventually.of_forall ?_⟩
      intro k
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      let : TopologicalSpace C.carrier := C.topologicalSpace
      let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      dsimp only
      intro cover i t ht x hx j hj
      have hj0 : j = 0 := by omega
      subst j
      rw [norm_iteratedFDeriv_zero]
      exact cover.norm_pullbackCoefficients_le hb i (hJ ht)
        (Metric.closedBall_subset_closedBall (by linarith) hx)
  | succ q ih =>
      obtain ⟨B, hB, hlower⟩ := ih
      let D : ℝ := max B 1
      have hD : 1 ≤ D := le_max_right _ _
      choose K hK hcurv using fun s =>
        H.eventually_compact_curvatureDerivativeNorm_le_of_local_derivative_estimates
          hShi isCompact_Icc hJ (A + R) (by positivity) s
      obtain ⟨C, hC, hevol⟩ := SpacetimeBounds.exists_affine_spatialJet_evolution_bound
        n q K (fun s => (hK s).le) ha hb D hD
      obtain ⟨Z, hZ, hinit⟩ :=
        H.eventually_normalChartCover_metric_jet_bound_of_local_derivative_estimates hShi
          (R := R) (a := a) (b := b) (N := N) hA hρ (by linarith) (q + 1)
      let E : ℝ := max Z 1 * Real.exp ((C + C) * (|T'| + |T|))
      have hE : 0 ≤ E := by dsimp [E]; positivity
      refine ⟨max B E, le_max_of_le_left hB, ?_⟩
      filter_upwards [hlower, hinit, (eventually_all_finite (Set.finite_Iic (q + 1))).mpr
        (fun s _ => hcurv s)] with k hk hk0 hkcurv
      let S := H.sequence.carrier k
      let F := H.sequence.flow k
      let : TopologicalSpace S.carrier := S.topologicalSpace
      let : ChartedSpace (EuclideanSpace ℝ (Fin n)) S.carrier := S.chartedSpace
      let : IsManifold (𝓡 n) ∞ S.carrier := S.isManifold
      dsimp only at hk hk0 hkcurv ⊢
      intro cover i t ht x hx j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | hj
      · apply le_trans _ (le_max_right B E)
        have hx2 : x ∈ Metric.closedBall 0 (2 * ρ) :=
          Metric.closedBall_subset_closedBall (by linarith) hx
        have hxR : x ∈ Metric.ball 0 R := Metric.closedBall_subset_ball hρR hx2
        have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (cover.chart i) (Metric.ball 0 R) := by
          simpa only [cover.source i] using (cover.chart i).contMDiffOn
        have hi : ∀ y ∈ Metric.ball 0 R,
            (mfderiv (𝓡 n) (𝓡 n) (cover.chart i) y).IsInvertible := by
          intro y hy
          exact ⟨((cover.chart i).isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞
            ((cover.source i).symm ▸ hy)).mfderivToContinuousLinearEquiv (by simp), rfl⟩
        have hdiff : ∀ s ∈ Icc l r, DifferentiableAt ℝ
            (fun u => iteratedFDeriv ℝ (q + 1)
              ((F.metricAt u).pullbackCoefficients (cover.chart i)) x) s := by
          intro s hs
          have hjoint := SpacetimeBounds.contDiffOn_spatialJet
            (F.flow.contDiffOn_pullbackCoefficients isOpen_Ioo Metric.isOpen_ball he)
            isOpen_Ioo Metric.isOpen_ball (q + 1)
          exact ((hjoint.contDiffAt (x := (s, x))
            ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds ⟨hJ hs, hxR⟩)).comp s
              (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
        have hbound : ∀ s ∈ Icc l r,
            ‖deriv (fun u => iteratedFDeriv ℝ (q + 1)
              ((F.metricAt u).pullbackCoefficients (cover.chart i)) x) s‖ ≤
              C + C * ‖iteratedFDeriv ℝ (q + 1)
                ((F.metricAt s).pullbackCoefficients (cover.chart i)) x‖ := by
          intro s hs
          have h := hevol F.flow isOpen_Ioo Metric.isOpen_ball he hi (hJ hs) hxR
            (fun v => (cover.coefficients i s (hJ hs) x hx2 v).1)
            (fun v => (cover.coefficients i s (hJ hs) x hx2 v).2)
            (fun d hd => hkcurv d hd s hs _ (cover.image_mem_zeroBall hA.le hR.le i hxR))
            (fun d hd hdq => (hk cover i s hs x hx d hdq).trans
              ((le_max_left B 1).trans (by
                simpa only [pow_one] using pow_le_pow_right₀ hD hd)))
          simpa only [BasedFlow.metricAt, mul_add, mul_one] using h
        have hprop := SpacetimeBounds.norm_le_exp_of_affine_deriv_bound
          (convex_Icc l r) h0 hdiff hC hC (hk0 cover i x hx) hbound ht
        apply hprop.trans
        apply mul_le_mul_of_nonneg_left _ (le_trans (by norm_num) (le_max_right Z 1))
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ (add_nonneg hC hC)
        rw [abs_le]
        constructor
        · linarith [(hJ ht).1, neg_abs_le T', abs_nonneg T]
        · linarith [(hJ ht).2, le_abs_self T, abs_nonneg T']
      · exact (hk cover i t ht x hx j (by omega)).trans (le_max_left B E)


theorem eventually_normalChartCover_spatial_bounds_on_interval
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hM04 : RicciFlowCurvatureTheory.{0})
    {l r : ℝ} (h0 : (0 : ℝ) ∈ Icc l r) (hJ : Icc l r ⊆ Ioo T' T)
    {A R ρ a b : ℝ} {N : ℕ} (hA : 0 < A) (hρ : 0 < ρ)
    (hρR : 2 * ρ < R) (ha : 0 < a) (hb : 0 ≤ b) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ cover : NormalChartCover F.metricAt F.base T' T A R ρ a b N,
        ∀ i, ∀ t ∈ Icc l r, ∀ x ∈ Metric.closedBall 0 ρ, ∀ j ≤ m,
          ‖iteratedFDeriv ℝ j ((F.metricAt t).pullbackCoefficients (cover.chart i)) x‖ ≤ B :=
  H.eventually_normalChartCover_spatial_bounds_on_interval_of_local_derivative_estimates
    hM04.local_derivative_estimates h0 hJ hA hρ hρR ha hb m



theorem eventually_normalChartCover_spatial_jet_bound
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hM04 : RicciFlowCurvatureTheory.{0})
    {I : Set ℝ} (hIcompact : IsCompact I) (hI : I ⊆ Ioo T' T)
    {A R ρ a b : ℝ} {N : ℕ} (hA : 0 < A) (hρ : 0 < ρ)
    (hρR : 2 * ρ < R) (ha : 0 < a) (hb : 0 ≤ b) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ cover : NormalChartCover F.metricAt F.base T' T A R ρ a b N,
        ∀ i, ∀ t ∈ I, ∀ x ∈ Metric.closedBall 0 ρ,
          ‖iteratedFDeriv ℝ m ((F.metricAt t).pullbackCoefficients (cover.chart i)) x‖ ≤ B := by
  have hI0 : insert 0 I ⊆ Ioo T' T := insert_subset H.time_bounds hI
  obtain ⟨l, hl, hmin⟩ :=
    (hIcompact.insert 0).exists_isMinOn (insert_nonempty 0 I) continuousOn_id
  obtain ⟨r, hr, hmax⟩ :=
    (hIcompact.insert 0).exists_isMaxOn (insert_nonempty 0 I) continuousOn_id
  have h0 : (0 : ℝ) ∈ Icc l r := ⟨hmin (mem_insert 0 I), hmax (mem_insert 0 I)⟩
  have hIJ : I ⊆ Icc l r := fun t ht => ⟨hmin (mem_insert_of_mem 0 ht),
    hmax (mem_insert_of_mem 0 ht)⟩
  have hJ : Icc l r ⊆ Ioo T' T := fun t ht =>
    ⟨(hI0 hl).1.trans_le ht.1, ht.2.trans_lt (hI0 hr).2⟩
  obtain ⟨B, hB, hbound⟩ := H.eventually_normalChartCover_spatial_bounds_on_interval
    hM04 h0 hJ (N := N) hA hρ hρR ha hb m
  refine ⟨B, hB, hbound.mono ?_⟩
  intro k hk
  dsimp only at hk ⊢
  intro cover i t ht x hx
  exact hk cover i t (hIJ ht) x hx m le_rfl

end PoincareConjecture.PointedRicciFlowCompactnessHypotheses
