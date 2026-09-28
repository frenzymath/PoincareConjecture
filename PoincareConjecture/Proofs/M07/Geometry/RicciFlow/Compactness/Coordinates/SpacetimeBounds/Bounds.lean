import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.SpatialBounds
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.BootstrapAdapter
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bootstrap.Evolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.PointedRicciFlowCompactnessHypotheses

open SpacetimeBounds SpacetimeBounds.Bootstrap

theorem eventually_normalChartCover_spacetime_jet_bound_of_local_derivative_estimates
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hShi : LocalCurvatureDerivativeEstimates.{0})
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
          ‖iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            (F.metricAt z.1).pullbackCoefficients (cover.chart i) z.2) (t, x)‖ ≤ B := by
  classical
  let : ∀ k, TopologicalSpace (H.sequence.carrier k).carrier :=
    fun k => (H.sequence.carrier k).topologicalSpace
  let : ∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (H.sequence.carrier k).carrier :=
    fun k => (H.sequence.carrier k).chartedSpace
  let : ∀ k, IsManifold (𝓡 n) ∞ (H.sequence.carrier k).carrier :=
    fun k => (H.sequence.carrier k).isManifold
  let Cover := fun k => NormalChartCover (H.sequence.flow k).metricAt
    (H.sequence.flow k).base T' T A R ρ a b N
  let α := (k : ℕ) × (Cover k × Fin (N + 1))
  let L : Filter α := Filter.comap Sigma.fst atTop
  let E := EuclideanSpace ℝ (Fin n)
  let f : α → ℝ × E → MetricCoefficient n := fun w z =>
    ((H.sequence.flow w.1).metricAt z.1).pullbackCoefficients (w.2.1.chart w.2.2) z.2
  let S : α → Set (ℝ × E) := fun _ => I ×ˢ Metric.closedBall 0 ρ
  have hxR {x : E} (hx : x ∈ Metric.closedBall 0 ρ) : x ∈ Metric.ball 0 R :=
    Metric.closedBall_subset_ball (by linarith) hx
  have he (w : α) : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (w.2.1.chart w.2.2)
      (Metric.ball 0 R) := by
    simpa only [w.2.1.source w.2.2] using (w.2.1.chart w.2.2).contMDiffOn
  have hi (w : α) (x : E) (hx : x ∈ Metric.ball 0 R) :
      (mfderiv (𝓡 n) (𝓡 n) (w.2.1.chart w.2.2) x).IsInvertible :=
    ⟨((w.2.1.chart w.2.2).isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞
      ((w.2.1.source w.2.2).symm ▸ hx)).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  have hf (w : α) : ContDiffOn ℝ ∞ (f w) (Ioo T' T ×ˢ Metric.ball 0 R) :=
    (H.sequence.flow w.1).flow.contDiffOn_pullbackCoefficients
      isOpen_Ioo Metric.isOpen_ball (he w)
  have hrange (w : α) (z : ℝ × E) (hz : z ∈ Ioo T' T ×ˢ Metric.ball 0 R) :
      spatialJet 2 (f w) z ∈ jetRicciFlowDomain n := by
    change ((twoJetProjection n (spatialJet 2 (f w) z)).1).IsInvertible
    rw [twoJetProjection_spatialJet]
    exact ((H.sequence.flow w.1).metricAt z.1).isInvertible_pullbackCoefficients
      (hi w z.2 hz.2).injective
  have hevol (w : α) (z : ℝ × E) (hz : z ∈ Ioo T' T ×ˢ Metric.ball 0 R) :
      deriv (fun t => f w (t, z.2)) z.1 = jetRicciFlowOperator n (spatialJet 2 (f w) z) := by
    rw [jetRicciFlowOperator, Function.comp_apply, twoJetProjection_spatialJet]
    exact deriv_pullbackCoefficients_eq_ricciFlowOperator (H.sequence.flow w.1).flow
      isOpen_Ioo Metric.isOpen_ball (he w) (hi w) hz.1 hz.2
  have hI0 : insert 0 I ⊆ Ioo T' T := insert_subset H.time_bounds hI
  obtain ⟨l, hl, hmin⟩ :=
    (hIcompact.insert 0).exists_isMinOn (insert_nonempty 0 I) continuousOn_id
  obtain ⟨r, hr, hmax⟩ :=
    (hIcompact.insert 0).exists_isMaxOn (insert_nonempty 0 I) continuousOn_id
  have h0 : (0 : ℝ) ∈ Icc l r := ⟨hmin (mem_insert 0 I), hmax (mem_insert 0 I)⟩
  have hIJ : I ⊆ Icc l r := fun t ht =>
    ⟨hmin (mem_insert_of_mem 0 ht), hmax (mem_insert_of_mem 0 ht)⟩
  have hJ : Icc l r ⊆ Ioo T' T := fun t ht =>
    ⟨(hI0 hl).1.trans_le ht.1, ht.2.trans_lt (hI0 hr).2⟩
  have hall (q : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ w in L, ∀ z ∈ S w, ∀ j ≤ q,
      ‖iteratedFDeriv ℝ j (fun x => f w (z.1, x)) z.2‖ ≤ B := by
    obtain ⟨B, hB, hbound⟩ :=
      H.eventually_normalChartCover_spatial_bounds_on_interval_of_local_derivative_estimates
        hShi h0 hJ (N := N) hA hρ hρR ha hb q
    refine ⟨B, hB, eventually_comap.mpr ?_⟩
    filter_upwards [hbound] with k hk w hw z hz j hj
    subst k
    exact hk w.2.1 w.2.2 z.1 (hIJ hz.1) z.2 hz.2 j hj
  have hspatial (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ w in L, ∀ z ∈ S w,
      ‖iteratedFDeriv ℝ j (fun x => f w (z.1, x)) z.2‖ ≤ B := by
    obtain ⟨B, hB, hbound⟩ := hall j
    exact ⟨B, hB, hbound.mono (fun w hw z hz => hw z hz j le_rfl)⟩
  have hcompact (j : ℕ) : ∃ K : Set (Jet E (MetricCoefficient n) (2 + j)),
      IsCompact K ∧ K ⊆ (baseProjection 2 j) ⁻¹' jetRicciFlowDomain n ∧
      ∀ᶠ w in L, MapsTo (spatialJet (2 + j) (f w)) (S w) K := by
    obtain ⟨B, hB, hbound⟩ := hall (2 + j)
    obtain ⟨K, hK, hKU, hbox⟩ := exists_compact_elliptic_jet_box n j ha B
    refine ⟨K, hK, hKU, hbound.mono ?_⟩
    intro w hw z hz
    apply hbox
    · exact (pi_norm_le_iff_of_nonneg hB).mpr (fun d => hw z hz d (by omega))
    · intro v
      exact (w.2.1.coefficients w.2.2 z.1 (hI hz.1) z.2
        (Metric.closedBall_subset_closedBall (by linarith) hz.2) v).1
  obtain ⟨B, hB, hbound⟩ := eventuallyBounded_spacetime_jets L
    (isOpen_jetRicciFlowDomain n) (contDiffOn_jetRicciFlowOperator n)
    f (fun _ => Ioo T' T) (fun _ => Metric.ball 0 R) S hf
    (fun _ => isOpen_Ioo) (fun _ => Metric.isOpen_ball)
    (fun _ _ hz => ⟨hI hz.1, hxR hz.2⟩) hrange hevol hspatial hcompact m
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_comap.mp hbound] with k hk
  dsimp only
  intro cover i t ht x hx
  exact hk ⟨k, cover, i⟩ rfl (t, x) ⟨ht, hx⟩

theorem eventually_normalChartCover_spacetime_jet_bound
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
          ‖iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            (F.metricAt z.1).pullbackCoefficients (cover.chart i) z.2) (t, x)‖ ≤ B :=
  H.eventually_normalChartCover_spacetime_jet_bound_of_local_derivative_estimates
    hM04.local_derivative_estimates hIcompact hI hA hρ hρR ha hb m

end PoincareConjecture.PointedRicciFlowCompactnessHypotheses
