import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.DerivativeControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Coordinates.Bounds










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.PointedRicciFlowCompactnessHypotheses

open SpacetimeBounds SpacetimeBounds.Bootstrap

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space

theorem eventually_uniform_zero_time_exponential_metric_jet_bound_of_m23_predecessors
    {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses 3 T' T)
    (P : M23NormalizedKappaCompactnessPredecessors)
    {A ρ R : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρR : ρ < R) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
      ∀ p ∈ F.zeroBall A,
        ∀ L : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3),
        ∀ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3)
            (EuclideanSpace ℝ (Fin 3)) C.carrier ∞,
          Φ.source = Metric.ball 0 R → Φ.target = (F.metricAt 0).ball p R →
          Φ 0 = p →
          (∀ u v, (F.metricAt 0).pullbackCoefficients
            (extChartAt (𝓡 3) p).symm (extChartAt (𝓡 3) p p)
            (L u) (L v) = inner ℝ u v) →
          HasFDerivAt (fun w => extChartAt (𝓡 3) p (Φ w))
            L.toContinuousLinearMap 0 →
          (∀ w ∈ Metric.ball 0 R,
            (F.metricAt 0).IsGeodesicOn (fun t => Φ (t • w))
              {t : ℝ | t • w ∈ Metric.ball 0 R}) →
          ∀ x ∈ Metric.closedBall 0 ρ,
            ‖iteratedFDeriv ℝ m ((F.metricAt 0).pullbackCoefficients Φ) x‖ ≤ B := by
  have hR : 0 < R := hρ.trans hρR
  choose D hD hcurv using fun l =>
    H.eventually_zero_time_curvatureDerivativeNorm_le_of_m23_predecessors
      P (A + R) (by positivity) l
  obtain ⟨B, hB, hbound⟩ := CoordinateExponential.exists_uniform_pullback_metric_jet_bound
    3 m hρ hρR D (fun l => (hD l).le)
  refine ⟨B, hB, ?_⟩
  filter_upwards [(eventually_all_finite (Set.finite_Iic m)).mpr
    (fun l _ => hcurv l)] with k hk
  let C := H.sequence.carrier k
  let F := H.sequence.flow k
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  let g := F.metricAt 0
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : C.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  intro p hp L Φ hsource htarget hzero hL hderiv hgeo
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Φ (Metric.ball 0 R) := by
    simpa only [hsource] using Φ.contMDiffOn
  have hnorm := g.pullbackCoefficients_zero_of_orthonormal p
    (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR)))
    hzero hderiv hL
  apply hbound g (F.flow.connection 0) Φ he
  · intro x hx
    exact ⟨(Φ.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (hsource.symm ▸ hx)).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  · exact hnorm
  · exact CoordinateExponential.gauss_identity_of_radial_family g he hgeo
      (fun v hv t ht =>
        g.tangentNorm_radial_of_normalized_exponential p L hzero hL hderiv hgeo hv ht)
  · intro l hl x hx
    apply hk l hl (Φ x)
    have hxp : Φ x ∈ g.ball p R := by
      rw [← htarget]
      exact Φ.map_source (hsource.symm ▸ hx)
    change g.edist F.base (Φ x) < ENNReal.ofReal (A + R)
    rw [ENNReal.ofReal_add hA.le hR.le]
    exact Manifold.riemannianEDist_triangle.trans_lt (ENNReal.add_lt_add hp hxp)


theorem eventually_normalChartCover_metric_jet_bound_of_m23_predecessors
    {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses 3 T' T)
    (P : M23NormalizedKappaCompactnessPredecessors)
    {A R ρ a b : ℝ} {N : ℕ} (hA : 0 < A) (hρ : 0 < ρ) (hρR : ρ < R) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
      ∀ C : NormalChartCover F.metricAt F.base T' T A R ρ a b N,
        C.HasMetricJetBound m B := by
  obtain ⟨B, hB, hbound⟩ :=
    H.eventually_uniform_zero_time_exponential_metric_jet_bound_of_m23_predecessors
      P hA hρ hρR m
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound] with k hk
  let C := H.sequence.carrier k
  let F := H.sequence.flow k
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  dsimp only
  intro C i x hx
  obtain ⟨L, hL, hderiv⟩ := C.normalized i
  exact hk (C.centre i) (C.centre_mem i) L (C.chart i) (C.source i) (C.target i)
    (C.map_zero i) hL hderiv (C.radial_geodesic i) x hx


theorem eventually_normalChartCover_spatial_bounds_on_interval_of_m23_predecessors
    {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses 3 T' T)
    (P : M23NormalizedKappaCompactnessPredecessors)
    {l r : ℝ} (h0 : (0 : ℝ) ∈ Icc l r) (hJ : Icc l r ⊆ Ioo T' T)
    {A R ρ a b : ℝ} {N : ℕ} (hA : 0 < A) (hρ : 0 < ρ)
    (hρR : 2 * ρ < R) (ha : 0 < a) (hb : 0 ≤ b) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
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
      let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
      let : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
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
        H.eventually_compact_curvatureDerivativeNorm_le_of_m23_predecessors
          P isCompact_Icc hJ (A + R) (by positivity) s
      obtain ⟨C, hC, hevol⟩ := SpacetimeBounds.exists_affine_spatialJet_evolution_bound
        3 q K (fun s => (hK s).le) ha hb D hD
      obtain ⟨Z, hZ, hinit⟩ :=
        H.eventually_normalChartCover_metric_jet_bound_of_m23_predecessors P
          (R := R) (a := a) (b := b) (N := N) hA hρ (by linarith) (q + 1)
      let E : ℝ := max Z 1 * Real.exp ((C + C) * (|T'| + |T|))
      have hE : 0 ≤ E := by dsimp [E]; positivity
      refine ⟨max B E, le_max_of_le_left hB, ?_⟩
      filter_upwards [hlower, hinit, (eventually_all_finite (Set.finite_Iic (q + 1))).mpr
        (fun s _ => hcurv s)] with k hk hk0 hkcurv
      let S := H.sequence.carrier k
      let F := H.sequence.flow k
      let : TopologicalSpace S.carrier := S.topologicalSpace
      let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) S.carrier := S.chartedSpace
      let : IsManifold (𝓡 3) ∞ S.carrier := S.isManifold
      dsimp only at hk hk0 hkcurv ⊢
      intro cover i t ht x hx j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | hj
      · apply le_trans _ (le_max_right B E)
        have hx2 : x ∈ Metric.closedBall 0 (2 * ρ) :=
          Metric.closedBall_subset_closedBall (by linarith) hx
        have hxR : x ∈ Metric.ball 0 R := Metric.closedBall_subset_ball hρR hx2
        have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (cover.chart i) (Metric.ball 0 R) := by
          simpa only [cover.source i] using (cover.chart i).contMDiffOn
        have hi : ∀ y ∈ Metric.ball 0 R,
            (mfderiv (𝓡 3) (𝓡 3) (cover.chart i) y).IsInvertible := by
          intro y hy
          exact ⟨((cover.chart i).isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
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


theorem eventually_normalChartCover_spacetime_jet_bound_of_m23_predecessors
    {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses 3 T' T)
    (P : M23NormalizedKappaCompactnessPredecessors)
    {I : Set ℝ} (hIcompact : IsCompact I) (hI : I ⊆ Ioo T' T)
    {A R ρ a b : ℝ} {N : ℕ} (hA : 0 < A) (hρ : 0 < ρ)
    (hρR : 2 * ρ < R) (ha : 0 < a) (hb : 0 ≤ b) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
      ∀ cover : NormalChartCover F.metricAt F.base T' T A R ρ a b N,
        ∀ i, ∀ t ∈ I, ∀ x ∈ Metric.closedBall 0 ρ,
          ‖iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
            (F.metricAt z.1).pullbackCoefficients (cover.chart i) z.2) (t, x)‖ ≤ B := by
  classical
  let : ∀ k, TopologicalSpace (H.sequence.carrier k).carrier :=
    fun k => (H.sequence.carrier k).topologicalSpace
  let : ∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (H.sequence.carrier k).carrier :=
    fun k => (H.sequence.carrier k).chartedSpace
  let : ∀ k, IsManifold (𝓡 3) ∞ (H.sequence.carrier k).carrier :=
    fun k => (H.sequence.carrier k).isManifold
  let Cover := fun k => NormalChartCover (H.sequence.flow k).metricAt
    (H.sequence.flow k).base T' T A R ρ a b N
  let α := (k : ℕ) × (Cover k × Fin (N + 1))
  let L : Filter α := Filter.comap Sigma.fst atTop
  let E := EuclideanSpace ℝ (Fin 3)
  let f : α → ℝ × E → MetricCoefficient 3 := fun w z =>
    ((H.sequence.flow w.1).metricAt z.1).pullbackCoefficients (w.2.1.chart w.2.2) z.2
  let S : α → Set (ℝ × E) := fun _ => I ×ˢ Metric.closedBall 0 ρ
  have hxR {x : E} (hx : x ∈ Metric.closedBall 0 ρ) : x ∈ Metric.ball 0 R :=
    Metric.closedBall_subset_ball (by linarith) hx
  have he (w : α) : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (w.2.1.chart w.2.2)
      (Metric.ball 0 R) := by
    simpa only [w.2.1.source w.2.2] using (w.2.1.chart w.2.2).contMDiffOn
  have hi (w : α) (x : E) (hx : x ∈ Metric.ball 0 R) :
      (mfderiv (𝓡 3) (𝓡 3) (w.2.1.chart w.2.2) x).IsInvertible :=
    ⟨((w.2.1.chart w.2.2).isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      ((w.2.1.source w.2.2).symm ▸ hx)).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  have hf (w : α) : ContDiffOn ℝ ∞ (f w) (Ioo T' T ×ˢ Metric.ball 0 R) :=
    (H.sequence.flow w.1).flow.contDiffOn_pullbackCoefficients
      isOpen_Ioo Metric.isOpen_ball (he w)
  have hrange (w : α) (z : ℝ × E) (hz : z ∈ Ioo T' T ×ˢ Metric.ball 0 R) :
      spatialJet 2 (f w) z ∈ jetRicciFlowDomain 3 := by
    change ((twoJetProjection 3 (spatialJet 2 (f w) z)).1).IsInvertible
    rw [twoJetProjection_spatialJet]
    exact ((H.sequence.flow w.1).metricAt z.1).isInvertible_pullbackCoefficients
      (hi w z.2 hz.2).injective
  have hevol (w : α) (z : ℝ × E) (hz : z ∈ Ioo T' T ×ˢ Metric.ball 0 R) :
      deriv (fun t => f w (t, z.2)) z.1 = jetRicciFlowOperator 3 (spatialJet 2 (f w) z) := by
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
      H.eventually_normalChartCover_spatial_bounds_on_interval_of_m23_predecessors
        P h0 hJ (N := N) hA hρ hρR ha hb q
    refine ⟨B, hB, eventually_comap.mpr ?_⟩
    filter_upwards [hbound] with k hk w hw z hz j hj
    subst k
    exact hk w.2.1 w.2.2 z.1 (hIJ hz.1) z.2 hz.2 j hj
  have hspatial (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ w in L, ∀ z ∈ S w,
      ‖iteratedFDeriv ℝ j (fun x => f w (z.1, x)) z.2‖ ≤ B := by
    obtain ⟨B, hB, hbound⟩ := hall j
    exact ⟨B, hB, hbound.mono (fun w hw z hz => hw z hz j le_rfl)⟩
  have hcompact (j : ℕ) : ∃ K : Set (Jet E (MetricCoefficient 3) (2 + j)),
      IsCompact K ∧ K ⊆ (baseProjection 2 j) ⁻¹' jetRicciFlowDomain 3 ∧
      ∀ᶠ w in L, MapsTo (spatialJet (2 + j) (f w)) (S w) K := by
    obtain ⟨B, hB, hbound⟩ := hall (2 + j)
    obtain ⟨K, hK, hKU, hbox⟩ := exists_compact_elliptic_jet_box 3 j ha B
    refine ⟨K, hK, hKU, hbound.mono ?_⟩
    intro w hw z hz
    apply hbox
    · exact (pi_norm_le_iff_of_nonneg hB).mpr (fun d => hw z hz d (by omega))
    · intro v
      exact (w.2.1.coefficients w.2.2 z.1 (hI hz.1) z.2
        (Metric.closedBall_subset_closedBall (by linarith) hz.2) v).1
  obtain ⟨B, hB, hbound⟩ := eventuallyBounded_spacetime_jets L
    (isOpen_jetRicciFlowDomain 3) (contDiffOn_jetRicciFlowOperator 3)
    f (fun _ => Ioo T' T) (fun _ => Metric.ball 0 R) S hf
    (fun _ => isOpen_Ioo) (fun _ => Metric.isOpen_ball)
    (fun _ _ hz => ⟨hI hz.1, hxR hz.2⟩) hrange hevol hspatial hcompact m
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_comap.mp hbound] with k hk
  dsimp only
  intro cover i t ht x hx
  exact hk ⟨k, cover, i⟩ rfl (t, x) ⟨ht, hx⟩


theorem eventually_referenceNormalChartCover_spacetime_jet_bound_of_m23_predecessors
    {T' T S' S : ℝ} (H : PointedRicciFlowCompactnessHypotheses 3 T' T)
    (P : M23NormalizedKappaCompactnessPredecessors) (hS : S' < 0 ∧ 0 < S)
    {I : Set ℝ} (hIcompact : IsCompact I) (hI : I ⊆ Ioo T' T)
    {A R ρ a b : ℝ} {N : ℕ} (hA : 0 < A) (hρ : 0 < ρ)
    (hρR : 2 * ρ < R) (ha : 0 < a) (hb : 0 < b) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      ∀ cover : NormalChartCover (H.sequence.flow k).metricAt
          (H.sequence.flow k).base S' S A R ρ a b N,
        ∀ i, ∀ t ∈ I, ∀ x ∈ Metric.closedBall 0 ρ,
          ‖iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
            ((H.sequence.flow k).metricAt z.1).pullbackCoefficients
              (cover.chart i) z.2) (t, x)‖ ≤ B := by
  obtain ⟨a', b', ha', hb', hext⟩ :=
    H.eventually_referenceNormalChartCover_extension hS (N := N) hA hρ hρR ha hb
  obtain ⟨B, hB, hjets⟩ :=
    H.eventually_normalChartCover_spacetime_jet_bound_of_m23_predecessors
      P hIcompact hI (N := N) hA hρ hρR ha' hb'.le m
  refine ⟨B, hB, ?_⟩
  filter_upwards [hext, hjets] with k hextk hjetsk
  intro cover
  obtain ⟨wide, hchart⟩ := hextk cover
  simpa only [hchart] using hjetsk wide


end PoincareConjecture.PointedRicciFlowCompactnessHypotheses
