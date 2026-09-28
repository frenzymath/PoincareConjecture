import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Family.Rays
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.Neighborhood
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.Positive
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.BackwardJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.GaussDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.Family.AnnularNets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Surface.LocalModelsRadial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Surface.LocalModelsAnnuli
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Surface.LocalModelsDistances

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

open Set Filter PoincareConjecture Poincare.Gluing Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology ENNReal
universe u

private theorem metricCoordinateBall_restriction_covers_ball
    {n : ℕ} {X : Type*} [MetricSpace X]
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r)
    (hradial : ∀ x, g.edist 0 x = ENNReal.ofReal ‖x‖)
    (e : RiemannianMetric.MetricCoordinateBall g r → X) (he : Isometry e)
    (hcover : Metric.ball (e ⟨0, Metric.mem_closedBall_self (hρ.le.trans hρr)⟩) r ⊆
      range e) :
    let e' : RiemannianMetric.MetricCoordinateBall g ρ → X := fun x =>
      e ⟨x.val, Metric.closedBall_subset_closedBall hρr x.property⟩
    Metric.ball (e' ⟨0, Metric.mem_closedBall_self hρ.le⟩) ρ ⊆ range e' := by
  intro e' z hz
  obtain ⟨y, hy⟩ := hcover (Metric.ball_subset_ball hρr hz)
  have hdist : dist (e ⟨0, Metric.mem_closedBall_self (hρ.le.trans hρr)⟩) (e y) < ρ := by
    rw [hy, dist_comm]
    exact hz
  rw [he.dist_eq, RiemannianMetric.MetricCoordinateBall.dist_eq, hradial,
    ENNReal.toReal_ofReal (norm_nonneg _)] at hdist
  refine ⟨⟨y.val, ?_⟩, hy⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hdist.le

theorem PoincareConjecture.RicciFlow.exists_backward_flat_annular_source_geometry_of_zero_ratio
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (hn : 1 ≤ n) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M)
    (hzero : ∀ C : ℝ, 0 < C → ∃ L : ℝ, ∀ x : M,
      L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C) :
    letI := (F.metric t₀).toMetricSpace
    let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
      (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        x (hoperator t₀ ht₀ x) v w
    let hc := (F.metric t₀).rayComparison_of_metricComplete
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ (h : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (D : ∀ j, LeviCivitaData (h j)),
      (∀ j (x v : EuclideanSpace ℝ (Fin n)), ‖v‖ / 2 ≤ (h j).tangentNorm x v ∧
        (h j).tangentNorm x v ≤ 3 * ‖v‖ / 2) ∧
      (∀ j x, x ∈ Metric.ball 0 r → (D j).curvatureTensorNorm x = 0) ∧
      let U := fun _ : ℕ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
      let hU : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_ball
      letI : ∀ i, Nonempty (Piece U i) := fun _ => ⟨⟨0, Metric.mem_ball_self hr⟩⟩
      ∃ O : OverlapSystem (fun i => Piece U i),
      letI := quotientChartedSpace U hU O
      (by exact IsManifold (𝓡 n) ∞ (Quotient O.setoid) ∧
      ∃ f : Quotient O.setoid → AsymptoticCone p hc,
        Topology.IsOpenEmbedding f ∧
        (∀ z, 0 < asymptoticConeRadius hc (f z)) ∧
        (∀ j (x y : Piece U j), dist (f (O.include j x)) (f (O.include j y)) =
          ((h j).edist x y).toReal) ∧
        {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1} ⊆ range f ∧
        IsCompact (f ⁻¹' {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1}) ∧
        ∃ V : Set (Quotient O.setoid), IsOpen V ∧ IsCompact (closure V) ∧
          f ⁻¹' {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1} ⊆ V ∧
        ∃ A : ℕ → Quotient O.setoid → M,
          (∀ᶠ k in atTop, Topology.IsOpenEmbedding (fun x : V => A k x) ∧
            IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (A k) V) ∧
          let Q := fun k : ℕ => ((σ k : ℝ) + 1)⁻¹ ^ 2
          let hQ : ∀ k, 0 < Q k := fun k => by dsimp [Q]; positivity
          let G := fun k => F.ancientRescaleAt (Q k) (hQ k) t₀ ht₀
          (∀ z ∈ V, ∃ j, ∃ W : Set (Piece U j), IsOpen W ∧
            z ∈ O.include j '' W ∧ O.include j '' W ⊆ V ∧
            ∀ m C, IsCompact C → C ⊆ Subtype.val '' W → TendstoUniformlyOn
              (fun k (w : ℝ × EuclideanSpace ℝ (Fin n)) => iteratedFDeriv ℝ m
                (((G k).metric w.1).pullbackCoefficients
                  (ChartDistance.chartParametrization U hU (A k ∘ O.include j))) w.2)
              (fun w => iteratedFDeriv ℝ m (h j).euclideanCoefficients w.2) atTop
              (Icc (-1) 0 ×ˢ C)) ∧
          (∀ C : Set (Quotient O.setoid), IsCompact C → C ⊆ V →
            TendstoUniformlyOn (fun k z => (((G k).metric 0).edist p (A k z)).toReal)
              (fun z => (asymptoticConeRadius hc (f z) : ℝ)) atTop C) ∧
          (∀ W : Set (Quotient O.setoid), IsOpen W → W ⊆ V →
            f ⁻¹' {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1} ⊆ W →
            ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in atTop,
              {x : M | |(((G k).metric 0).edist p x).toReal - 1| ≤ δ} ⊆ A k '' W) ∧
          ∀ C : Set (Quotient O.setoid), IsCompact C → C ⊆ V →
            TendstoUniformlyOn
              (fun k (z : Quotient O.setoid × Quotient O.setoid) =>
                (((G k).metric 0).edist (A k z.1) (A k z.2)).toReal)
              (fun z => dist (f z.1) (f z.2)) atTop (C ×ˢ C)) := by
  classical
  let := (F.metric t₀).toMetricSpace
  let := (F.metric t₀).properSpace_toMetricSpace (hcomplete t₀ ht₀)
  let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
    (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t₀ ht₀ x) v w
  let hc := (F.metric t₀).rayComparison_of_metricComplete
    (F.connection t₀) (hcomplete t₀ ht₀) hsec p
  obtain ⟨η, _, hunitDense, hnets, _, S, hS, hSsmall, σ, hσ, Φ, hcharts, _,
    h, D, r, hr, hrS, helliptic, _, hglobal, hgauss, hjets, hflat, _, hbackward,
    d, hd, _, T, _, _, _, _, _, _, _, e₀, he₀, hecross, hecenter₀, hecover₀, hbaseRadius⟩ :=
    F.exists_radial_dense_ray_annular_overlaps_of_zero_ratio hC hcomplete hoperator
      hK hbound hκ hnoncollapse hn t₀ ht₀ p hzero
  obtain ⟨b, hb, _, _, hbackward⟩ := hbackward
  let Q := fun k : ℕ => ((σ k : ℝ) + 1)⁻¹ ^ 2
  have hQ : ∀ k, 0 < Q k := fun k => by dsimp [Q]; positivity
  let G := fun k => F.ancientRescaleAt (Q k) (hQ k) t₀ ht₀
  let ρ := min r b / 40
  have hminr : min r b ≤ r := min_le_left _ _
  have hminb : min r b ≤ b := min_le_right _ _
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρr : ρ ≤ r / 40 := by dsimp [ρ]; linarith
  have hρS : 3 * (ρ / 4) ≤ S := by dsimp [ρ]; linarith
  let e : ∀ j, RiemannianMetric.MetricCoordinateBall (h j) ρ → AsymptoticCone p hc :=
    fun j x => e₀ j ⟨x.val, Metric.closedBall_subset_closedBall hρr x.property⟩
  have he : ∀ j, Isometry (e j) := by
    intro j
    apply Isometry.of_dist_eq
    intro x y
    exact (he₀ j).dist_eq _ _
  have hecenter : ∀ j, e j ⟨0, Metric.mem_closedBall_self hρ.le⟩ =
      asymptoticConeRayProjection hc (1, η j) := by
    intro j
    exact hecenter₀ j
  have hcover : ∀ j, Metric.ball (e j ⟨0, Metric.mem_closedBall_self hρ.le⟩) ρ ⊆
      range (e j) := by
    intro j
    apply metricCoordinateBall_restriction_covers_ball (h j) hρ hρr
      ((h j).edist_zero_eq_of_gauss (hgauss j)) (e₀ j) (he₀ j)
    rw [hecenter₀]
    exact hecover₀ j
  let U := fun _ : ℕ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (ρ / 4)
  let hU : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_ball
  let : ∀ i, Nonempty (Piece U i) := fun _ => ⟨⟨0, Metric.mem_ball_self (by positivity)⟩⟩
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (ρ / 4) ⊆
      Metric.ball 0 (r / 20) := Metric.ball_subset_ball (by dsimp [ρ]; linarith)
  let ι := Set.inclusion hsub
  have hι : Continuous ι := continuous_inclusion hsub
  let d' : ∀ i j, C(Piece U i × Piece U j, ℝ) := fun i j =>
    (d i j).comp ⟨fun z => (ι z.1, ι z.2), (hι.comp continuous_fst).prodMk (hι.comp continuous_snd)⟩
  let : ∀ k, MetricSpace M := fun k => ((G k).metric 0).toMetricSpace
  have hd' : ∀ i j, TendstoLocallyUniformly
      (fun k (z : Piece U i × Piece U j) =>
        (((G k).metric 0).edist (Φ k i z.1) (Φ k j z.2)).toReal) (d' i j) atTop := by
    intro i j
    exact (hd i j).comp (fun z : Piece U i × Piece U j => (ι z.1, ι z.2))
      ((hι.comp continuous_fst).prodMk (hι.comp continuous_snd))
  have hsource (k j : ℕ) : (Φ k j).source = Metric.ball 0 S := (hcharts k j).1
  have htarget (k j : ℕ) : (Φ k j).target =
      ((G k).metric 0).ball (rayExtension (η j) ((σ k : ℝ) + 1)) S := (hcharts k j).2.1
  have hradial (k j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 S) :
      ((G k).metric 0).edist (rayExtension (η j) ((σ k : ℝ) + 1)) (Φ k j x) =
        ENNReal.ofReal ‖x‖ := (hcharts k j).2.2.2 x hx
  have hsmallElliptic : ∀ k j, ∀ x ∈ Metric.ball 0 (3 * (ρ / 4)), ∀ v,
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ((G k).metric 0).pullbackCoefficients (Φ k j) x v v ∧
      ((G k).metric 0).pullbackCoefficients (Φ k j) x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2 := by
    intro k j x hx v
    exact helliptic k j x ((Metric.ball_subset_ball (by dsimp [ρ]; linarith :
      3 * (ρ / 4) ≤ 2 * r)).trans Metric.ball_subset_closedBall hx) v
  have hsmallJets : ∀ j m C, IsCompact C → C ⊆ Metric.ball 0 (ρ / 4) → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (((G k).metric 0).pullbackCoefficients (Φ k j)))
      (iteratedFDeriv ℝ m (h j).euclideanCoefficients) atTop C := by
    intro j m C hC hCU
    exact hjets j m C hC (hCU.trans
      ((Metric.ball_subset_ball (by dsimp [ρ]; linarith : ρ / 4 ≤ r)).trans Metric.ball_subset_closedBall))
  have hsmallBackward : ∀ j m C, IsCompact C → C ⊆ Metric.ball 0 (ρ / 4) → TendstoUniformlyOn
      (fun k (z : ℝ × EuclideanSpace ℝ (Fin n)) => iteratedFDeriv ℝ m
        (((G k).metric z.1).pullbackCoefficients (Φ k j)) z.2)
      (fun z => iteratedFDeriv ℝ m (h j).euclideanCoefficients z.2) atTop
      (Icc (-1) 0 ×ˢ C) := by
    intro j m C _ hCU
    apply (hbackward j m).mono
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    refine ⟨ht, ?_⟩
    exact (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by dsimp [ρ]; linarith : ρ / 4 ≤ b))) (hCU hx)
  have hcross : ∀ i j (x : Piece U i) (y : Piece U j),
      dist ((h i).uniformBallRestriction hρ (e i) x) ((h j).uniformBallRestriction hρ (e j) y) =
        d' i j (x, y) := by
    intro i j x y
    exact hecross i j _ _
  have hgeom := RiemannianMetric.normal_chart_restriction_geometry
    (fun k => (G k).metric 0) (fun k j => rayExtension (η j) ((σ k : ℝ) + 1)) Φ
    (by positivity : 0 < ρ / 4) hρS hsource htarget hradial hsmallElliptic
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  let hp := fun i j x y => (hd' i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := @ChartDistance.overlapSystem ℕ (fun i => Piece U i) (fun _ => inferInstance)
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ : ℕ => M)
    (fun k => ((G k).metric 0).toMetricSpace) (fun k i x => Φ k i x) d' hp
    (fun _ => 3 / 2) hgeom.1
    (fun _ => 1 / 2) (fun _ => by norm_num) hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1
  let := quotientChartedSpace U hU O
  obtain ⟨hO, f, hfopen, hfinclude, hfunit, hfcompact, V, hV, hVcompact, hKV,
      A, hmodels, hA, _⟩ :=
    RiemannianMetric.exists_source_embeddings_near_realized_unit_slice hc
      (fun k => (G k).metric 0) (fun k j => rayExtension (η j) ((σ k : ℝ) + 1)) Φ h
      hρ hρS hsource htarget hradial hsmallElliptic hsmallJets hglobal η hunitDense
      e he hecenter hcover d' hd' hcross
  have hmetric := RiemannianMetric.exists_local_source_metric_convergence_uniform_parameter_of_normal_charts
    U hU O (fun k t => (G k).metric t) (Icc (-1) 0) Φ
    (fun k i => by rw [hsource]; exact Metric.ball_subset_ball (by dsimp [ρ]; linarith))
    h hsmallBackward hmodels
  let : T2Space (Quotient O.setoid) := hfopen.isEmbedding.t2Space
  have hrel := @ChartDistance.overlapSystem_rel_iff ℕ (fun i => Piece U i)
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ : ℕ => M) (fun k => ((G k).metric 0).toMetricSpace)
    (fun k i x => Φ k i x) d' hp (fun _ => 3 / 2) hgeom.1
    (fun _ => 1 / 2) (fun _ => by norm_num) hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1
  have hradius : ∀ C : Set (Quotient O.setoid), IsCompact C → C ⊆ V →
      TendstoUniformlyOn (fun k z => (((G k).metric 0).edist p (A k z)).toReal)
        (fun z => (asymptoticConeRadius hc (f z) : ℝ)) atTop C := by
    intro C hC hCV
    apply @ChartDistance.HasLocalSourceModels.tendstoUniformlyOn_basepoint_distance
      ℕ n U hU (fun _ => inferInstance) O (fun _ : ℕ => M)
      (fun k => ((G k).metric 0).toMetricSpace) (fun k i x => Φ k i x) d'
      hd' hrel (fun _ => 3 / 2) hgeom.1 A V hmodels hV
      (fun _ => p) (fun z => (asymptoticConeRadius hc (f z) : ℝ))
      _ C hC hC.isClosed hCV
    intro j E _ _
    let inc : Piece U j → RiemannianMetric.MetricCoordinateBall (h j) (r / 40) :=
      fun x => ⟨x.val, (Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall (by dsimp [ρ]; linarith : ρ / 4 ≤ r / 40))) x.property⟩
    have hlim := (hbaseRadius j).comp inc
    dsimp only [Function.comp_def] at hlim
    have heq : (fun x : Piece U j => (asymptoticConeRadius hc (e₀ j (inc x)) : ℝ)) =
        fun x => (asymptoticConeRadius hc (f (O.include j x)) : ℝ) := by
      funext x
      rw [hfinclude]
      rfl
    rw [heq] at hlim
    exact hlim.tendstoUniformlyOn
  have hannulus : ∀ W : Set (Quotient O.setoid), IsOpen W → W ⊆ V →
      f ⁻¹' {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1} ⊆ W →
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in atTop,
        {x : M | |(((G k).metric 0).edist p x).toReal - 1| ≤ δ} ⊆ A k '' W := by
    intro W hW hWV hKW
    let o : ∀ j, Piece U j := fun _ => ⟨0, Metric.mem_ball_self (by positivity)⟩
    have hchart : ∀ j, LipschitzWith (3 / 2) (f ∘ O.include j) := by
      intro j
      apply LipschitzWith.of_dist_le_mul
      intro x y
      change dist (f (O.include j x)) (f (O.include j y)) ≤ (3 / 2 : ℝ) * dist x y
      rw [hfinclude, hfinclude, (h j).uniformBallRestriction_dist hρ (e j) (he j)]
      have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
        ((h j).edist_bounds_of_uniform_tangentNorm_bounds (hglobal j) x.val y.val).2
      rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 3 * ‖y.val - x.val‖ / 2)] at hb
      simpa only [Subtype.dist_eq, dist_eq_norm, norm_sub_rev, div_mul_eq_mul_div] using hb
    have hAW : ∀ᶠ k in atTop, Topology.IsOpenEmbedding (fun x : W => A k x) := by
      filter_upwards [hA] with k hk
      exact hk.1.comp (Topology.IsOpenEmbedding.inclusion hWV
        (hW.preimage continuous_subtype_val))
    apply @ChartDistance.HasLocalSourceModels.eventually_annulus_subset_image
      n U hU (fun _ => inferInstance) O (fun _ : ℕ => M)
      (fun k => ((G k).metric 0).toMetricSpace) (fun k i x => Φ k i x) d'
      hd' hrel (fun _ => 3 / 2) hgeom.1 A W (hmodels.restrict hW hWV)
      hW hAW _ _ f hfopen _ (isCompact_asymptoticCone_unit_slice hc) ?_
      o (3 / 2) hchart ?_ (ρ / 4) (1 / 2)
      (show 0 < ρ / 4 by positivity) (by norm_num : (0 : ℝ) < 1 / 2) ?_ ?_ ?_
      (fun _ => p) ?_
    · intro z hz
      obtain ⟨x, rfl⟩ := hfunit hz
      exact ⟨x, hKW hz, rfl⟩
    · intro j
      change asymptoticConeRadius hc (f (O.include j (o j))) = 1
      rw [hfinclude]
      change asymptoticConeRadius hc (e j ⟨0, _⟩) = 1
      rw [hecenter]
      rfl
    · intro s _ hs j
      apply Poincare.Topology.isCompact_closedBall_subtype_of_subset
      exact Metric.closedBall_subset_ball hs
    · intro k j y _
      exact hgeom.2.1 k j y (o j)
    · intro k j s
      exact hgeom.2.2.2.1 k _ s
    · intro ε hε
      have hL : Tendsto (fun k : ℕ => (σ k : ℝ) + 1) atTop atTop :=
        tendsto_atTop_mono (fun k => by dsimp only [Function.comp_def]; linarith)
          (tendsto_natCast_atTop_atTop.comp hσ.tendsto_atTop)
      obtain ⟨δ, hδ, _, N, hnet⟩ :=
        eventually_finite_ray_net_on_rescaled_annulus η hnets hL hε
      refine ⟨δ, hδ, N, ?_⟩
      have hscale (k : ℕ) (x y : M) :
          (((G k).metric 0).edist x y).toReal =
            ((F.metric t₀).edist x y).toReal / ((σ k : ℝ) + 1) := by
        rw [ancientRescaleAt_edist_toReal_zero, Real.sqrt_sq (by positivity),
          div_eq_mul_inv, mul_comm]
      filter_upwards [hnet] with k hk x hx
      change |(((G k).metric 0).edist p x).toReal - 1| ≤ δ at hx
      have hx' : |((F.metric t₀).edist p x).toReal / ((σ k : ℝ) + 1) - 1| ≤ δ := by
        rwa [hscale] at hx
      obtain ⟨j, hj, hdist⟩ := hk x hx'
      refine ⟨j, hj, ?_⟩
      change (((G k).metric 0).edist x (Φ k j 0)).toReal < ε
      rw [(hcharts k j).2.2.1, hscale]
      exact hdist
  have hpairs : ∀ C : Set (Quotient O.setoid), IsCompact C → C ⊆ V →
      TendstoUniformlyOn
        (fun k (z : Quotient O.setoid × Quotient O.setoid) =>
          (((G k).metric 0).edist (A k z.1) (A k z.2)).toReal)
        (fun z => dist (f z.1) (f z.2)) atTop (C ×ˢ C) := by
    intro C hC hCV
    exact @ChartDistance.HasLocalSourceModels.tendstoUniformlyOn_pairwise_distance
      ℕ n U hU (fun _ => inferInstance) O (fun _ : ℕ => M)
      (fun k => ((G k).metric 0).toMetricSpace) (fun k i x => Φ k i x) d'
      hd' hrel (fun _ => 3 / 2) hgeom.1 A V hmodels hV
      (AsymptoticCone p hc) inferInstance f hfopen
      (fun i j x y => by rw [hfinclude, hfinclude]; exact hcross i j x y) C hC hCV
  refine ⟨ρ / 4, by positivity, σ, hσ, h, D, hglobal, ?_, O, hO,
    f, hfopen, ?_, ?_, hfunit, hfcompact, V, hV, hVcompact, hKV, A, hA,
    hmetric, hradius, hannulus, hpairs⟩
  · intro j x hx
    exact hflat j x ((Metric.ball_subset_ball (by dsimp [ρ]; linarith : ρ / 4 ≤ r)).trans
      Metric.ball_subset_closedBall hx)
  · exact RiemannianMetric.coneRadius_pos_of_quotient_coordinateRealization hc h hρ
      (by dsimp [ρ]; linarith : ρ < 1 / 8) hglobal η e he hecenter O f hfinclude
  · intro j x y
    rw [hfinclude, hfinclude]
    exact (h j).uniformBallRestriction_dist hρ (e j) (he j) x y

theorem PoincareConjecture.RicciFlow.exists_backward_flat_annular_source_models_of_zero_ratio
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (hn : 1 ≤ n) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M)
    (hzero : ∀ C : ℝ, 0 < C → ∃ L : ℝ, ∀ x : M,
      L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C) :
    letI := (F.metric t₀).toMetricSpace
    let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
      (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        x (hoperator t₀ ht₀ x) v w
    let hc := (F.metric t₀).rayComparison_of_metricComplete
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ (h : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (D : ∀ j, LeviCivitaData (h j)),
      (∀ j (x v : EuclideanSpace ℝ (Fin n)), ‖v‖ / 2 ≤ (h j).tangentNorm x v ∧
        (h j).tangentNorm x v ≤ 3 * ‖v‖ / 2) ∧
      (∀ j x, x ∈ Metric.ball 0 r → (D j).curvatureTensorNorm x = 0) ∧
      let U := fun _ : ℕ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
      let hU : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_ball
      letI : ∀ i, Nonempty (Piece U i) := fun _ => ⟨⟨0, Metric.mem_ball_self hr⟩⟩
      ∃ O : OverlapSystem (fun i => Piece U i),
      letI := quotientChartedSpace U hU O
      (by exact IsManifold (𝓡 n) ∞ (Quotient O.setoid) ∧
      ∃ f : Quotient O.setoid → AsymptoticCone p hc,
        Topology.IsOpenEmbedding f ∧
        (∀ z, 0 < asymptoticConeRadius hc (f z)) ∧
        (∀ j (x y : Piece U j), dist (f (O.include j x)) (f (O.include j y)) =
          ((h j).edist x y).toReal) ∧
        {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1} ⊆ range f ∧
        IsCompact (f ⁻¹' {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1}) ∧
        ∃ V : Set (Quotient O.setoid), IsOpen V ∧ IsCompact (closure V) ∧
          f ⁻¹' {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1} ⊆ V ∧
        ∃ A : ℕ → Quotient O.setoid → M,
          (∀ᶠ k in atTop, Topology.IsOpenEmbedding (fun x : V => A k x) ∧
            IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (A k) V) ∧
          let Q := fun k : ℕ => ((σ k : ℝ) + 1)⁻¹ ^ 2
          let hQ : ∀ k, 0 < Q k := fun k => by dsimp [Q]; positivity
          let G := fun k => F.ancientRescaleAt (Q k) (hQ k) t₀ ht₀
          ∀ z ∈ V, ∃ j, ∃ W : Set (Piece U j), IsOpen W ∧
            z ∈ O.include j '' W ∧ O.include j '' W ⊆ V ∧
            ∀ m C, IsCompact C → C ⊆ Subtype.val '' W → TendstoUniformlyOn
              (fun k (w : ℝ × EuclideanSpace ℝ (Fin n)) => iteratedFDeriv ℝ m
                (((G k).metric w.1).pullbackCoefficients
                  (ChartDistance.chartParametrization U hU (A k ∘ O.include j))) w.2)
              (fun w => iteratedFDeriv ℝ m (h j).euclideanCoefficients w.2) atTop
              (Icc (-1) 0 ×ˢ C)) := by
  classical
  obtain ⟨r, hr, σ, hσ, h, D, hglobal, hflat, O, hO, f, hf, hpositive,
    hdist, hunit, hcompact, V, hV, hVcompact, hKV, A, hA, hmetric, _, _, _⟩ :=
    F.exists_backward_flat_annular_source_geometry_of_zero_ratio hC hcomplete hoperator
      hK hbound hκ hnoncollapse hn t₀ ht₀ p hzero
  exact ⟨r, hr, σ, hσ, h, D, hglobal, hflat, O, hO, f, hf, hpositive,
    hdist, hunit, hcompact, V, hV, hVcompact, hKV, A, hA, hmetric⟩
