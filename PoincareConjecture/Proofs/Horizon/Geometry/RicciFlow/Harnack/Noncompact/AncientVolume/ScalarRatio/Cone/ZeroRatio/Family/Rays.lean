import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.FamilyOverlaps
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.Family.DenseDirections
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.SectionalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.ChartCoverage
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Family.Realization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open Set Filter Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.RicciFlow

theorem exists_radial_dense_ray_annular_overlaps_of_zero_ratio
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
    ∃ η : ℕ → basedMinimizingRays p,
      DenseRange (fun j => asymptoticLinkProjection hc (η j)) ∧
      DenseRange (fun j => asymptoticConeUnitProjection hc (asymptoticLinkProjection hc (η j))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ L₀ : ℝ, 0 < L₀ ∧
        ∀ L : ℝ, L₀ ≤ L → ∀ x : M, ((F.metric t₀).edist p x).toReal = L →
          ∃ j ≤ N, ((F.metric t₀).edist x (rayExtension (η j) L)).toReal / L < ε) ∧
      let q := fun j k : ℕ => rayExtension (η j) ((k : ℝ) + 1)
      let Q := fun k : ℕ => ((k : ℝ) + 1)⁻¹ ^ 2
      let hQ : ∀ k, 0 < Q k := fun k => by dsimp [Q]; positivity
      (∀ j k, (((F.ancientRescaleAt (Q k) (hQ k) t₀ ht₀).metric 0).edist p (q j k)).toReal = 1) ∧
    ∃ S : ℝ, 0 < S ∧ S < 1 / 8 ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ Φ : ℕ → ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      let G := fun k => F.ancientRescaleAt (Q (σ k)) (hQ (σ k)) t₀ ht₀
      (∀ k j, (Φ k j).source = Metric.ball 0 S ∧
        (Φ k j).target = ((G k).metric 0).ball (q j (σ k)) S ∧ Φ k j 0 = q j (σ k) ∧
        ∀ x ∈ Metric.ball 0 S,
          ((G k).metric 0).edist (q j (σ k)) (Φ k j x) = ENNReal.ofReal ‖x‖) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < S → ∃ N : ℕ, ∀ᶠ k in atTop,
        ∀ x : M, (((G k).metric 0).edist p x).toReal = 1 →
          ∃ j ≤ N, ∃ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ,
            Φ k j y = x) ∧
      ∃ (g : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (D : ∀ j, LeviCivitaData (g j)) (r : ℝ), ∃ hr : 0 < r,
        2 * r < S / 4 ∧
        (∀ k j, ∀ x ∈ Metric.closedBall 0 (2 * r), ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ((G k).metric 0).pullbackCoefficients (Φ k j) x v v ∧
          ((G k).metric 0).pullbackCoefficients (Φ k j) x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) ∧
        (∀ j v w, (g j).inner 0 v w = inner ℝ v w) ∧
        (∀ j (x v : EuclideanSpace ℝ (Fin n)), ‖v‖ / 2 ≤ (g j).tangentNorm x v ∧
          (g j).tangentNorm x v ≤ 3 * ‖v‖ / 2) ∧
        (∀ j x v, (g j).inner x x v = inner ℝ x v) ∧
        (∀ j m C, IsCompact C → C ⊆ Metric.closedBall 0 r → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (((G k).metric 0).pullbackCoefficients (Φ k j)))
          (iteratedFDeriv ℝ m (g j).euclideanCoefficients) atTop C) ∧
        (∀ j x, x ∈ Metric.closedBall 0 r → (D j).curvatureTensorNorm x = 0) ∧
        (∀ j, TendstoUniformlyOn
          (fun k (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
            (((G k).metric 0).edist (Φ k j z.1) (Φ k j z.2)).toReal)
          (fun z => ((g j).edist z.1 z.2).toReal) atTop
          (Metric.closedBall 0 (r / 20) ×ˢ Metric.closedBall 0 (r / 20))) ∧
        (∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧ ρ < S / 2 ∧ ∀ j m,
          TendstoUniformlyOn
            (fun k (z : ℝ × EuclideanSpace ℝ (Fin n)) => iteratedFDeriv ℝ m
              (((G k).metric z.1).pullbackCoefficients (Φ k j)) z.2)
            (fun z => iteratedFDeriv ℝ m (g j).euclideanCoefficients z.2) atTop
            (Icc (-1) 0 ×ˢ Metric.closedBall 0 ρ)) ∧
        let X := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 20)
        letI : Nonempty X := ⟨⟨0, Metric.mem_ball_self (by positivity)⟩⟩
        ∃ d : ℕ → ℕ → C(X × X, ℝ),
          (∀ i j, TendstoLocallyUniformly
            (fun k (z : X × X) => (((G k).metric 0).edist (Φ k i z.1) (Φ k j z.2)).toReal)
            (d i j) atTop) ∧
          (∀ i (x y : X), d i i (x, y) = ((g i).edist x y).toReal) ∧
          ∃ T : ℕ → ℕ → OpenPartialHomeomorph X X,
            (∀ i j (x y : X), x ∈ (T i j).source ∧ T i j x = y ↔ d i j (x, y) = 0) ∧
            (∀ i, (T i i).source = univ) ∧ (∀ i x, T i i x = x) ∧
            (∀ i j l x, x ∈ (T i j).source → T i j x ∈ (T j l).source →
              x ∈ (T i l).source ∧ T j l (T i j x) = T i l x) ∧
            (∀ i j, IsClosed {z : X × X | z.1 ∈ (T i j).source ∧ T i j z.1 = z.2}) ∧
            (∀ i j x, x ∈ (T i j).source →
              Tendsto (fun k => Function.invFun (fun z : X => Φ k j z) (Φ k i x))
                atTop (𝓝 (T i j x))) ∧
            (∀ i j (x y : X), x ∈ (T i j).source → y ∈ (T i j).source →
              ((g i).edist x y).toReal = ((g j).edist (T i j x) (T i j y)).toReal) ∧
            ∃ e : ∀ j, RiemannianMetric.MetricCoordinateBall (g j) (r / 40) → AsymptoticCone p hc,
              (by exact
                (∀ j, Isometry (e j)) ∧
                (∀ i j x y, dist (e i x) (e j y) = d i j
                  (⟨x.val, Metric.closedBall_subset_ball (by linarith : r / 40 < r / 20) x.property⟩,
                   ⟨y.val, Metric.closedBall_subset_ball (by linarith : r / 40 < r / 20) y.property⟩)) ∧
                (∀ j, e j ⟨0, Metric.mem_closedBall_self (by positivity)⟩ =
                  asymptoticConeRayProjection hc (1, η j)) ∧
                (∀ j, Metric.ball (asymptoticConeRayProjection hc (1, η j)) (r / 40) ⊆ range (e j)) ∧
                (∀ j, TendstoUniformly
                  (fun k (x : RiemannianMetric.MetricCoordinateBall (g j) (r / 40)) =>
                    (((G k).metric 0).edist p (Φ k j x.val)).toReal)
                  (fun x => (asymptoticConeRadius hc (e j x) : ℝ)) atTop)) := by
  classical
  let := (F.metric t₀).toMetricSpace
  let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
    (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t₀ ht₀ x) v w
  obtain ⟨η, hdense, hunitDense, hnets⟩ :=
    (F.metric t₀).exists_dense_ray_sequence_with_source_sphere_nets
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p
  refine ⟨η, hdense, hunitDense, hnets, ?_⟩
  let q := fun j k : ℕ => rayExtension (η j) ((k : ℝ) + 1)
  let Q := fun k : ℕ => ((k : ℝ) + 1)⁻¹ ^ 2
  have hQ : ∀ k, 0 < Q k := fun k => by dsimp [Q]; positivity
  have hQzero : Tendsto Q atTop (𝓝 0) := by
    simpa only [Q, one_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0)).pow 2
  have hsqrt (k : ℕ) : Real.sqrt (Q k) = ((k : ℝ) + 1)⁻¹ :=
    Real.sqrt_sq (by positivity)
  have hradial (j k : ℕ) : ((F.metric t₀).edist p (q j k)).toReal = (k : ℝ) + 1 := by
    change dist p (rayExtension (η j) ((k : ℝ) + 1)) = (k : ℝ) + 1
    simpa only [rayExtension_zero, zero_sub, abs_neg,
      abs_of_pos (by positivity : 0 < (k : ℝ) + 1)] using
        rayExtension_dist (η j) (s := 0) (t := (k : ℝ) + 1) (by norm_num) (by positivity)
  have hcenter (j k : ℕ) :
      (((F.ancientRescaleAt (Q k) (hQ k) t₀ ht₀).metric 0).edist p (q j k)).toReal = 1 := by
    rw [ancientRescaleAt_edist_toReal_zero, hsqrt, hradial,
      inv_mul_cancel₀ (by positivity : (k : ℝ) + 1 ≠ 0)]
  refine ⟨hcenter, ?_⟩
  obtain ⟨S, hS, hSsmall, σ, hσ, Φ, hcharts, hrest⟩ :=
    F.exists_common_flat_annular_overlaps_of_zero_ratio hC hcomplete hoperator
      hK hbound hκ hnoncollapse hn t₀ ht₀ p hzero Q hQ hQzero q
      (fun j k => by rw [hcenter]; norm_num)
      (fun j => ⟨1, fun k => (hcenter j k).le⟩)
  have hsourceCover : ∀ ρ : ℝ, 0 < ρ → ρ < S → ∃ N : ℕ, ∀ᶠ k in atTop,
      ∀ x : M,
        (((F.ancientRescaleAt (Q (σ k)) (hQ (σ k)) t₀ ht₀).metric 0).edist p x).toReal = 1 →
        ∃ j ≤ N, ∃ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ, Φ k j y = x := by
    intro ρ hρ hρS
    obtain ⟨N, L₀, _, hnet⟩ := hnets ρ hρ
    have hscale (k : ℕ) (x y : M) :
      (((F.ancientRescaleAt (Q (σ k)) (hQ (σ k)) t₀ ht₀).metric 0).edist x y).toReal =
        ((F.metric t₀).edist x y).toReal / ((σ k : ℝ) + 1) := by
      rw [ancientRescaleAt_edist_toReal_zero, hsqrt, div_eq_mul_inv, mul_comm]
    have hL : Tendsto (fun k : ℕ => (σ k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_mono (fun k => by dsimp only [Function.comp_def]; linarith)
        (tendsto_natCast_atTop_atTop.comp hσ.tendsto_atTop)
    refine ⟨N, ?_⟩
    filter_upwards [hL.eventually_ge_atTop L₀] with k hk x hx
    have hxL : ((F.metric t₀).edist p x).toReal = (σ k : ℝ) + 1 := by
      rw [hscale] at hx
      exact (div_eq_one_iff_eq (by positivity : (σ k : ℝ) + 1 ≠ 0)).mp hx
    obtain ⟨j, hj, hnear⟩ := hnet ((σ k : ℝ) + 1) hk x hxL
    have hnear' : ((F.metric t₀).edist (q j (σ k)) x).toReal / ((σ k : ℝ) + 1) < ρ := by
      change dist (q j (σ k)) x / ((σ k : ℝ) + 1) < ρ
      rw [dist_comm]
      exact hnear
    have hxball : x ∈ ((F.ancientRescaleAt (Q (σ k)) (hQ (σ k)) t₀ ht₀).metric 0).ball
        (q j (σ k)) ρ := by
      apply (ENNReal.lt_ofReal_iff_toReal_lt
        (((F.ancientRescaleAt (Q (σ k)) (hQ (σ k)) t₀ ht₀).metric 0).edist_ne_top _ _)).mpr
      rw [hscale]
      exact hnear'
    obtain ⟨y, hy, hxy⟩ :=
      ((F.ancientRescaleAt (Q (σ k)) (hQ (σ k)) t₀ ht₀).metric 0).ball_subset_image_closedBall_of_normal_chart
        (Φ k j) (q j (σ k)) hρ hρS (hcharts k j).1 (hcharts k j).2.1
        (hcharts k j).2.2.2 hxball
    exact ⟨j, hj, y, hy, hxy⟩
  obtain ⟨g, D, r, hr, hrS, helliptic, hcenterMetric, hglobal, hgauss, hjets, hflat,
    hdist, hbackward, d, hd, hdiag, T, hzeroD, hselfDomain, hself, hcocycle, hclosed,
    htransition, hmetric⟩ := hrest
  let X := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 20)
  let repr : EuclideanSpace ℝ (Fin n) → X := fun x =>
    if hx : x ∈ X then ⟨x, hx⟩ else ⟨0, Metric.mem_ball_self (by positivity)⟩
  let δ := fun i j x y => d i j (repr x, repr y)
  have hrepr (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.closedBall 0 (r / 40)) :
      repr x = ⟨x, Metric.closedBall_subset_ball (by linarith : r / 40 < r / 20) hx⟩ := by
    dsimp only [repr]
    rw [dif_pos (Metric.closedBall_subset_ball (by linarith : r / 40 < r / 20) hx)]
  have hL (k : ℕ) : 1 / Real.sqrt (Q (σ k)) = (σ k : ℝ) + 1 := by
    rw [hsqrt, one_div, inv_inv]
  obtain ⟨τ, hτ, e, he, hecross, hecenter, hecover, heradial⟩ :=
    (F.metric t₀).exists_radial_cone_realization_of_normal_chart_family_on_rays
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p (fun k => Q (σ k)) (fun k => hQ (σ k))
      (hQzero.comp hσ.tendsto_atTop) g (by positivity : 0 < r / 40)
      (by linarith : r / 40 < 1 / 8) (by linarith : r / 40 < S) η Φ δ
      (by simpa only [ancientRescaleAt_metric, zero_div, add_zero, hL] using hcharts)
      (fun j => by
        simpa only [ancientRescaleAt_metric, zero_div, add_zero] using
          (hdist j).mono (Set.prod_mono
            (Metric.closedBall_subset_closedBall (by linarith : r / 40 ≤ r / 20))
            (Metric.closedBall_subset_closedBall (by linarith : r / 40 ≤ r / 20))))
      (by
        intro i j x hx y hy
        have h := (hd i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (repr x, repr y))
        simpa only [δ, hrepr x hx, hrepr y hy, ancientRescaleAt_metric, zero_div, add_zero] using h)
  have hτlim := hτ.tendsto_atTop
  refine ⟨S, hS, hSsmall, σ ∘ τ, hσ.comp hτ, (fun k => Φ (τ k)),
    (fun k => hcharts (τ k)), ?_, g, D, r, hr, hrS,
    (fun k => helliptic (τ k)), hcenterMetric, hglobal, hgauss, ?_, hflat, ?_, ?_,
    d, ?_, hdiag, T, hzeroD, hselfDomain, hself, hcocycle, hclosed,
    (fun i j x hx => (htransition i j x hx).comp hτlim), hmetric,
    e, he, ?_, hecenter, hecover, ?_⟩
  · intro ρ hρ hρS
    obtain ⟨N, hN⟩ := hsourceCover ρ hρ hρS
    exact ⟨N, hτlim.eventually hN⟩
  · intro j m C hC hCr V hV
    exact hτlim.eventually (hjets j m C hC hCr V hV)
  · intro j V hV
    exact hτlim.eventually (hdist j V hV)
  · obtain ⟨ρ, hρ, hρr, hρS, hbackward⟩ := hbackward
    exact ⟨ρ, hρ, hρr, hρS, fun j m V hV => hτlim.eventually (hbackward j m V hV)⟩
  · intro i j V hV x
    obtain ⟨E, hE, hlim⟩ := hd i j V hV x
    exact ⟨E, hE, hτlim.eventually hlim⟩
  · intro i j x y
    simpa only [δ, hrepr x.val x.property, hrepr y.val y.property] using hecross i j x y
  · intro j
    simpa only [ancientRescaleAt_metric, zero_div, add_zero, Function.comp_def] using heradial j

theorem exists_dense_ray_annular_overlaps_of_zero_ratio
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
    ∃ η : ℕ → basedMinimizingRays p,
      DenseRange (fun j => asymptoticLinkProjection hc (η j)) ∧
      DenseRange (fun j => asymptoticConeUnitProjection hc (asymptoticLinkProjection hc (η j))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ L₀ : ℝ, 0 < L₀ ∧
        ∀ L : ℝ, L₀ ≤ L → ∀ x : M, ((F.metric t₀).edist p x).toReal = L →
          ∃ j ≤ N, ((F.metric t₀).edist x (rayExtension (η j) L)).toReal / L < ε) ∧
      let q := fun j k : ℕ => rayExtension (η j) ((k : ℝ) + 1)
      let Q := fun k : ℕ => ((k : ℝ) + 1)⁻¹ ^ 2
      let hQ : ∀ k, 0 < Q k := fun k => by dsimp [Q]; positivity
      (∀ j k, (((F.ancientRescaleAt (Q k) (hQ k) t₀ ht₀).metric 0).edist p (q j k)).toReal = 1) ∧
    ∃ S : ℝ, 0 < S ∧ S < 1 / 8 ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ Φ : ℕ → ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      let G := fun k => F.ancientRescaleAt (Q (σ k)) (hQ (σ k)) t₀ ht₀
      (∀ k j, (Φ k j).source = Metric.ball 0 S ∧
        (Φ k j).target = ((G k).metric 0).ball (q j (σ k)) S ∧ Φ k j 0 = q j (σ k) ∧
        ∀ x ∈ Metric.ball 0 S,
          ((G k).metric 0).edist (q j (σ k)) (Φ k j x) = ENNReal.ofReal ‖x‖) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < S → ∃ N : ℕ, ∀ᶠ k in atTop,
        ∀ x : M, (((G k).metric 0).edist p x).toReal = 1 →
          ∃ j ≤ N, ∃ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ,
            Φ k j y = x) ∧
      ∃ (g : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (D : ∀ j, LeviCivitaData (g j)) (r : ℝ), ∃ hr : 0 < r,
        2 * r < S / 4 ∧
        (∀ k j, ∀ x ∈ Metric.closedBall 0 (2 * r), ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ((G k).metric 0).pullbackCoefficients (Φ k j) x v v ∧
          ((G k).metric 0).pullbackCoefficients (Φ k j) x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) ∧
        (∀ j v w, (g j).inner 0 v w = inner ℝ v w) ∧
        (∀ j (x v : EuclideanSpace ℝ (Fin n)), ‖v‖ / 2 ≤ (g j).tangentNorm x v ∧
          (g j).tangentNorm x v ≤ 3 * ‖v‖ / 2) ∧
        (∀ j x v, (g j).inner x x v = inner ℝ x v) ∧
        (∀ j m C, IsCompact C → C ⊆ Metric.closedBall 0 r → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (((G k).metric 0).pullbackCoefficients (Φ k j)))
          (iteratedFDeriv ℝ m (g j).euclideanCoefficients) atTop C) ∧
        (∀ j x, x ∈ Metric.closedBall 0 r → (D j).curvatureTensorNorm x = 0) ∧
        (∀ j, TendstoUniformlyOn
          (fun k (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
            (((G k).metric 0).edist (Φ k j z.1) (Φ k j z.2)).toReal)
          (fun z => ((g j).edist z.1 z.2).toReal) atTop
          (Metric.closedBall 0 (r / 20) ×ˢ Metric.closedBall 0 (r / 20))) ∧
        (∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧ ρ < S / 2 ∧ ∀ j m,
          TendstoUniformlyOn
            (fun k (z : ℝ × EuclideanSpace ℝ (Fin n)) => iteratedFDeriv ℝ m
              (((G k).metric z.1).pullbackCoefficients (Φ k j)) z.2)
            (fun z => iteratedFDeriv ℝ m (g j).euclideanCoefficients z.2) atTop
            (Icc (-1) 0 ×ˢ Metric.closedBall 0 ρ)) ∧
        let X := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 20)
        letI : Nonempty X := ⟨⟨0, Metric.mem_ball_self (by positivity)⟩⟩
        ∃ d : ℕ → ℕ → C(X × X, ℝ),
          (∀ i j, TendstoLocallyUniformly
            (fun k (z : X × X) => (((G k).metric 0).edist (Φ k i z.1) (Φ k j z.2)).toReal)
            (d i j) atTop) ∧
          (∀ i (x y : X), d i i (x, y) = ((g i).edist x y).toReal) ∧
          ∃ T : ℕ → ℕ → OpenPartialHomeomorph X X,
            (∀ i j (x y : X), x ∈ (T i j).source ∧ T i j x = y ↔ d i j (x, y) = 0) ∧
            (∀ i, (T i i).source = univ) ∧ (∀ i x, T i i x = x) ∧
            (∀ i j l x, x ∈ (T i j).source → T i j x ∈ (T j l).source →
              x ∈ (T i l).source ∧ T j l (T i j x) = T i l x) ∧
            (∀ i j, IsClosed {z : X × X | z.1 ∈ (T i j).source ∧ T i j z.1 = z.2}) ∧
            (∀ i j x, x ∈ (T i j).source →
              Tendsto (fun k => Function.invFun (fun z : X => Φ k j z) (Φ k i x))
                atTop (𝓝 (T i j x))) ∧
            (∀ i j (x y : X), x ∈ (T i j).source → y ∈ (T i j).source →
              ((g i).edist x y).toReal = ((g j).edist (T i j x) (T i j y)).toReal) ∧
            ∃ e : ∀ j, RiemannianMetric.MetricCoordinateBall (g j) (r / 40) → AsymptoticCone p hc,
              (by exact
                (∀ j, Isometry (e j)) ∧
                (∀ i j x y, dist (e i x) (e j y) = d i j
                  (⟨x.val, Metric.closedBall_subset_ball (by linarith : r / 40 < r / 20) x.property⟩,
                   ⟨y.val, Metric.closedBall_subset_ball (by linarith : r / 40 < r / 20) y.property⟩)) ∧
                (∀ j, e j ⟨0, Metric.mem_closedBall_self (by positivity)⟩ =
                  asymptoticConeRayProjection hc (1, η j)) ∧
                ∀ j, Metric.ball (asymptoticConeRayProjection hc (1, η j)) (r / 40) ⊆ range (e j)) := by
  let := (F.metric t₀).toMetricSpace
  obtain ⟨η, hdense, hunitDense, hnets, hcenter, S, hS, hSsmall, σ, hσ, Φ,
    hcharts, hsourceCover, g, D, r, hr, hrS, helliptic, hcenterMetric, hglobal,
    hgauss, hjets, hflat, hdist, hbackward, d, hd, hdiag, T, hzeroD,
    hselfDomain, hself, hcocycle, hclosed, htransition, hmetric, e,
    he, hecross, hecenter, hecover, heradial⟩ :=
    F.exists_radial_dense_ray_annular_overlaps_of_zero_ratio hC hcomplete hoperator
      hK hbound hκ hnoncollapse hn t₀ ht₀ p hzero
  exact ⟨η, hdense, hunitDense, hnets, hcenter, S, hS, hSsmall, σ, hσ, Φ,
    hcharts, hsourceCover, g, D, r, hr, hrS, helliptic, hcenterMetric, hglobal,
    hgauss, hjets, hflat, hdist, hbackward, d, hd, hdiag, T, hzeroD,
    hselfDomain, hself, hcocycle, hclosed, htransition, hmetric, e,
    he, hecross, hecenter, hecover⟩

end PoincareConjecture.RicciFlow
