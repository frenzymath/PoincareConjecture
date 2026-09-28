import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.UniformDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.ChartOverlaps
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Backward.FamilyJets

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.RicciFlow

theorem exists_common_flat_annular_overlaps_of_zero_ratio
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
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C)
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (hQzero : Tendsto Q atTop (𝓝 0))
    (q : ℕ → ℕ → M)
    (hcenter : ∀ j k, 3 / 4 ≤
      (((F.ancientRescaleAt (Q k) (hQ k) t₀ ht₀).metric 0).edist p (q j k)).toReal)
    (hbounded : ∀ j, ∃ A : ℝ, ∀ k,
      (((F.ancientRescaleAt (Q k) (hQ k) t₀ ht₀).metric 0).edist p (q j k)).toReal ≤ A) :
    ∃ S : ℝ, 0 < S ∧ S < 1 / 8 ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ Φ : ℕ → ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      let G := fun k => F.ancientRescaleAt (Q (σ k)) (hQ (σ k)) t₀ ht₀
      (∀ k j, (Φ k j).source = Metric.ball 0 S ∧
        (Φ k j).target = ((G k).metric 0).ball (q j (σ k)) S ∧ Φ k j 0 = q j (σ k) ∧
        ∀ x ∈ Metric.ball 0 S,
          ((G k).metric 0).edist (q j (σ k)) (Φ k j x) = ENNReal.ofReal ‖x‖) ∧
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
            ∀ i j (x y : X), x ∈ (T i j).source → y ∈ (T i j).source →
              ((g i).edist x y).toReal = ((g j).edist (T i j x) (T i j y)).toReal := by
  obtain ⟨S, hS, hSr, σ, hσ, L₀, Φ, hcurv, hcharts, g, D, r, hr, hrS,
    helliptic, hnorm, hglobal, hgauss, houtside, hjets, hflat, hdist⟩ :=
    F.exists_common_flat_annular_metrics_with_source_distances_of_zero_ratio
      hC hcomplete hoperator hK hbound
      hκ hnoncollapse hn t₀ ht₀ p hzero Q hQ hQzero q hcenter
  let G := fun k => F.ancientRescaleAt (Q (σ k)) (hQ (σ k)) t₀ ht₀
  have hcoeff (j : ℕ) : TendstoUniformlyOn
      (fun k => ((G k).metric 0).pullbackCoefficients (Φ k j))
      (g j).euclideanCoefficients atTop (Metric.closedBall 0 r) := by
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn
          (hjets j 0 _ (isCompact_closedBall _ _) Subset.rfl)
  obtain ⟨ρ, hρ, hρr, hρS, hbackward⟩ :=
    F.exists_common_backward_static_metric_jets_of_zero_ratio hC hcomplete hoperator hK hbound
      t₀ ht₀ p hzero (Q ∘ σ) (fun k => hQ (σ k)) (hQzero.comp hσ.tendsto_atTop)
      (fun j k => q j (σ k)) (fun j k => hcenter j (σ k)) hS hSr L₀ Φ
      (fun k j => (hcharts k j).1) (fun k j => (hcharts k j).2.2.1)
      (fun k j => (hcharts k j).2.2.2.1) (fun k j => (hcharts k j).2.2.2.2.1)
      (fun k j => (hcharts k j).2.2.2.2.2.1) (fun k j => (hcharts k j).2.2.2.2.2.2)
      g hr (fun j x hx => (hcoeff j).tendsto_at (Metric.ball_subset_closedBall hx))
  have hpair (i j : ℕ) : ∃ A : ℝ, ∀ k,
      (((G k).metric 0).edist (q i (σ k)) (q j (σ k))).toReal ≤ A := by
    obtain ⟨A, hA⟩ := hbounded i
    obtain ⟨B, hB⟩ := hbounded j
    refine ⟨A + B, ?_⟩
    intro k
    let := ((G k).metric 0).toMetricSpace
    have ht := dist_triangle (q i (σ k)) p (q j (σ k))
    rw [dist_comm (q i (σ k)) p] at ht
    exact ht.trans (add_le_add (hA (σ k)) (hB (σ k)))
  obtain ⟨τ, hτ, d, hd, T, hzeroD, hselfDomain, hself, hcocycle, hclosed, htransition⟩ :=
    RiemannianMetric.exists_normal_chart_overlap_limits (M := fun _ => M)
      (fun k => (G k).metric 0) (fun k j => q j (σ k)) Φ
      (by positivity : 0 < r / 20) (by linarith : 3 * (r / 20) ≤ S)
      (fun k j => (hcharts k j).1) (fun k j => (hcharts k j).2.1)
      (fun k j => (hcharts k j).2.2.2.2.2.2)
      (fun k j x hx v => helliptic k j x
        (Metric.ball_subset_closedBall ((Metric.ball_subset_ball
          (by linarith : 3 * (r / 20) ≤ 2 * r)) hx)) v) hpair
  let X := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 20)
  have hnewdist (j : ℕ) : TendstoUniformlyOn
      (fun k (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
        (((G (τ k)).metric 0).edist (Φ (τ k) j z.1) (Φ (τ k) j z.2)).toReal)
      (fun z => ((g j).edist z.1 z.2).toReal) atTop
      (Metric.closedBall 0 (r / 20) ×ˢ Metric.closedBall 0 (r / 20)) := by
    intro V hV
    exact hτ.tendsto_atTop.eventually (hdist j V hV)
  have hcross (i j : ℕ) (x y : X) : Tendsto
      (fun k => (((G (τ k)).metric 0).edist (Φ (τ k) i x) (Φ (τ k) j y)).toReal)
      atTop (𝓝 (d i j (x, y))) :=
    (hd i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  have hdiagonal (i : ℕ) (x y : X) : d i i (x, y) = ((g i).edist x y).toReal := by
    have hxy : ((x : EuclideanSpace ℝ (Fin n)), (y : EuclideanSpace ℝ (Fin n))) ∈
        Metric.closedBall 0 (r / 20) ×ˢ Metric.closedBall 0 (r / 20) :=
      ⟨Metric.ball_subset_closedBall x.property, Metric.ball_subset_closedBall y.property⟩
    exact tendsto_nhds_unique (hcross i i x y) ((hnewdist i).tendsto_at hxy)
  have hsymm (i j : ℕ) (x y : X) : d i j (x, y) = d j i (y, x) := by
    apply tendsto_nhds_unique (hcross i j x y)
    apply (hcross j i y x).congr
    intro k
    let := ((G (τ k)).metric 0).toMetricSpace
    exact dist_comm (Φ (τ k) j y) (Φ (τ k) i x)
  have hfour (i j : ℕ) (x y a b : X) :
      d i i (x, y) ≤ d i j (x, a) + d j j (a, b) + d i j (y, b) := by
    apply le_of_tendsto_of_tendsto (hcross i i x y)
      (((hcross i j x a).add (hcross j j a b)).add (hcross i j y b))
    exact Filter.Eventually.of_forall fun k => by
      let := ((G (τ k)).metric 0).toMetricSpace
      have h := dist_triangle4 (Φ (τ k) i x) (Φ (τ k) j a)
        (Φ (τ k) j b) (Φ (τ k) i y)
      rwa [dist_comm (Φ (τ k) j b) (Φ (τ k) i y)] at h
  have hmetric (i j : ℕ) (x y : X) (hx : x ∈ (T i j).source)
      (hy : y ∈ (T i j).source) :
      ((g i).edist x y).toReal = ((g j).edist (T i j x) (T i j y)).toReal := by
    have hxzero := (hzeroD i j x (T i j x)).mp ⟨hx, rfl⟩
    have hyzero := (hzeroD i j y (T i j y)).mp ⟨hy, rfl⟩
    have hf := hfour i j x y (T i j x) (T i j y)
    have hb := hfour j i (T i j x) (T i j y) x y
    rw [← hsymm i j x (T i j x), ← hsymm i j y (T i j y)] at hb
    rw [hxzero, hyzero, zero_add, add_zero, hdiagonal, hdiagonal] at hf hb
    exact le_antisymm hf hb
  refine ⟨S, hS, hSr, σ ∘ τ, hσ.comp hτ, (fun k => Φ (τ k)), ?_,
    g, D, r, hr, hrS, (fun k => helliptic (τ k)), hnorm, hglobal, hgauss, ?_, hflat,
    hnewdist, ⟨ρ, hρ, hρr, hρS, fun j m =>
      (hbackward j m).seq_tendstoUniformlyOn τ hτ.tendsto_atTop⟩,
    d, hd, hdiagonal, T, hzeroD, hselfDomain, hself, hcocycle, hclosed,
    htransition, hmetric⟩
  · intro k j
    exact ⟨(hcharts (τ k) j).1, (hcharts (τ k) j).2.1,
      (hcharts (τ k) j).2.2.1, (hcharts (τ k) j).2.2.2.2.2.2⟩
  · intro j m C hCcompact hCball V hV
    exact hτ.tendsto_atTop.eventually (hjets j m C hCcompact hCball V hV)

end PoincareConjecture.RicciFlow
