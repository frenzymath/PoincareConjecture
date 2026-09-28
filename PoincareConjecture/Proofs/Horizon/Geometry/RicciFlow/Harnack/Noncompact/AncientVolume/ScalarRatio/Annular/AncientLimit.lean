import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.NormalizedSpacetime
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.ChartFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.LimitPositivity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.LimitCurvature














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000

open Set Filter Metric TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow

private theorem curvature_of_ancient_chart_coefficient_limit
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {ρ : ℝ} (hρ : 0 < ρ) (Fseq : ℕ → RicciFlow n M (Iic 0))
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (hsource : ∀ k, closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ ⊆ (Φ k).source)
    (hoperator : ∀ k t, t ≤ 0 → ∀ x, ((Fseq k).connection t).NonnegativeCurvatureOperator x)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hU : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ ball 0 ρ)
    (F : RicciFlow n U (Iic 0))
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (Iic 0 ×ˢ closedBall 0 ρ))
    (hcoeff : ∀ t ≤ 0, ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      (F.metric t).inner x v w = B (t, x) v w)
    (hjet : ∀ r K, IsCompact K → K ⊆ Iic 0 ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ →
      TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ r
          (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((Fseq k).metric z.1).pullbackCoefficients (Φ k) z.2)
          (Iic 0 ×ˢ closedBall 0 ρ))
        (iteratedFDerivWithin ℝ r B (Iic 0 ×ˢ closedBall 0 ρ)) atTop K) :
    ∀ t ≤ 0, ∀ x : U, (F.connection t).NonnegativeCurvatureOperator x ∧
      Tendsto (fun k => ((Fseq k).connection t).scalarCurvature (Φ k x)) atTop
        (𝓝 ((F.connection t).scalarCurvature x)) := by
  intro t ht x
  have hsmooth (k : ℕ) :=
    ((Fseq k).contDiffOn_pullbackCoefficients_within (Φ k).open_source
      (Φ k).contMDiffOn_toFun).mono (prod_mono subset_rfl (hsource k))
  have hslice : ContDiffOn ℝ ∞ (fun y => B (t, y)) U := by
    apply hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    exact fun y hy => ⟨ht, ball_subset_closedBall (hU hy)⟩
  obtain ⟨g, D, V, hVo, hxV, hVU, heq⟩ :=
    RiemannianMetric.exists_local_realization U.isOpen x.property (fun y => B (t, y))
      hslice (fun y hy v w => by
        rw [← hcoeff t ht ⟨y, hy⟩ v w, ← hcoeff t ht ⟨y, hy⟩ w v]
        exact (F.metric t).symm _ _ _)
      (fun y hy v hv => by
        rw [← hcoeff t ht ⟨y, hy⟩ v v]
        exact (F.metric t).pos _ v hv)
  have hevent : g.euclideanCoefficients =ᶠ[𝓝 (x : EuclideanSpace ℝ (Fin n))]
      (fun y => B (t, y)) := Filter.Eventually.mono (hVo.mem_nhds hxV) heq
  have hspatial := (Poincare.AncientVolume.spatial_and_time_jets_of_halfCylinder_compact_uniform
    hρ (fun k (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
      ((Fseq k).metric z.1).pullbackCoefficients (Φ k) z.2)
    B hsmooth hB hjet ht (hU x.property)).1
  obtain ⟨hpos, hscalar⟩ := LeviCivitaData.curvature_of_partialDiffeomorph_metric_jets
    (fun k => (Fseq k).metric t) (fun k => (Fseq k).connection t) Φ D x
    (fun k => hsource k (ball_subset_closedBall (hU x.property)))
    (fun r _ => by
      rw [(hevent.iteratedFDeriv ℝ r).self_of_nhds]
      exact hspatial r)
    (Eventually.of_forall (fun k => hoperator k t ht (Φ k x)))
  have hid (y : U) :
      mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → EuclideanSpace ℝ (Fin n)) y =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    change mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) y) y = _
    exact mfderiv_extChartAt_self
  have hmetric : ∀ y ∈ (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' V,
      ∀ v w : TangentSpace (𝓡 n) y,
        (F.metric t).inner y v w = g.inner (y : EuclideanSpace ℝ (Fin n))
          (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → EuclideanSpace ℝ (Fin n)) y v)
          (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → EuclideanSpace ℝ (Fin n)) y w) := by
    intro y hy v w
    rw [hid]
    change (F.metric t).inner y v w = g.inner (y : EuclideanSpace ℝ (Fin n)) v w
    rw [hcoeff t ht]
    exact (congrArg (fun T => T v w) (heq y hy)).symm
  have hlocal : IsOpen ((Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' V) :=
    hVo.preimage continuous_subtype_val
  have hmap : ContMDiffOn (𝓡 n) (𝓡 n) ∞
      (Subtype.val : U → EuclideanSpace ℝ (Fin n))
      ((Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' V) :=
    contMDiff_subtype_val.contMDiffOn
  refine ⟨((F.connection t).nonnegativeCurvatureOperator_iff_of_local_isometry D
    hlocal hmap hmetric hxV).2 hpos, ?_⟩
  rwa [← (F.connection t).scalarCurvature_eq_of_local_isometry D
    hlocal hmap hmetric hxV] at hscalar

set_option maxHeartbeats 600000 in




theorem exists_normalized_annular_ancient_flow
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
    (hn : 1 ≤ n) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M) (q : ℕ → M)
    (hQ : ∀ i, 0 < (F.connection t₀).scalarCurvature (q i))
    (hd : Tendsto (fun i => ((F.metric t₀).edist p (q i)).toReal) atTop atTop)
    {A C L : ℝ} (hA : 0 < A) (hCnonneg : 0 ≤ C)
    (hratio : Tendsto (fun i => (F.connection t₀).scalarCurvature (q i) *
      ((F.metric t₀).edist p (q i)).toReal ^ 2) atTop (𝓝 A))
    (hdecay : ∀ x, L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C) :
    ∃ K₀ S ρ : ℝ, 0 < K₀ ∧ 0 < S ∧ 0 < ρ ∧ ρ < S / 2 ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ L₀ : ℕ → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      let G := fun k => F.ancientRescaleAt
        ((F.connection t₀).scalarCurvature (q (σ k))) (hQ (σ k)) t₀ ht₀
      (∀ k s, s ≤ 0 → MetricComplete ((G k).metric s)) ∧
      (∀ k s, s ≤ 0 → ∀ x, ((G k).connection s).NonnegativeCurvatureOperator x) ∧
      (∀ k s, s ≤ 0 → ∀ x ∈ ((G k).metric 0).ball (q (σ k)) (2 * S),
        ((G k).connection s).curvatureTensorNorm x ≤ K₀) ∧
      (∀ k, ((G k).connection 0).scalarCurvature (q (σ k)) = 1) ∧
      (∀ k, (Φ k).source = ball 0 S ∧
        (Φ k).target = ((G k).metric 0).ball (q (σ k)) S ∧ Φ k 0 = q (σ k) ∧
        (∀ v w, ((G k).metric 0).pullbackCoefficients
          (extChartAt (𝓡 n) (q (σ k))).symm (extChartAt (𝓡 n) (q (σ k)) (q (σ k)))
            (L₀ k v) (L₀ k w) = inner ℝ v w) ∧
        HasFDerivAt (fun w => extChartAt (𝓡 n) (q (σ k)) (Φ k w))
          (L₀ k).toContinuousLinearMap 0 ∧
        (∀ w ∈ ball 0 S, ((G k).metric 0).IsGeodesicOn
          (fun t => Φ k (t • w)) {t : ℝ | t • w ∈ ball 0 S}) ∧
        ∀ w ∈ ball 0 S,
          ((G k).metric 0).edist (q (σ k)) (Φ k w) = ENNReal.ofReal ‖w‖) ∧
      ∃ B : ℝ × EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
        ContDiffOn ℝ ∞ B (Iic 0 ×ˢ closedBall 0 ρ) ∧
        (∀ m E, IsCompact E → E ⊆ Iic 0 ×ˢ closedBall 0 ρ → TendstoUniformlyOn
          (fun k => iteratedFDerivWithin ℝ m
            (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
              ((G k).metric z.1).pullbackCoefficients (Φ k) z.2)
            (Iic 0 ×ˢ closedBall 0 ρ))
          (iteratedFDerivWithin ℝ m B (Iic 0 ×ˢ closedBall 0 ρ)) atTop E) ∧
        ∃ (U : Opens (EuclideanSpace ℝ (Fin n))) (hzeroU : 0 ∈ U),
          (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ ball 0 ρ ∧
          ∃ Flimit : RicciFlow n U (Iic 0),
            (∀ t ≤ 0, ∀ (x : U) (v w : EuclideanSpace ℝ (Fin n)),
              (Flimit.metric t).inner x v w = B (t, x) v w) ∧
            (∀ t ≤ 0, ∀ (x : U) (v : EuclideanSpace ℝ (Fin n)),
              (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ (Flimit.metric t).inner x v v) ∧
            (∀ t ≤ 0, ∀ x : U, (Flimit.connection t).NonnegativeCurvatureOperator x) ∧
            (Flimit.connection 0).scalarCurvature ⟨0, hzeroU⟩ = 1 ∧
            (∀ v w : EuclideanSpace ℝ (Fin n),
              (Flimit.metric 0).inner ⟨0, hzeroU⟩ v w = inner ℝ v w) ∧
            (∀ t ≤ 0, ∀ x : U,
              Tendsto (fun k => ((G k).connection t).scalarCurvature (Φ k x)) atTop
                (𝓝 ((Flimit.connection t).scalarCurvature x))) := by
  obtain ⟨K₀, S, ρ, hK₀, hS, hρ, hρS, σ, hσ, L₀, Φ,
    hcompleteG, hoperatorG, hcurvG, hscalarG, hcharts,
    _gTerminal, _DTerminal, _V, _hVo, _hzeroV, _hVS, _hVρ, _hnormTerminal, _hterminal,
    B, hB, _hterminalB, hnorm, hjets⟩ :=
    F.exists_normalized_annular_spacetime_limit hC hcomplete hoperator hK hbound
      hκ hnoncollapse hn t₀ ht₀ p q hQ hd hA hCnonneg hratio hdecay
  let G := fun k => F.ancientRescaleAt
    ((F.connection t₀).scalarCurvature (q (σ k))) (hQ (σ k)) t₀ ht₀
  have hsource (k : ℕ) : closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ ⊆ (Φ k).source := by
    rw [(hcharts k).1]
    exact closedBall_subset_ball (by linarith : ρ < S)
  have hconv (t : ℝ) (ht : t ≤ 0) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ ball 0 ρ) :
      Tendsto (fun k => ((G k).metric t).pullbackCoefficients (Φ k) x) atTop (𝓝 (B (t, x))) := by
    have hpoint : (t, x) ∈ Iic 0 ×ˢ closedBall 0 ρ := ⟨ht, ball_subset_closedBall hx⟩
    have hzerojet := hjets 0 {(t, x)} isCompact_singleton (singleton_subset_iff.mpr hpoint)
    have hvalue := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → ℝ × EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn hzerojet
    simpa only [Function.comp_def, iteratedFDerivWithin_zero_apply] using
      hvalue.tendsto_at (mem_singleton (t, x))
  have hslice : ContDiffOn ℝ ∞ (fun x => B (0, x)) (closedBall 0 ρ) :=
    hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x hx => ⟨by simp, hx⟩)
  have hcont : ContinuousAt (fun x => B (0, x)) 0 :=
    (hslice.contDiffAt (mem_of_superset
      (isOpen_ball.mem_nhds (mem_ball_self hρ)) ball_subset_closedBall)).continuousAt
  have hRic (k : ℕ) (t : ℝ) (ht : t ≤ 0) (x : M) (v : TangentSpace (𝓡 n) x) :
      0 ≤ ((G k).connection t).ricci x v v :=
    (((G k).connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus n M ((G k).metric t) ((G k).connection t)) x
      (hoperatorG k t ht x) v).1
  obtain ⟨hsymm, _hmono, V, hVo, hzeroV, hVρ, hlower⟩ :=
    exists_uniform_positive_neighborhood_of_normalized_ancient_limit G hRic
      (fun k => Φ k) isOpen_ball (mem_ball_self hρ) B hconv hcont hnorm
  let U : Opens (EuclideanSpace ℝ (Fin n)) := ⟨V, hVo⟩
  have hUρ : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ ball 0 ρ := hVρ
  obtain ⟨Flimit, hcoeff⟩ := exists_ancient_limit_of_partial_chart_coefficients
    hρ G Φ hsource U hUρ B hB
      (fun t ht x hx => hsymm t ht x (hUρ hx))
      (fun t ht x hx => ⟨1 / 2, by norm_num, hlower t ht x hx⟩) hjets
  have hcurvature := curvature_of_ancient_chart_coefficient_limit
    hρ G Φ hsource hoperatorG U hUρ Flimit B hB hcoeff hjets
  have hscalar : (Flimit.connection 0).scalarCurvature ⟨0, hzeroV⟩ = 1 := by
    apply tendsto_nhds_unique (hcurvature 0 (by simp) ⟨0, hzeroV⟩).2
    exact tendsto_const_nhds.congr (fun k => by
      change (1 : ℝ) = ((G k).connection 0).scalarCurvature (Φ k 0)
      rw [(hcharts k).2.2.1]
      exact (hscalarG k).symm)
  refine ⟨K₀, S, ρ, hK₀, hS, hρ, hρS, σ, hσ, L₀, Φ,
    hcompleteG, hoperatorG, hcurvG, hscalarG, hcharts, B, hB, hjets,
    U, hzeroV, hUρ, Flimit, hcoeff, ?_,
    (fun t ht x => (hcurvature t ht x).1), hscalar, ?_,
    (fun t ht x => (hcurvature t ht x).2)⟩
  · intro t ht x v
    rw [hcoeff t ht]
    exact hlower t ht x x.property v
  · intro v w
    exact (hcoeff 0 (by simp) ⟨0, hzeroV⟩ v w).trans (hnorm v w)

end PoincareConjecture.RicciFlow
