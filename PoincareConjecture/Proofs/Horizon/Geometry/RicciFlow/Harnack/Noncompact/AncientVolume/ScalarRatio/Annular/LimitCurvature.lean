import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.NormalizedLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.CurvatureLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Limit.RicciConvergence

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators ENNReal

namespace PoincareConjecture.LeviCivitaData

private theorem scalarCurvature_eq_inverse_gram
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x)) :
    D.scalarCurvature x = ∑ i, ∑ j,
      (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j * D.ricci x (b i) (b j) := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let B := ∑ i, D.curvatureTensor_bilinear_first_third x
    (g.orthonormalBasis x i) (g.orthonormalBasis x i)
  have h := bilinear_sum_basis_eq_inverse_gram (E := TangentSpace (𝓡 n) x)
    B b (g.orthonormalBasis x)
  change (∑ i, B (g.orthonormalBasis x i) (g.orthonormalBasis x i)) =
    ∑ i, ∑ j, (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j * B (b i) (b j) at h
  simpa only [B, LinearMap.sum_apply, curvatureTensor_bilinear_first_third_apply,
    ricci, scalarCurvature] using h

theorem tendsto_scalarCurvature_of_scalar_metric_jets
    {n : ℕ} {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ i, LeviCivitaData (gseq i)) (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin n)))
    (hjets : ∀ r : ℕ, r ≤ 2 → ∀ a c : ι,
      Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (gseq i).inner y (b a) (b c)) x) l
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x))) :
    Tendsto (fun i => (Dseq i).scalarCurvature x) l (𝓝 (D.scalarCurvature x)) := by
  classical
  have hzero := (RiemannianMetric.tendsto_euclideanCoefficients_of_scalar_jets x b hjets).1
  let Gseq : α → Matrix ι ι ℝ := fun k i j => (gseq k).inner x (b i) (b j)
  let G : Matrix ι ι ℝ := fun i j => g.inner x (b i) (b j)
  have hmatrix : Tendsto Gseq l (𝓝 G) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact ((ContinuousLinearMap.apply ℝ ℝ (b j)).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (b i)).continuous.tendsto _).comp hzero)
  have hdet : G.det ≠ 0 := by
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change (Matrix.gram ℝ (show Module.Basis ι ℝ (TangentSpace (𝓡 n) x) from b)).det ≠ 0
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr b.linearIndependent
  have hinv : Tendsto (fun i => (Gseq i)⁻¹) l (𝓝 G⁻¹) := by
    apply (continuousAt_matrix_inv G ?_).tendsto.comp hmatrix
    rw [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv]
    exact continuousAt_inv₀ hdet
  simp_rw [scalarCurvature_eq_inverse_gram _ x b]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hinv i)) j).mul
    (tendsto_ricci_of_scalar_metric_jets Dseq D x (b i) (b j) b hjets)

private theorem scalar_jets_of_bilinear_jets
    {n : ℕ} {gseq : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (x a b : EuclideanSpace ℝ (Fin n)) (r : ℕ)
    (h : Tendsto (fun k => iteratedFDeriv ℝ r (gseq k).euclideanCoefficients x)
      atTop (𝓝 (iteratedFDeriv ℝ r g.euclideanCoefficients x))) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun y => (gseq k).inner y a b) x)
      atTop (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y a b) x)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ b).comp
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) a)
  have heq (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) :
      iteratedFDeriv ℝ r (fun y => g'.inner y a b) x =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ r g'.euclideanCoefficients x) := by
    ext v
    exact g'.iteratedFDeriv_inner_eq x a b r v
  have hpost := ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin r => E) (E →L[ℝ] E →L[ℝ] ℝ) ℝ L).continuous.tendsto _).comp h
  change Tendsto (fun k => L.compContinuousMultilinearMap
    (iteratedFDeriv ℝ r (gseq k).euclideanCoefficients x)) atTop
    (𝓝 (L.compContinuousMultilinearMap (iteratedFDeriv ℝ r g.euclideanCoefficients x))) at hpost
  rw [← heq g] at hpost
  exact hpost.congr (fun k => (heq (gseq k)).symm)

theorem curvature_of_partialDiffeomorph_metric_jets
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (gseq : ℕ → RiemannianMetric n M) (Dseq : ∀ k, LeviCivitaData (gseq k))
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ∀ k, x ∈ (Φ k).source)
    (hjets : ∀ r : ℕ, r ≤ 2 →
      Tendsto (fun k => iteratedFDeriv ℝ r ((gseq k).pullbackCoefficients (Φ k)) x)
        atTop (𝓝 (iteratedFDeriv ℝ r g.euclideanCoefficients x)))
    (hpos : ∀ᶠ k in atTop, (Dseq k).NonnegativeCurvatureOperator (Φ k x)) :
    D.NonnegativeCurvatureOperator x ∧
      Tendsto (fun k => (Dseq k).scalarCurvature (Φ k x)) atTop
        (𝓝 (D.scalarCurvature x)) := by
  have hreal (k : ℕ) :
      ∃ (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (_D' : LeviCivitaData g') (V : Set (EuclideanSpace ℝ (Fin n))),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (Φ k).source ∧
          ∀ y ∈ V, g'.euclideanCoefficients y = (gseq k).pullbackCoefficients (Φ k) y := by
    apply RiemannianMetric.exists_local_realization (Φ k).open_source (hx k)
      ((gseq k).pullbackCoefficients (Φ k))
    · intro y hy
      exact ((gseq k).contDiffAt_pullbackCoefficients
        ((Φ k).contMDiffOn.contMDiffAt ((Φ k).open_source.mem_nhds hy))).contDiffWithinAt
    · intro y _ a b
      exact (gseq k).symm (Φ k y) _ _
    · intro y hy v hv
      apply (gseq k).pos (Φ k y)
      intro hz
      apply hv
      have hd : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ (Φ k) y :=
        ⟨Φ k, hy, Set.eqOn_refl _ _⟩
      apply (hd.mfderivToContinuousLinearEquiv (by simp)).injective
      change mfderiv (𝓡 n) (𝓡 n) (Φ k) y v = mfderiv (𝓡 n) (𝓡 n) (Φ k) y 0
      rw [map_zero]
      convert! hz using 1
  choose gs Ds V hVo hxV hVsource heq using hreal
  have hmetric (k : ℕ) : ∀ y ∈ V k, ∀ a b : TangentSpace (𝓡 n) y,
      (gs k).inner y a b = (gseq k).inner (Φ k y)
        (mfderiv (𝓡 n) (𝓡 n) (Φ k) y a) (mfderiv (𝓡 n) (𝓡 n) (Φ k) y b) := by
    intro y hy a b
    exact congrArg (fun B => B a b) (heq k y hy)
  have hscal (k : ℕ) : (Ds k).scalarCurvature x = (Dseq k).scalarCurvature (Φ k x) :=
    (Ds k).scalarCurvature_eq_of_local_isometry (Dseq k) (hVo k)
      ((Φ k).contMDiffOn.mono (hVsource k)) (hmetric k) (hxV k)
  have hpositive : ∀ᶠ k in atTop, (Ds k).NonnegativeCurvatureOperator x := by
    filter_upwards [hpos] with k hk
    exact ((Ds k).nonnegativeCurvatureOperator_iff_of_local_isometry (Dseq k) (hVo k)
      ((Φ k).contMDiffOn.mono (hVsource k)) (hmetric k) (hxV k)).2 hk
  have hbilinear (r : ℕ) (hr : r ≤ 2) :
      Tendsto (fun k => iteratedFDeriv ℝ r (gs k).euclideanCoefficients x)
        atTop (𝓝 (iteratedFDeriv ℝ r g.euclideanCoefficients x)) := by
    apply (hjets r hr).congr
    intro k
    symm
    have hevent : (gs k).euclideanCoefficients =ᶠ[𝓝 x] (gseq k).pullbackCoefficients (Φ k) :=
      Filter.Eventually.mono ((hVo k).mem_nhds (hxV k)) (heq k)
    exact (hevent.iteratedFDeriv ℝ r).self_of_nhds
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hscalar (r : ℕ) (hr : r ≤ 2) (a c : Fin n) :
      Tendsto (fun k => iteratedFDeriv ℝ r (fun y => (gs k).inner y (b a) (b c)) x)
        atTop (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x)) :=
    scalar_jets_of_bilinear_jets x (b a) (b c) r (hbilinear r hr)
  refine ⟨nonnegativeCurvatureOperator_of_scalar_metric_jets Ds D x b hscalar hpositive, ?_⟩
  exact (tendsto_scalarCurvature_of_scalar_metric_jets Ds D x b hscalar).congr hscal

theorem curvature_of_partialDiffeomorph_metric_limit
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (gseq : ℕ → RiemannianMetric n M) (Dseq : ∀ k, LeviCivitaData (gseq k))
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hzero : 0 ∈ V)
    (hsource : ∀ k, V ⊆ (Φ k).source)
    (hjets : ∀ r E, IsCompact E → E ⊆ V → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ r ((gseq k).pullbackCoefficients (Φ k)))
      (iteratedFDeriv ℝ r g.euclideanCoefficients) atTop E)
    (hpos : ∀ k, ∀ x ∈ V, (Dseq k).NonnegativeCurvatureOperator (Φ k x))
    (hscalar : ∀ k, (Dseq k).scalarCurvature (Φ k 0) = 1) :
    (∀ x ∈ V, D.NonnegativeCurvatureOperator x) ∧ D.scalarCurvature 0 = 1 := by
  have hpoint (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ V) :=
    curvature_of_partialDiffeomorph_metric_jets gseq Dseq Φ D x
      (fun k => hsource k hx)
      (fun r _ => (hjets r {x} isCompact_singleton (singleton_subset_iff.mpr hx)).tendsto_at
        (mem_singleton x))
      (Eventually.of_forall (fun k => hpos k x hx))
  refine ⟨fun x hx => (hpoint x hx).1, ?_⟩
  apply tendsto_nhds_unique (hpoint 0 hzero).2
  exact tendsto_const_nhds.congr (fun k => (hscalar k).symm)

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RicciFlow

universe u

set_option maxHeartbeats 600000 in

theorem exists_terminal_normalized_annular_metric_limit_with_curvature
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
    ∃ B S : ℝ, 0 < B ∧ 0 < S ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ L₀ : ℕ → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      let G := fun k => F.ancientRescaleAt
        ((F.connection t₀).scalarCurvature (q (σ k))) (hQ (σ k)) t₀ ht₀
      (∀ k s, s ≤ 0 → ∀ x ∈ ((G k).metric 0).ball (q (σ k)) (2 * S),
        ((G k).connection s).curvatureTensorNorm x ≤ B) ∧
      (∀ k, ((G k).connection 0).scalarCurvature (q (σ k)) = 1) ∧
      (∀ k, (Φ k).source = Metric.ball 0 S ∧
        (Φ k).target = ((G k).metric 0).ball (q (σ k)) S ∧ Φ k 0 = q (σ k) ∧
        (∀ v w, ((G k).metric 0).pullbackCoefficients
          (extChartAt (𝓡 n) (q (σ k))).symm (extChartAt (𝓡 n) (q (σ k)) (q (σ k)))
            (L₀ k v) (L₀ k w) = inner ℝ v w) ∧
        HasFDerivAt (fun w => extChartAt (𝓡 n) (q (σ k)) (Φ k w))
          (L₀ k).toContinuousLinearMap 0 ∧
        (∀ w ∈ Metric.ball 0 S, ((G k).metric 0).IsGeodesicOn
          (fun t => Φ k (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 S}) ∧
        ∀ w ∈ Metric.ball 0 S,
          ((G k).metric 0).edist (q (σ k)) (Φ k w) = ENNReal.ofReal ‖w‖) ∧
      ∃ (gLimit : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (D : LeviCivitaData gLimit) (V : Set (EuclideanSpace ℝ (Fin n))),
        IsOpen V ∧ 0 ∈ V ∧ V ⊆ Metric.ball 0 (S / 4) ∧
        (∀ v w, gLimit.inner 0 v w = inner ℝ v w) ∧
        (∀ x ∈ V, D.NonnegativeCurvatureOperator x) ∧ D.scalarCurvature 0 = 1 ∧
        (∀ m E, IsCompact E → E ⊆ V → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (((G k).metric 0).pullbackCoefficients (Φ k)))
          (iteratedFDeriv ℝ m gLimit.euclideanCoefficients) atTop E) := by
  obtain ⟨B, S, hB, hS, σ, hσ, L₀, Φ, hcurv, hscalar, hchart,
      gLimit, D, V, hVo, hzeroV, hVS, hnorm, hjets⟩ :=
    F.exists_terminal_normalized_annular_metric_limit hC hcomplete hoperator hK hbound
      hκ hnoncollapse hn t₀ ht₀ p q hQ hd hA hCnonneg hratio hdecay
  let G := fun k => F.ancientRescaleAt
    ((F.connection t₀).scalarCurvature (q (σ k))) (hQ (σ k)) t₀ ht₀
  have hVsource (k : ℕ) : V ⊆ (Φ k).source := by
    rw [(hchart k).1]
    exact hVS.trans (Metric.ball_subset_ball (by linarith : S / 4 ≤ S))
  have hpos (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) (_hx : x ∈ V) :
      ((G k).connection 0).NonnegativeCurvatureOperator (Φ k x) := by
    apply F.parabolicRescale_nonnegativeCurvatureOperator
    exact hoperator _ (by simpa only [zero_div, add_zero] using ht₀) _
  have hscalar' (k : ℕ) : ((G k).connection 0).scalarCurvature (Φ k 0) = 1 := by
    rw [(hchart k).2.2.1]
    exact hscalar k
  obtain ⟨hpositive, hone⟩ := LeviCivitaData.curvature_of_partialDiffeomorph_metric_limit
    (fun k => (G k).metric 0) (fun k => (G k).connection 0) Φ D hzeroV
    hVsource hjets hpos hscalar'
  exact ⟨B, S, hB, hS, σ, hσ, L₀, Φ, hcurv, hscalar, hchart,
    gLimit, D, V, hVo, hzeroV, hVS, hnorm, hpositive, hone, hjets⟩

end PoincareConjecture.RicciFlow
