import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.BackwardFlatAnnulus
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.CurvatureDecay
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.NeighborhoodMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.UnitPotential
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.UnitMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.UnitLink.Connected
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Backward.EnclosingCharts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Backward.NestedRescaling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Backward.GlobalEnclosedLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hypersurface.HomotheticRadialPotential
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompactImages
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompactNeighborhood

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set Filter PoincareConjecture Poincare.Gluing Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace Poincare.AncientVolume.ScalarRatio

private theorem rescaled_pullback_jets
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X]
    (gseq : ℕ → RiemannianMetric n X) (g : RiemannianMetric n X)
    (c : ℝ) (hc : 0 < c) (a : EuclideanSpace ℝ (Fin n) → X)
    {U C : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (ha : ContMDiffOn (𝓡 n) (𝓡 n) ∞ a U) (hCU : C ⊆ U) (m : ℕ)
    (hlim : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((gseq k).pullbackCoefficients a))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients a)) atTop C) :
    TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((rescaledMetric (gseq k) c hc).pullbackCoefficients a))
      (iteratedFDeriv ℝ m ((rescaledMetric g c hc).pullbackCoefficients a)) atTop C := by
  have hcoeff (g : RiemannianMetric n X) :
      (rescaledMetric g c hc).pullbackCoefficients a =
        fun x => c • g.pullbackCoefficients a x := by
    funext x
    ext v w
    exact rescaledMetric_inner g c hc _ _ _
  have hjet (g : RiemannianMetric n X) (x) (hx : x ∈ U) :
      iteratedFDeriv ℝ m ((rescaledMetric g c hc).pullbackCoefficients a) x =
        c • iteratedFDeriv ℝ m (g.pullbackCoefficients a) x := by
    rw [hcoeff]
    exact iteratedFDeriv_const_smul_apply'
      ((g.contDiffAt_pullbackCoefficients
        (ha.contMDiffAt (hU.mem_nhds hx))).of_le (by exact_mod_cast le_top))
  apply (((uniformContinuous_const_smul c).comp_tendstoUniformlyOn hlim).congr ?_).congr_right
  · exact fun x hx => (hjet g x (hCU hx)).symm
  · exact Eventually.of_forall fun k x hx => (hjet (gseq k) x (hCU hx)).symm

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RicciFlow

private theorem terminal_distance_le_backward_of_nonnegative_operator
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (x y : M) :
    ((F.metric 0).edist x y).toReal ≤ ((F.metric (-1)).edist x y).toReal := by
  have hinner (z : M) (v : TangentSpace (𝓡 n) z) :
      (F.metric 0).inner z v v ≤ (F.metric (-1)).inner z v v :=
    F.antitoneOn_metric_inner_self_on_ancient_of_ricci_nonneg z v
      (fun t ht => ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
        (hC.tensor_calculus n M (F.metric t) (F.connection t)) z
        (hoperator t ht z) v).1) (by norm_num) (by norm_num) (by norm_num)
  have hdist : (F.metric 0).edist x y ≤ (F.metric (-1)).edist x y := by
    simpa only [id_eq, ENNReal.ofReal_one, one_mul] using
      (F.metric (-1)).edist_le_mul_of_inner_mfderiv_le (F.metric 0)
        (F := id) contMDiff_id zero_lt_one (fun z v => by
          simpa only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq, one_pow, one_mul]
            using hinner z v) x y
  exact ENNReal.toReal_mono ((F.metric (-1)).edist_ne_top x y) hdist

theorem exists_unitSlice_euclidean_umbilic_of_zero_ratio
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 2))) M] [IsManifold (𝓡 (n + 2)) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (n + 2) M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ (n + 2)) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M)
    (hzero : ∀ C : ℝ, 0 < C → ∃ L : ℝ, ∀ x : M,
      L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C) :
    letI := (F.metric t₀).toMetricSpace
    let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
      (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        x (hoperator t₀ ht₀ x) v w
    let hc := (F.metric t₀).rayComparison_of_metricComplete
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p
    let hcover := F.unitSliceRadialAtlas_covers_of_zero_ratio hC hcomplete hoperator
      hK hbound hκ hnoncollapse t₀ ht₀ p hzero
    letI := unitSliceChartedSpace hc (n + 1) hcover
    letI := unitSlice_isManifold hc (n + 1) hcover
    ∃ f N : AsymptoticConeUnitSlice p hc → EuclideanSpace ℝ (Fin (n + 2)),
      ContMDiff (𝓡 (n + 1)) (𝓡 (n + 2)) ∞ f ∧
      ContMDiff (𝓡 (n + 1)) (𝓡 (n + 2)) ∞ N ∧
      (∀ z, Function.Injective (mfderiv (𝓡 (n + 1)) (𝓡 (n + 2)) f z)) ∧
      (∀ z, ‖N z‖ = 1) ∧
      (∀ z, mfderiv (𝓡 (n + 1)) (𝓡 (n + 2)) N z =
        mfderiv (𝓡 (n + 1)) (𝓡 (n + 2)) f z) ∧
      (∀ x y, dist x y ≤ dist (f x) (f y)) ∧
      ∀ z (v w : TangentSpace (𝓡 (n + 1)) z),
        (unitSliceMetric hcover).inner z v w =
          inner ℝ (mfderiv (𝓡 (n + 1)) (𝓡 (n + 2)) f z v)
            (mfderiv (𝓡 (n + 1)) (𝓡 (n + 2)) f z w) := by
  classical
  let := (F.metric t₀).toMetricSpace
  let := (F.metric t₀).properSpace_toMetricSpace (hcomplete t₀ ht₀)
  let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
    (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t₀ ht₀ x) v w
  let hc := (F.metric t₀).rayComparison_of_metricComplete
    (F.connection t₀) (hcomplete t₀ ht₀) hsec p
  let hcover := F.unitSliceRadialAtlas_covers_of_zero_ratio hC hcomplete hoperator
    hK hbound hκ hnoncollapse t₀ ht₀ p hzero
  let hne := nonempty_asymptoticConePositive_of_unitSlice hc
    (nonempty_asymptoticConeUnitSlice hc
      ((F.metric t₀).nonempty_basedMinimizingRays (hcomplete t₀ ht₀) p))
  let := unitSliceChartedSpace hc (n + 1) hcover
  let := unitSlice_isManifold hc (n + 1) hcover
  let := positiveConeChartedSpace hc (n + 1) hne hcover
  let := positiveCone_isManifold hc (n + 1) hne hcover
  letI : PathConnectedSpace (AsymptoticConeUnitSlice p hc) :=
    F.unitSlice_pathConnected_of_zero_ratio (by omega) hC hcomplete hoperator
      hK hbound hκ hnoncollapse t₀ ht₀ p hzero
  let z₀ : AsymptoticConeUnitSlice p hc := Classical.choice inferInstance
  obtain ⟨r, hr, σ, hσ, h, D, hnorm, hflat, O, hO, f, hfopen, hfpos, hfdist,
    hfunit, hfcompact, V, hV, hVcompact, hKV, A, hA, hmetric, hrad, hannulus, hpairs⟩ :=
    F.exists_backward_flat_annular_source_geometry_of_zero_ratio hC hcomplete hoperator
      hK hbound hκ hnoncollapse (by omega) t₀ ht₀ p hzero
  let U := fun _ : ℕ => Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 2))) r
  let hU : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_ball
  let : ∀ i, Nonempty (Piece U i) := fun _ => ⟨⟨0, Metric.mem_ball_self hr⟩⟩
  let := quotientChartedSpace U hU O
  let := hO
  let fP := positiveConeRealization hc f hfpos
  have hfP : Topology.IsOpenEmbedding fP :=
    isOpenEmbedding_positiveConeRealization hc f hfpos hfopen
  have hunit : {a : AsymptoticConePositive p hc | asymptoticConeRadius hc a.val = 1} ⊆
      range fP := unitSlice_subset_range_positiveConeRealization hc f hfpos hfunit
  have hdist : ∀ j (x y : Piece U j), dist (fP (O.include j x)) (fP (O.include j y)) =
      ((h j).edist x y).toReal := hfdist
  have hlocal := (isLocalDiffeomorph_positiveCone_realization hc hne hcover
    U hU O h fP hfP hdist).2
  let : T2Space (Quotient O.setoid) := hfP.isEmbedding.t2Space
  let : SecondCountableTopology (Quotient O.setoid) := O.quotient_secondCountableTopology
  let V' : TopologicalSpace.Opens (Quotient O.setoid) := ⟨V, hV⟩
  let Q := fun k : ℕ => ((σ k : ℝ) + 1)⁻¹ ^ 2
  let hQ : ∀ k, 0 < Q k := fun k => by dsimp [Q]; positivity
  let G := fun k => F.ancientRescaleAt (Q k) (hQ k) t₀ ht₀
  let g0 := positiveConeRealizationMetric hc hne hcover U hU O h fP hfP hdist
  let gV := g0.pullbackOfLocalDiffeomorph Subtype.val
    (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 (n + 2)) V')
  let u0 := positiveConeRadialPotential hc ∘ fP
  let uV := fun x : V' => u0 x
  let b := unitSlicePreimageInOpen hc fP hunit V' hKV
  have hb := unitSlicePreimageInOpen_geometry
    (hc := hc) (hne := hne) (hcover := hcover) (f := fP) (hf := hfP)
    (hunit := hunit) (V := V') (hKV := hKV) hlocal
  have hu0 := positiveConeRealizationMetric_radialPotential hc hne hcover U hU O h fP hfP hdist
  have huV := RiemannianMetric.radialPotential_on_open g0 u0 hu0.1 hu0.2.1 hu0.2.2 V'
  let AV : ℕ → V' → M := fun k x => A k x
  have hAV : ∀ᶠ k in atTop,
      IsLocalDiffeomorph (𝓡 (n + 2)) (𝓡 (n + 2)) ∞ (AV k) := by
    filter_upwards [hA] with k hk x
    exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 (n + 2)) V' x).comp
      (𝓡 (n + 2)) M (hk.2 x)
  have hQunit : ∀ z, gV.leviCivitaData.levelQ uV (b z) = 1 := by
    intro z
    rw [huV.2.2]
    change 2 * positiveConeRadialPotential hc (fP (b z)) = 1
    rw [hb.2.2.2]
    norm_num
  have hjetsAt (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0) :
      ∀ z ∈ V, ∃ j, ∃ W : Set (Piece U j), IsOpen W ∧
      z ∈ O.include j '' W ∧ O.include j '' W ⊆ V ∧
      ∀ m C, IsCompact C → C ⊆ Subtype.val '' W → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (((G k).metric s).pullbackCoefficients
          (ChartDistance.chartParametrization U hU (A k ∘ O.include j))))
        (iteratedFDeriv ℝ m (h j).euclideanCoefficients) atTop C := by
    intro z hz
    obtain ⟨j, W, hW, hzW, hWV, hj⟩ := hmetric z hz
    refine ⟨j, W, hW, hzW, hWV, ?_⟩
    intro m C hC hCW
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hj m C hC hCW) ε hε]
      with k hk x hx
    exact hk (s, x) ⟨hs, hx⟩
  obtain ⟨gseq, hgseq, hcharts⟩ :=
    exists_neighborhood_metrics_of_positive_cone_source_jets
      hc hne hcover U hU O h fP hfP hdist (fun k => (G k).metric (-1)) V' A
      (hA.mono fun _ hk => hk.2) (hjetsAt (-1) (by norm_num))
  obtain ⟨d, hd, hdiam⟩ :=
    RiemannianMetric.exists_uniform_image_distance_bound_of_chart_convergence
      (RiemannianMetric.Induced.pullbackMetric gV b hb.1 hb.2.1)
      gV gseq (fun k => (G k).metric (-1)) hb.1 (fun _ _ _ => rfl)
      (hAV.mono fun _ hk => hk.contMDiff) (hgseq.mono fun _ hk => hk.2)
      (fun q _ => by
        obtain ⟨c, hqc, hcd, _, hc0, _⟩ := hcharts q
        exact ⟨c, hqc, hcd, hc0⟩)
  obtain ⟨W, hW, hbW, C, hCpos, hWdist⟩ :=
    RiemannianMetric.exists_open_uniform_image_distance_bound gV gseq
      (fun k => (G k).metric (-1)) AV (fun k => AV k (b z₀)) hb.2.2.1
      (hAV.mono fun _ hk => hk.contMDiff) (hgseq.mono fun _ hk => hk.2)
      (fun q _ => by
        obtain ⟨c, hqc, hcd, _, hc0, _⟩ := hcharts q
        exact ⟨c, hqc, hcd, hc0⟩) (by
        filter_upwards [hdiam] with k hk x hx
        obtain ⟨z, rfl⟩ := hx
        exact hk z z₀)
  have hdecay := ChartDistance.eventually_curvatureTensorNorm_lt_on_compact_of_local_metric_jets
    U hU O (fun k => (G k).connection 0) h D hflat A
      (hjetsAt 0 (by norm_num)) hfcompact hKV hO (hA.mono fun _ hk => hk.2)
  have hbmem (z : AsymptoticConeUnitSlice p hc) :
      (b z : Quotient O.setoid) ∈ f ⁻¹' {a | asymptoticConeRadius hc a = 1} := by
    change asymptoticConeRadius hc (f (unitSlicePreimage hc fP hunit z)) = 1
    rw [show f (unitSlicePreimage hc fP hunit z) = z.val from
      congrArg Subtype.val (apply_unitSlicePreimage hc fP hunit z)]
    exact z.property
  have hscalar : Tendsto (fun k => ((G k).connection 0).scalarCurvature (AV k (b z₀)))
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hdim : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) ^ 2 := by positivity
    filter_upwards [hdecay (ε / ((n + 2 : ℕ) : ℝ) ^ 2) (div_pos hε hdim)] with k hk
    rw [Real.dist_eq, sub_zero]
    calc
      |((G k).connection 0).scalarCurvature (AV k (b z₀))| ≤
          ((n + 2 : ℕ) : ℝ) ^ 2 * ((G k).connection 0).curvatureTensorNorm (AV k (b z₀)) :=
        ((G k).connection 0).abs_scalarCurvature_le_curvatureTensorNorm _
      _ < ((n + 2 : ℕ) : ℝ) ^ 2 * (ε / ((n + 2 : ℕ) : ℝ) ^ 2) :=
        mul_lt_mul_of_pos_left (hk _ (hbmem z₀)) hdim
      _ = ε := by field_simp
  obtain ⟨c, hcpos, hcd, τ, hτ, L, Φ, hchart, hΦjetsRaw⟩ :=
    F.exists_backward_enclosing_euclidean_charts hC hcomplete hoperator hK hbound
      hκ hnoncollapse (by omega) t₀ ht₀ Q hQ (fun k => AV k (b z₀))
      (fun k => AV k '' W) hscalar (by
        filter_upwards [hWdist] with k hk x hx
        obtain ⟨z, hz, rfl⟩ := hx
        exact hk z hz)
  let ρ := RiemannianMetric.localInjectivityRadius (n + 2) 1 1 κ
  have hρ : 0 < ρ := RiemannianMetric.localInjectivityRadius_pos (n + 2) 1
    (by norm_num) κ
  let W' : TopologicalSpace.Opens V' := ⟨W, hW⟩
  letI : Nonempty W' := ⟨⟨b z₀, hbW (mem_range_self z₀)⟩⟩
  let heW := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 (n + 2)) W'
  let gW := gV.pullbackOfLocalDiffeomorph Subtype.val heW
  let gWseq := fun k => (gseq k).pullbackOfLocalDiffeomorph Subtype.val heW
  let bW : AsymptoticConeUnitSlice p hc → W' := fun z => ⟨b z, hbW (mem_range_self z)⟩
  let uW : W' → ℝ := fun x => uV x
  have hbWs : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 2)) ∞ bW := by
    intro z
    exact (ContMDiffAt.subtypeVal_comp_iff W' bW z).mp (hb.1 z)
  have hdbW (z) :
      (mfderiv (𝓡 (n + 2)) (𝓡 (n + 2)) (Subtype.val : W' → V') (bW z)).comp
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 2)) bW z) =
          mfderiv (𝓡 (n + 1)) (𝓡 (n + 2)) b z := by
    rw [← mfderiv_comp z (heW.mdifferentiable (by simp) (bW z))
      (hbWs.mdifferentiable (by simp) z)]
    rfl
  have hbWi : ∀ z, Function.Injective (mfderiv (𝓡 (n + 1)) (𝓡 (n + 2)) bW z) := by
    intro z v w hvw
    apply hb.2.1 z
    have h := congrArg (mfderiv (𝓡 (n + 2)) (𝓡 (n + 2))
      (Subtype.val : W' → V') (bW z)) hvw
    simpa only [← ContinuousLinearMap.comp_apply, hdbW] using h
  have huW := RiemannianMetric.radialPotential_on_open gV uV
    huV.1 huV.2.1 huV.2.2 W'
  have hunitW : ∀ z, gW.inner (bW z)
      (gW.leviCivitaData.gradient uW (bW z)) (gW.leviCivitaData.gradient uW (bW z)) = 1 := by
    intro z
    change gW.leviCivitaData.levelQ uW (bW z) = 1
    rw [huW.2.2]
    change 2 * positiveConeRadialPotential hc (fP (b z)) = 1
    rw [hb.2.2.2]
    norm_num
  have hlinkMetric : ∀ z (v w : TangentSpace (𝓡 (n + 1)) z),
      (unitSliceMetric hcover).inner z v w = gW.inner (bW z)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 2)) bW z v)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 2)) bW z w) := by
    intro z v w
    have hh := unitSlicePreimageInOpen_inner hc hne hcover fP hfP hunit V' hKV hlocal z v w
    change (unitSliceMetric hcover).inner z v w = gV.inner (b z)
      (((mfderiv (𝓡 (n + 2)) (𝓡 (n + 2)) (Subtype.val : W' → V') (bW z)).comp
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 2)) bW z)) v)
      (((mfderiv (𝓡 (n + 2)) (𝓡 (n + 2)) (Subtype.val : W' → V') (bW z)).comp
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 2)) bW z)) w)
    rw [hdbW]
    exact hh
  have hWcharts := convergent_metric_charts_on_open gV gseq
    (fun x => by
      obtain ⟨e, hxe, he, hj, _, _⟩ := hcharts x
      exact ⟨e, hxe, he, hj⟩) W'
  let gC := rescaledMetric gW c hcpos
  let gCseq := fun k => rescaledMetric (gWseq (τ k)) c hcpos
  let gM := fun k => rescaledMetric ((G (τ k)).metric (-1)) c hcpos
  have hscale (k : ℕ) :
      (F.ancientRescaleAt (c * Q (τ k)) (mul_pos hcpos (hQ (τ k)))
        (t₀ - 1 / Q (τ k))
        (sub_nonpos.mpr (ht₀.trans (one_div_nonneg.mpr (hQ (τ k)).le)))).metric 0 =
        gM k :=
    F.ancientRescaleAt_backward_metric_zero c hcpos (Q (τ k)) (hQ (τ k)) t₀ ht₀ _
  have hΦjets : ∀ m T, IsCompact T → T ⊆ Metric.ball 0 (ρ / 4) → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((gM k).pullbackCoefficients (Φ k)))
      (iteratedFDeriv ℝ m (fun _ : EuclideanSpace ℝ (Fin (n + 2)) => innerSL ℝ))
      atTop T := by
    intro m T hT hsub
    simpa only [hscale] using hΦjetsRaw m T hT hsub
  let AW : ℕ → W' → M := fun k x => AV (τ k) x
  have hAW : ∀ᶠ k in atTop, ContMDiff (𝓡 (n + 2)) (𝓡 (n + 2)) ∞ (AW k) := by
    filter_upwards [hτ.tendsto_atTop.eventually hAV] with k hk
    exact hk.contMDiff.comp heW.contMDiff
  have hAWmetric : ∀ᶠ k in atTop, ∀ x v w,
      (gCseq k).inner x v w = (gM k).inner (AW k x)
        (mfderiv (𝓡 (n + 2)) (𝓡 (n + 2)) (AW k) x v)
        (mfderiv (𝓡 (n + 2)) (𝓡 (n + 2)) (AW k) x w) := by
    filter_upwards [hτ.tendsto_atTop.eventually hgseq] with k hk x v w
    rw [show AW k = AV (τ k) ∘ Subtype.val from rfl,
      mfderiv_comp x (hk.1.mdifferentiable (by simp) x.val)
        (heW.mdifferentiable (by simp) x)]
    change c * (gseq (τ k)).inner x.val
      (mfderiv (𝓡 (n + 2)) (𝓡 (n + 2)) (Subtype.val : W' → V') x v)
      (mfderiv (𝓡 (n + 2)) (𝓡 (n + 2)) (Subtype.val : W' → V') x w) = _
    rw [hk.2]
    rfl
  have hCcharts : ∀ x : W', ∃ e : OpenPartialHomeomorph W' (EuclideanSpace ℝ (Fin (n + 2))),
      x ∈ e.source ∧ IsLocalDiffeomorphOn (𝓡 (n + 2)) (𝓡 (n + 2)) ∞ e.symm e.target ∧
      ∀ m T, IsCompact T → T ⊆ e.target → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m ((gCseq k).pullbackCoefficients e.symm))
        (iteratedFDeriv ℝ m (gC.pullbackCoefficients e.symm)) atTop T := by
    intro x
    obtain ⟨e, hxe, he, hj⟩ := hWcharts x
    refine ⟨e, hxe, he, ?_⟩
    intro m T hT hTe
    apply rescaled_pullback_jets (fun k => gWseq (τ k)) gW c hcpos e.symm
      e.open_target he.contMDiffOn hTe m
    exact fun u hu => hτ.tendsto_atTop.eventually (hj m T hT hTe u hu)
  have hsource : ∀ k, (Φ k).source = Metric.ball 0 ρ := fun k => (hchart k).1
  have htarget : ∀ k, (Φ k).target = (gM k).ball (AV (τ k) (b z₀)) ρ :=
    by
      intro k
      rw [← hscale k]
      exact (hchart k).2.1
  have hΦradial : ∀ k x, x ∈ Metric.ball 0 ρ →
      (gM k).edist (AV (τ k) (b z₀)) (Φ k x) = ENNReal.ofReal ‖x‖ :=
    by
      intro k
      rw [← hscale k]
      exact (hchart k).2.2.2.2.2.2.2.1
  have hinside : ∀ k (x : W'), AW k x ∈ (gM k).ball (AV (τ k) (b z₀)) (ρ / 8) := by
    intro k x
    rw [← hscale k]
    exact (hchart k).2.2.2.1 (mem_image_of_mem _ x.property)
  have hcoordTarget (k : ℕ) (x : W') : AW k x ∈ (Φ k).target := by
    rw [htarget k]
    exact (hinside k x).trans_le (ENNReal.ofReal_le_ofReal (by linarith : ρ / 8 ≤ ρ))
  have hcoordRight (k : ℕ) (x : W') : Φ k ((Φ k).symm (AW k x)) = AW k x :=
    (Φ k).right_inv (hcoordTarget k x)
  have hcoordInside (k : ℕ) (x : W') : (Φ k).symm (AW k x) ∈ Metric.ball 0 (ρ / 8) := by
    have he := hΦradial k ((Φ k).symm (AW k x))
      (hsource k ▸ (Φ k).map_target (hcoordTarget k x))
    rw [hcoordRight] at he
    have hh := hinside k x
    change (gM k).edist (AV (τ k) (b z₀)) (AW k x) < ENNReal.ofReal (ρ / 8) at hh
    rw [he, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)] at hh
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  obtain ⟨υ, hυ, J, hJ, hJi, hJmetric, hJrange, hJlim⟩ :=
    exists_global_enclosed_smooth_limit gC gCseq gM AW (fun k => AV (τ k) (b z₀))
      hAW hAWmetric hCcharts Φ (by linarith : ρ / 8 < ρ / 4)
      (by linarith : ρ / 4 < ρ) hsource htarget hΦradial
      (Eventually.of_forall hinside) hΦjets
  obtain ⟨fE, N, hfEeq, hfE, hN, hfEi, hNunit, hNderiv, hfEmetric⟩ :=
    Poincare.Geometry.Riemannian.Hypersurface.exists_unit_umbilic_of_homothetic_radial_potential
      gW.leviCivitaData hcpos hJ hJmetric huW.1 huW.2.1 hbWs hbWi hunitW
  refine ⟨fE, N, hfE, hN, hfEi, hNunit, hNderiv, ?_, ?_⟩
  · intro x y
    have hfpre (z : AsymptoticConeUnitSlice p hc) : f (b z) = z.val :=
      congrArg Subtype.val (apply_unitSlicePreimage hc fP hunit z)
    have hpair : Tendsto
        (fun k => (((G k).metric 0).edist (AV k (b x)) (AV k (b y))).toReal)
        atTop (𝓝 (dist x y)) := by
      have hdistval : dist x y = dist (x.val : AsymptoticCone p hc) y.val := rfl
      rw [hdistval]
      have hh := (hpairs _ hfcompact hKV).tendsto_at (x := ((b x).val, (b y).val))
        ⟨hbmem x, hbmem y⟩
      change Tendsto
        (fun k => (((G k).metric 0).edist (AV k (b x)) (AV k (b y))).toReal)
        atTop (𝓝 (dist (f (b x)) (f (b y)))) at hh
      simpa only [hfpre, Subtype.dist_eq] using hh
    have hoperatorG : ∀ k t, t ≤ 0 → ∀ z,
        ((G k).connection t).NonnegativeCurvatureOperator z := by
      intro k t ht z
      apply F.parabolicRescale_nonnegativeCurvatureOperator
      exact hoperator _
        ((add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg ht (hQ k).le)).trans ht₀) z
    have hcoeff : TendstoUniformlyOn
        (fun k => (gM (υ k)).pullbackCoefficients (Φ (υ k)))
        (fun _ : EuclideanSpace ℝ (Fin (n + 2)) => innerSL ℝ)
        atTop (Metric.closedBall 0 (ρ / 6)) := by
      have hh := hΦjets 0 (Metric.closedBall 0 (ρ / 6)) (isCompact_closedBall _ _)
        (Metric.closedBall_subset_ball (by linarith : ρ / 6 < ρ / 4))
      have hz := (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → EuclideanSpace ℝ (Fin (n + 2)))).comp_tendstoUniformlyOn hh
      have hz' : TendstoUniformlyOn
          (fun k => (gM k).pullbackCoefficients (Φ k))
          (fun _ : EuclideanSpace ℝ (Fin (n + 2)) => innerSL ℝ)
          atTop (Metric.closedBall 0 (ρ / 6)) := by
        simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using hz
      exact fun u hu => hυ.tendsto_atTop.eventually (hz' u hu)
    have hd : Tendsto
        (fun k => Real.sqrt c * (((G (τ (υ k))).metric 0).edist
          (AV (τ (υ k)) (b x)) (AV (τ (υ k)) (b y))).toReal)
        atTop (𝓝 (Real.sqrt c * dist x y)) :=
      tendsto_const_nhds.mul (hpair.comp (hτ.tendsto_atTop.comp hυ.tendsto_atTop))
    have hsep : Real.sqrt c * dist x y ≤ dist (J (bW x)) (J (bW y)) := by
      apply lower_distance_of_enclosed_euclidean_limit
        (fun k => gM (υ k)) (fun k => Φ (υ k))
        (r := ρ / 6) (fun k => (Φ (υ k)).contMDiffOn.mono (by
          rw [hsource]
          exact Metric.ball_subset_ball (by linarith : ρ / 6 ≤ ρ)))
        hcoeff (hJlim (bW x)) (hJlim (bW y))
        (Eventually.of_forall fun k =>
          ⟨Metric.ball_subset_ball (by linarith : ρ / 8 ≤ ρ / 6) (hcoordInside (υ k) (bW x)),
            Metric.ball_subset_ball (by linarith : ρ / 8 ≤ ρ / 6) (hcoordInside (υ k) (bW y))⟩)
        hd
      refine Eventually.of_forall fun k => ?_
      rw [hcoordRight, hcoordRight]
      have hh := terminal_distance_le_backward_of_nonnegative_operator hC
        (G (τ (υ k))) (hoperatorG (τ (υ k)))
        (AV (τ (υ k)) (b x)) (AV (τ (υ k)) (b y))
      simpa only [gM, rescaledMetric_edist, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using
          mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg c)
    rw [hfEeq x, hfEeq y, dist_smul₀, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hcpos))]
    have hsqrt := (Real.sqrt_pos.mpr hcpos).ne'
    simpa only [← mul_assoc, inv_mul_cancel₀ hsqrt, one_mul] using
      mul_le_mul_of_nonneg_left hsep (inv_nonneg.mpr (Real.sqrt_nonneg c))
  · intro z v w
    exact (hlinkMetric z v w).trans (hfEmetric z v w)

end PoincareConjecture.RicciFlow
