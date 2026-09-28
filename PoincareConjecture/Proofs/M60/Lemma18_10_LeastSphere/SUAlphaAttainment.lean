import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaEnergyMinimizers
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Elliptic.Dirichlet.Coordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Uniformity
open scoped Manifold ContDiff Topology ENNReal

noncomputable section

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem weak_column_eq_classical
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {u V : LoopPlane → E} (hu : ContDiff ℝ ∞ u) (x : LoopPlane) (r : ℝ)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hV : MemLp V q (volume.restrict (Metric.ball x r)))
    (v : LoopPlane)
    (hweak : ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ Metric.ball x r →
      (∫ z in Metric.ball x r, phi z • V z) =
        -(∫ z in Metric.ball x r, fderiv ℝ phi z v • u z)) :
    V =ᵐ[volume.restrict (Metric.ball x r)] fun z => fderiv ℝ u z v := by
  let O := Metric.ball x r
  let mu := volume.restrict O
  let D := fun z => fderiv ℝ u z v
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hD : Continuous D := (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDi : Integrable D mu := MemLp.integrable le_rfl
    (suAlpha_continuous_memLp_ball hD x r 1)
  have hVi : Integrable V mu := MemLp.integrable hq hV
  have hi : IntegrableOn (fun z => V z - D z) O := hVi.sub hDi
  have hz := Metric.isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    hi.locallyIntegrableOn (fun phi hphi hc hs => ?_)
  · filter_upwards [ae_restrict_of_ae hz, ae_restrict_mem measurableSet_ball] with z hz hzO
    exact sub_eq_zero.mp (hz hzO)
  · have hvp := hVi.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      hphi.continuous hc
    have hdp := hDi.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      hphi.continuous hc
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := O) (fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hz (hs hh)), zero_smul])]
    simp_rw [smul_sub]
    have hh := Poincare.Analysis.Sobolev.WeakCompactness.setIntegral_test_fderiv
      (u := u) Metric.isOpen_ball (hu.contDiffOn.of_le (by simp)) hphi hc hs v
    change (∫ z, phi z • D z ∂mu) = -(∫ z in Metric.ball x r,
      fderiv ℝ phi z v • u z) at hh
    rw [integral_sub hvp hdp, hweak phi hphi hc hs, hh]
    exact sub_self _

private theorem density_eq_observed (g : RiemannianMetric n M) (alpha : ℝ)
    (p : UnitTwoSphere) (b : M) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) (e : M → EuclideanSpace ℝ (Fin n))
    (z : LoopPlane)
    (hz : f ((chartAt LoopPlane p).symm z) ∈ (chartAt (EuclideanSpace ℝ (Fin n)) b).source)
    (he : e ∘ f ∘ (chartAt LoopPlane p).symm =ᶠ[𝓝 z]
      (chartAt (EuclideanSpace ℝ (Fin n)) b) ∘ f ∘ (chartAt LoopPlane p).symm) :
    suSphereChartAlphaDensity g alpha p f z =
      suAlphaLocalDensity g b alpha z
        (e (f ((chartAt LoopPlane p).symm z)),
          suAlphaDerivativePair (e ∘ f ∘ (chartAt LoopPlane p).symm) z) := by
  have hh := suSphereChartAlphaDensity_eq_regularized g alpha p b f hf z (by simpa using hz)
  change _ = suAlphaLocalDensity g b alpha z
    ((chartAt (EuclideanSpace ℝ (Fin n)) b) (f ((chartAt LoopPlane p).symm z)),
      suAlphaDerivativePair ((chartAt (EuclideanSpace ℝ (Fin n)) b) ∘ f ∘
        (chartAt LoopPlane p).symm) z) at hh
  rw [hh]
  congr 2
  · exact he.self_of_nhds.symm
  · unfold suAlphaDerivativePair
    rw [he.fderiv_eq]

set_option maxHeartbeats 1600000 in

theorem suAlpha_minimizing_local_density_L1 [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) {alpha C : ℝ} (ha : 1 ≤ alpha)
    (f : ℕ → UnitTwoSphere → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hn : ∀ j, ¬ IsNullHomotopicSphere (f j))
    (hbound : ∀ j, m60SphereAlphaEnergy g alpha (f j) ≤ C)
    (henergy : Tendsto (fun j => m60SphereAlphaEnergy g alpha (f j)) atTop
      (𝓝 (sInf (m60NonNullAlphaEnergyValues g alpha))))
    (f0 : C(UnitTwoSphere, M)) (hf0 : ContMDiff (𝓡 2) (𝓡 n) ∞ f0)
    (hlim : Tendsto (fun j => (⟨f j, (hf j).continuous⟩ : C(UnitTwoSphere, M)))
      atTop (𝓝 f0)) (p : UnitTwoSphere) :
    ∃ r : ℝ, 0 < r ∧ Tendsto (fun j => eLpNorm (fun z =>
      suSphereChartAlphaDensity g alpha p (f j) z - suSphereChartAlphaDensity g alpha p f0 z)
      1 (volume.restrict (Metric.ball ((chartAt LoopPlane p) p) r))) atTop (𝓝 0) := by
  let : UniformSpace M := uniformSpaceOfCompactR1
  obtain ⟨e, r, r0, k, he, hr, _, _, hKt, hlocal, htail, V, hVp, htest, hstrong⟩ :=
    suAlpha_minimizing_strong_derivatives g ha f hf hn hbound henergy f0 hlim p
  let cs := chartAt LoopPlane p
  let c := chartAt (EuclideanSpace ℝ (Fin n)) (f0 p)
  let O := Metric.ball (cs p) r
  let mu := volume.restrict O
  let q := ENNReal.ofReal (2 * alpha)
  let u := fun j => e ∘ f j ∘ cs.symm
  let u0 := e ∘ f0 ∘ cs.symm
  let W := fun j z => (u j z, suAlphaDerivativePair (u j) z)
  let W0 := fun z => (u0 z, suAlphaDerivativePair u0 z)
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hq : 1 ≤ q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hu (j) : ContDiff ℝ ∞ (u j) :=
    contMDiff_iff_contDiff.mp (he.comp ((hf j).comp (suSphereChart_smooth p)))
  have hu0 : ContDiff ℝ ∞ u0 :=
    contMDiff_iff_contDiff.mp (he.comp (hf0.comp (suSphereChart_smooth p)))
  have hD (j) : Continuous (suAlphaDerivativePair (u j)) :=
    (((hu j).continuous_fderiv (by simp)).clm_apply continuous_const).prodMk
      (((hu j).continuous_fderiv (by simp)).clm_apply continuous_const)
  have hD0 : Continuous (suAlphaDerivativePair u0) :=
    ((hu0.continuous_fderiv (by simp)).clm_apply continuous_const).prodMk
      ((hu0.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hVeq (i : Fin 2) : (fun z => V i z) =ᵐ[mu]
      fun z => fderiv ℝ u0 z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
    apply weak_column_eq_classical hu0 (cs p) r hq (hVp i)
    intro phi hphi hc hs
    rw [htest i phi hphi hc hs]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    change _ • c (f0 (cs.symm z)) = _ • e (f0 (cs.symm z))
    rw [(hlocal z (Metric.ball_subset_closedBall hz)).2.1]
  have hcol (i : Fin 2) : Tendsto (fun j => eLpNorm (fun z =>
      fderiv ℝ (u j) z (EuclideanSpace.basisFun (Fin 2) ℝ i) -
        fderiv ℝ u0 z (EuclideanSpace.basisFun (Fin 2) ℝ i)) q mu) atTop (𝓝 0) := by
    apply (hstrong i).congr'
    filter_upwards [] with j
    apply eLpNorm_congr_ae
    filter_upwards [hVeq i] with z hz
    rw [hz]
  have hder := suAlpha_strong_pair hq
    (fun j => (hD j).fst.aestronglyMeasurable) (fun j => (hD j).snd.aestronglyMeasurable)
      hD0.fst.aestronglyMeasurable hD0.snd.aestronglyMeasurable (hcol 0) (hcol 1)
  have hfU : TendstoUniformly f f0 atTop := tendstoUniformlyOn_univ.mp
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hlim univ isCompact_univ)
  have huU : TendstoUniformly u u0 atTop :=
    ((CompactSpace.uniformContinuous_of_continuous he.continuous).comp_tendstoUniformly hfU).comp
      cs.symm
  have hfun := suAlpha_strong_of_uniform (mu := mu) (q := q)
    (fun j => (hu j).continuous.aestronglyMeasurable) hu0.continuous.aestronglyMeasurable huU
  have hWstrong := suAlpha_strong_pair hq
    (fun j => (hu j).continuous.aestronglyMeasurable) (fun j => (hD j).aestronglyMeasurable)
      hu0.continuous.aestronglyMeasurable hD0.aestronglyMeasurable hfun hder
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  have hK : Metric.closedBall (c (f0 p)) r0 ⊆ (extChartAt (𝓡 n) (f0 p)).target := by
    simpa using hKt
  have hstate := suAlpha_chart_integral_limit g ha p (f0 p) (isCompact_closedBall _ _) hK
    (fun j => W (j + N)) W0
    (fun j => suAlpha_continuous_memLp_ball ((hu (j + N)).continuous.prodMk (hD _)) _ _ q)
    (suAlpha_continuous_memLp_ball (hu0.continuous.prodMk hD0) _ _ q)
    (hWstrong.comp (tendsto_add_atTop_nat N))
    (fun j => ?_) ?_
  · refine ⟨r, hr, (tendsto_add_atTop_iff_nat N).mp ?_⟩
    apply hstate.2.2.2.congr'
    filter_upwards [] with j
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hj := hN (j + N) (Nat.le_add_left _ _) z (Metric.ball_subset_closedBall hz)
    have h0 := hlocal z (Metric.ball_subset_closedBall hz)
    have heqj : e ∘ f (j + N) ∘ cs.symm =ᶠ[𝓝 z] c ∘ f (j + N) ∘ cs.symm :=
      hj.2.1.comp_tendsto (((hf _).continuous.comp (suSphereChart_smooth p).continuous).tendsto z)
    have heq0 : u0 =ᶠ[𝓝 z] c ∘ f0 ∘ cs.symm := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
      exact (hlocal y (Metric.ball_subset_closedBall hy)).2.1
    have hej := density_eq_observed g alpha p (f0 p) (f (j + N)) (hf _) e z hj.1 heqj
    have he0 := density_eq_observed g alpha p (f0 p) f0 hf0 e z h0.1 heq0
    change suAlphaLocalDensity g (f0 p) alpha z (W (j + N) z) -
      suAlphaLocalDensity g (f0 p) alpha z (W0 z) = _
    rw [hej, he0]
    rfl
  · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact Metric.ball_subset_closedBall
      (hN (j + N) (Nat.le_add_left _ _) z (Metric.ball_subset_closedBall hz)).2.2
  · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact Metric.ball_subset_closedBall (hlocal z (Metric.ball_subset_closedBall hz)).2.2

private theorem sphereChart_L1_restrict (p : UnitTwoSphere) (r : ℝ)
    (H : UnitTwoSphere → ℝ) (hH : Continuous H) :
    let cs := chartAt LoopPlane p
    let O := Metric.ball (cs p) r
    let U := cs.source ∩ cs ⁻¹' O
    eLpNorm H 1 (m60RoundSphereMetric.volumeMeasure.restrict U) =
      eLpNorm (fun z => H (cs.symm z) * suAlphaRoundFactor z) 1 (volume.restrict O) := by
  dsimp only
  let cs := chartAt LoopPlane p
  let O := Metric.ball (cs p) r
  let U := cs.source ∩ cs ⁻¹' O
  let : IsFiniteMeasure (volume.restrict O) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hU : IsOpen U := cs.isOpen_inter_preimage Metric.isOpen_ball
  have hUs : U ⊆ cs.source := inter_subset_left
  have hh := m60RoundSphereMetric.integral_target_eq_integral_pullback_density_of_measurable
    cs.symm contMDiffOn_chart_symm contMDiffOn_chart (hH.norm.measurable.indicator hU.measurableSet)
  change (∫ y in cs.source, U.indicator (fun y => ‖H y‖) y
      ∂m60RoundSphereMetric.volumeMeasure) =
    ∫ z in cs.target, U.indicator (fun y => ‖H y‖) (cs.symm z) *
      m60RoundSphereMetric.pullbackVolumeDensity cs.symm z at hh
  rw [setIntegral_indicator hU.measurableSet, inter_eq_right.mpr hUs,
    suSphereChart_target, setIntegral_univ] at hh
  simp only [cs, suSphereChart_volumeDensity] at hh
  have heq : (fun z => U.indicator (fun y => ‖H y‖) (cs.symm z) * suAlphaRoundFactor z) =
      O.indicator (fun z => ‖H (cs.symm z) * suAlphaRoundFactor z‖) := by
    funext z
    have ht : z ∈ cs.target := by rw [suSphereChart_target]; exact mem_univ z
    have hsrc := cs.map_target ht
    by_cases hz : z ∈ O
    · have hzU : cs.symm z ∈ U := ⟨hsrc, by simpa only [mem_preimage, cs.right_inv ht] using hz⟩
      rw [indicator_of_mem hzU, indicator_of_mem hz, norm_mul,
        Real.norm_of_nonneg (show 0 ≤ suAlphaRoundFactor z by
          unfold suAlphaRoundFactor; positivity)]
    · have hzU : cs.symm z ∉ U := fun hy => hz (by
        have hh := hy.2
        simpa only [mem_preimage, cs.right_inv ht] using hh)
      rw [indicator_of_notMem hzU, indicator_of_notMem hz, zero_mul]
  change (∫ y in U, ‖H y‖ ∂m60RoundSphereMetric.volumeMeasure) =
    ∫ z, U.indicator (fun y => ‖H y‖) (cs.symm z) * suAlphaRoundFactor z at hh
  rw [heq, integral_indicator measurableSet_ball] at hh
  have hHi : Integrable H m60RoundSphereMetric.volumeMeasure :=
    hH.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlam : Continuous suAlphaRoundFactor := continuous_const.div₀
    (((continuous_norm.pow 2).add continuous_const).pow 2) (fun _ => by positivity)
  have hHchart := ((hH.comp (suSphereChart_smooth p).continuous).mul hlam)
  have hci : Integrable (fun z => H (cs.symm z) * suAlphaRoundFactor z)
      (volume.restrict O) := MemLp.integrable le_rfl
        (suAlpha_continuous_memLp_ball hHchart (cs p) r 1)
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hHi.integrableOn,
    ← ofReal_integral_norm_eq_lintegral_enorm hci, hh]

private theorem sphereChart_alpha_density_intrinsic (g : RiemannianMetric n M)
    (alpha : ℝ) (p : UnitTwoSphere) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) (z : LoopPlane) :
    suSphereChartAlphaDensity g alpha p f z =
      (1 + 2 * m60SphereIntrinsicEnergy g f ((chartAt LoopPlane p).symm z)) ^ alpha *
        suAlphaRoundFactor z := by
  rw [suSphereChartAlphaDensity, suSphereChart_energy g f (hf.of_le (by simp))]
  change (1 + 2 * (m60SphereIntrinsicEnergy g f ((chartAt LoopPlane p).symm z) *
    suAlphaRoundFactor z) / suAlphaRoundFactor z) ^ alpha * suAlphaRoundFactor z = _
  rw [← mul_assoc, mul_div_cancel_right₀ _
    (show suAlphaRoundFactor z ≠ 0 by unfold suAlphaRoundFactor; positivity)]

set_option maxHeartbeats 1200000 in

theorem suAlpha_minimizing_energy_attained [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) {alpha C : ℝ} (ha : 1 ≤ alpha)
    (f : ℕ → UnitTwoSphere → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hn : ∀ j, ¬ IsNullHomotopicSphere (f j))
    (hbound : ∀ j, m60SphereAlphaEnergy g alpha (f j) ≤ C)
    (henergy : Tendsto (fun j => m60SphereAlphaEnergy g alpha (f j)) atTop
      (𝓝 (sInf (m60NonNullAlphaEnergyValues g alpha))))
    (f0 : C(UnitTwoSphere, M)) (hf0 : ContMDiff (𝓡 2) (𝓡 n) ∞ f0)
    (hlim : Tendsto (fun j => (⟨f j, (hf j).continuous⟩ : C(UnitTwoSphere, M)))
      atTop (𝓝 f0)) :
    m60SphereAlphaEnergy g alpha f0 = sInf (m60NonNullAlphaEnergyValues g alpha) := by
  classical
  let mu := m60RoundSphereMetric.volumeMeasure
  let A := fun (f : UnitTwoSphere → M) (p : UnitTwoSphere) =>
    (1 + 2 * m60SphereIntrinsicEnergy g f p) ^ alpha
  have hA (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) : Continuous (A f) :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ alpha)).comp
      (continuous_const.add
        (continuous_const.mul (m60SphereIntrinsicEnergy_contMDiff g f hf).continuous))
  choose r hr hlocal using fun p =>
    suAlpha_minimizing_local_density_L1 g ha f hf hn hbound henergy f0 hf0 hlim p
  let U := fun p : UnitTwoSphere => (chartAt LoopPlane p).source ∩
    (chartAt LoopPlane p) ⁻¹' Metric.ball ((chartAt LoopPlane p) p) (r p)
  have hU (p) : IsOpen (U p) := (chartAt LoopPlane p).isOpen_inter_preimage Metric.isOpen_ball
  have hcover : (univ : Set UnitTwoSphere) ⊆ ⋃ p, U p := by
    intro p _
    apply mem_iUnion.mpr
    refine ⟨p, ?_⟩
    change p ∈ (chartAt LoopPlane p).source ∧
      (chartAt LoopPlane p) p ∈ Metric.ball ((chartAt LoopPlane p) p) (r p)
    exact ⟨mem_chart_source LoopPlane p, Metric.mem_ball_self (hr p)⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have hTcover : (⋃ p : T, U p) = univ := by
    apply eq_univ_iff_forall.mpr
    intro p
    obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp (hT (mem_univ p))
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, hpq⟩
  have hloc (p : T) : Tendsto (fun j => eLpNorm (A (f j) - A f0) 1
      (mu.restrict (U p))) atTop (𝓝 0) := by
    apply (hlocal p).congr'
    filter_upwards [] with j
    rw [sphereChart_L1_restrict p (r p) (A (f j) - A f0) ((hA _ (hf j)).sub (hA _ hf0))]
    apply eLpNorm_congr_ae
    filter_upwards [] with z
    rw [sphereChart_alpha_density_intrinsic g alpha p (f j) (hf j),
      sphereChart_alpha_density_intrinsic g alpha p f0 hf0]
    simp only [A, Pi.sub_apply, sub_mul]
  have hboundL1 (j) : eLpNorm (A (f j) - A f0) 1 mu ≤
      ∑ p : T, eLpNorm (A (f j) - A f0) 1 (mu.restrict (U p)) := by
    have hh := lintegral_iUnion_le (μ := mu) (fun p : T => U p)
      (fun x => ‖(A (f j) - A f0) x‖ₑ)
    simpa only [hTcover, setLIntegral_univ, tsum_fintype,
      eLpNorm_one_eq_lintegral_enorm] using hh
  have hsum : Tendsto (fun j => ∑ p : T, eLpNorm (A (f j) - A f0) 1
      (mu.restrict (U p))) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun p _ => hloc p)
  have hL1 : Tendsto (fun j => eLpNorm (A (f j) - A f0) 1 mu) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le) hboundL1
  have henergy0 := tendsto_integral_of_L1' (A f0)
    (hA _ hf0).aestronglyMeasurable
    (Eventually.of_forall fun j => m60SphereAlphaEnergy_integrable g alpha (f j) (hf j)) hL1
  exact tendsto_nhds_unique henergy0 henergy

end PoincareConjecture.M60

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60_exists_weakAlphaSphere
    [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    (g : RiemannianMetric n M) (x : M) (hpi : Nontrivial (HomotopyGroup.Pi 2 M x))
    {eps0 alpha : ℝ} (ha : alpha ∈ Ioo 1 (1 + eps0)) (h2 : alpha ≤ 2) :
    ∃ u : M60.SUWeakAlphaSphere g eps0 alpha, ¬ IsNullHomotopicSphere u.map ∧
      ∀ _hs : ContMDiff (𝓡 2) (𝓡 n) ∞ u.map,
        m60SphereAlphaEnergy g alpha u.map = sInf (m60NonNullAlphaEnergyValues g alpha) := by
  obtain ⟨u, hn, C, f, hf, hfn, hb, hE, hlim⟩ :=
    m60_exists_nonNull_weakAlphaSphere g x hpi ha h2
  exact ⟨u, hn, fun hs => M60.suAlpha_minimizing_energy_attained g ha.1.le
    f hf hfn hb hE u.map hs hlim⟩

end PoincareConjecture
