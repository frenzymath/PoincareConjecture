import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.CoordinateSystem
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.FiniteDimensional
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import PoincareConjecture.Proofs.M04.LocalMetricComparison
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u

namespace PoincareConjecture

private theorem m65Slice_deriv_eq {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : ℝ × ℝ → V} {t x : ℝ}
    (hf : DifferentiableAt ℝ f (t, x)) :
    deriv (fun y => f (t, y)) x = fderiv ℝ f (t, x) (0, 1) := by
  exact (hf.hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))).hasDerivAt.deriv

private theorem m65Time_deriv_eq {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : ℝ × ℝ → V} {t x : ℝ}
    (hf : DifferentiableAt ℝ f (t, x)) :
    deriv (fun r => f (r, x)) t = fderiv ℝ f (t, x) (1, 0) := by
  exact (hf.hasFDerivAt.comp t
    ((hasFDerivAt_id t).prodMk (hasFDerivAt_const x t))).hasDerivAt.deriv

private theorem m65Slice_second_eq {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : ℝ × ℝ → V} {t x : ℝ}
    (hf : ContDiffAt ℝ ∞ f (t, x)) :
    deriv (deriv (fun y => f (t, y))) x =
      iteratedFDeriv ℝ 2 f (t, x) (fun _ => (0, 1)) := by
  have hfirst : deriv (fun y : ℝ => (t, y)) = fun _ => (0, 1) := by
    funext y
    exact ((hasDerivAt_const y t).prodMk (hasDerivAt_id y)).deriv
  have hs : ContDiffAt ℝ 2 (fun y : ℝ => (t, y)) x := by fun_prop
  have h := iteratedDeriv_vcomp_two
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hs
  simpa only [Function.comp_def, iteratedDeriv_succ, iteratedDeriv_zero,
    hfirst, deriv_const, map_zero, add_zero] using h

noncomputable def m65LimitChartJet {n : ℕ}
    (Y : ℝ × ℝ → M65ProjectedChartStateSpace n) (z : ℝ × ℝ) :
    M65ProjectedChartJetSpace n :=
  (Y z, fderiv ℝ Y z (0, 1), iteratedFDeriv ℝ 2 Y z (fun _ => (0, 1)))

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}

omit [T2Space M] in

theorem m65LimitChartJet_eq_actual {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) (p : M) {t x : ℝ} (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    m65LimitChartJet (m65ProjectedChartState P c p) (t, x) =
      m65ProjectedChartJet P c p (t, x) := by
  have hs := m65ProjectedChartState_contDiffAt P c hc p ht hx
  simp only [m65LimitChartJet, m65ProjectedChartJet,
    m65Slice_deriv_eq (hs.differentiableAt (by simp)), m65Slice_second_eq hs]

private theorem m65JointJet_tendsto {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : ℕ → ℝ × ℝ → V} {Y : ℝ × ℝ → V}
    {Ω : Set (ℝ × ℝ)}
    (hjet : ∀ m K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k)) (iteratedFDeriv ℝ m Y) atTop K)
    {z : ℝ × ℝ} (hz : z ∈ Ω) (m : ℕ) (v : Fin m → ℝ × ℝ) :
    Tendsto (fun k => iteratedFDeriv ℝ m (f k) z v) atTop
      (𝓝 (iteratedFDeriv ℝ m Y z v)) := by
  have h := (hjet m {z} isCompact_singleton (singleton_subset_iff.mpr hz)).tendsto_at
    (mem_singleton z)
  exact ((continuous_eval_const v).tendsto _).comp h

private theorem m65Value_tendsto {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : ℕ → ℝ × ℝ → V} {Y : ℝ × ℝ → V}
    {Ω : Set (ℝ × ℝ)}
    (hjet : ∀ m K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k)) (iteratedFDeriv ℝ m Y) atTop K)
    {z : ℝ × ℝ} (hz : z ∈ Ω) :
    Tendsto (fun k => f k z) atTop (𝓝 (Y z)) := by
  simpa only [iteratedFDeriv_zero_apply] using
    m65JointJet_tendsto hjet hz 0 (fun _ => (0, 0))

theorem m65ProjectedChart_limit_equation
    {circumference : ℕ → ℝ} (P : ∀ k, M62.CircleProductData F (circumference k))
    (c : ∀ k, ℝ → ℝ → (P k).charts.Point)
    (hc : ∀ k, M62ShrinkingCurve (P k).flow (c k)) (p : M)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hΩtime : ∀ z ∈ Ω, z.1 ∈ Ioo a b)
    (hchart : ∀ k z, z ∈ Ω →
      (c k z.2 z.1).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    {Y : ℝ × ℝ → M65ProjectedChartStateSpace n} (hY : ContDiffOn ℝ ∞ Y Ω)
    (hjet : ∀ m K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (m65ProjectedChartState (P k) (c k) p))
      (iteratedFDeriv ℝ m Y) atTop K)
    (hrange : ∀ z ∈ Ω, m65LimitChartJet Y z ∈
      m65ProjectedChartOperatorDomain (a := a) (b := b) p) :
    ∀ z ∈ Ω, HasDerivAt (fun t => Y (t, z.2))
      (m65ProjectedChartOperator F p (m65LimitChartJet Y z)) z.1 := by
  intro z hz
  have hzero := m65Value_tendsto hjet hz
  have hspace := m65JointJet_tendsto hjet hz 1 (fun _ => (0, 1))
  have hsecond := m65JointJet_tendsto hjet hz 2 (fun _ => (0, 1))
  have htime := m65JointJet_tendsto hjet hz 1 (fun _ => (1, 0))
  simp only [iteratedFDeriv_one_apply] at hspace htime
  have hfinite : Tendsto (fun k =>
      m65LimitChartJet (m65ProjectedChartState (P k) (c k) p) z) atTop
      (𝓝 (m65LimitChartJet Y z)) := hzero.prodMk_nhds (hspace.prodMk_nhds hsecond)
  have hop := ((m65ProjectedChartOperator_contDiffOn F p).continuousOn.continuousAt
    ((m65ProjectedChartOperatorDomain_isOpen p).mem_nhds (hrange z hz))).tendsto.comp hfinite
  have heq (k : ℕ) :
      fderiv ℝ (m65ProjectedChartState (P k) (c k) p) z (1, 0) =
        m65ProjectedChartOperator F p
          (m65LimitChartJet (m65ProjectedChartState (P k) (c k) p) z) := by
    rw [m65LimitChartJet_eq_actual (P k) (c k) (hc k) p (hΩtime z hz) (hchart k z hz)]
    rw [← m65Time_deriv_eq ((m65ProjectedChartState_contDiffAt (P k) (c k) (hc k) p
      (hΩtime z hz) (hchart k z hz)).differentiableAt (by simp))]
    exact (m65ProjectedChartState_equation (P k) (c k) (hc k) p
      (hΩtime z hz) (hchart k z hz)).deriv
  have hlim : fderiv ℝ Y z (1, 0) =
      m65ProjectedChartOperator F p (m65LimitChartJet Y z) :=
    tendsto_nhds_unique htime (hop.congr (fun k => (heq k).symm))
  have hs := (hY.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp)
  have h := (hs.hasFDerivAt.comp z.1
    ((hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1))).hasDerivAt
  exact h.congr_deriv hlim

theorem m65ProjectedChart_exists_smooth_limit
    {circumference : ℕ → ℝ} (P : ∀ k, M62.CircleProductData F (circumference k))
    (c : ∀ k, ℝ → ℝ → (P k).charts.Point)
    (hc : ∀ k, M62ShrinkingCurve (P k).flow (c k)) (p : M)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hΩtime : ∀ z ∈ Ω, z.1 ∈ Ioo a b)
    (hchart : ∀ k z, z ∈ Ω →
      (c k z.2 z.1).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    {Kq : Set (EuclideanSpace ℝ (Fin n))} (hKq : IsCompact Kq)
    (hKtarget : Kq ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) p).target)
    (hq : ∀ k z, z ∈ Ω →
      (chartAt (EuclideanSpace ℝ (Fin n)) p) (c k z.2 z.1).1 ∈ Kq)
    {vmin : ℝ} (hvmin : 0 < vmin)
    (hv : ∀ k z, z ∈ Ω → vmin ≤ curveSpeed (P k).flow (c k) z.1 z.2)
    (hu : ∀ z ∈ Ω, Tendsto (fun k => m62Slope (P k) (c k) z.1 z.2) atTop (𝓝 0))
    (hbound : ∀ K, IsCompact K → K ⊆ Ω → ∀ m : ℕ, ∃ B : ℝ,
      ∀ᶠ k in atTop, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m (m65ProjectedChartState (P k) (c k) p) z‖ ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ Y : ℝ × ℝ → M65ProjectedChartStateSpace n,
      ContDiffOn ℝ ∞ Y Ω ∧
      (∀ m K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (m65ProjectedChartState (P (σ k)) (c (σ k)) p))
        (iteratedFDeriv ℝ m Y) atTop K) ∧
      (∀ z ∈ Ω, (Y z).1 = z.1 ∧ (Y z).2.1 ∈ Kq ∧
        vmin ≤ (Y z).2.2.1 ∧ (Y z).2.2.2 = 0) ∧
      ∀ z ∈ Ω, HasDerivAt (fun t => Y (t, z.2))
        (m65ProjectedChartOperator F p (m65LimitChartJet Y z)) z.1 := by
  have hs (k : ℕ) : ContDiffOn ℝ ∞ (m65ProjectedChartState (P k) (c k) p) Ω :=
    fun z hz => (m65ProjectedChartState_contDiffAt (P k) (c k) (hc k) p
      (hΩtime z hz) (hchart k z hz)).contDiffWithinAt
  obtain ⟨σ, hσ, Y, hY, hjet⟩ :=
    Poincare.Analysis.Calculus.exists_common_smoothSubsequenceExtraction_finiteDimensional
      (E := fun _ => ℝ × ℝ) (F := fun _ => M65ProjectedChartStateSpace n)
      (Ω := fun _ => Ω) (fun _ => hΩ)
      (fun _ k => m65ProjectedChartState (P k) (c k) p)
      (fun _ => hs) (fun _ => hbound)
  have hvalues (z : ℝ × ℝ) (hz : z ∈ Ω) :
      (Y 0 z).1 = z.1 ∧ (Y 0 z).2.1 ∈ Kq ∧
        vmin ≤ (Y 0 z).2.2.1 ∧ (Y 0 z).2.2.2 = 0 := by
    have h0 := m65Value_tendsto (hjet 0) hz
    have htend := h0.fst_nhds
    change Tendsto (fun _ : ℕ => z.1) atTop (𝓝 (Y 0 z).1) at htend
    have hqtend : Tendsto (fun k => (chartAt (EuclideanSpace ℝ (Fin n)) p)
        (c (σ k) z.2 z.1).1) atTop (𝓝 (Y 0 z).2.1) := h0.snd_nhds.fst_nhds
    have hvtend : Tendsto (fun k => curveSpeed (P (σ k)).flow (c (σ k)) z.1 z.2)
        atTop (𝓝 (Y 0 z).2.2.1) := h0.snd_nhds.snd_nhds.fst_nhds
    have hutend : Tendsto (fun k => m62Slope (P (σ k)) (c (σ k)) z.1 z.2)
        atTop (𝓝 (Y 0 z).2.2.2) := h0.snd_nhds.snd_nhds.snd_nhds
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact tendsto_nhds_unique htend tendsto_const_nhds
    · exact hKq.isClosed.mem_of_tendsto hqtend
        (Eventually.of_forall (fun k => hq (σ k) z hz))
    · exact ge_of_tendsto hvtend (Eventually.of_forall (fun k => hv (σ k) z hz))
    · exact tendsto_nhds_unique hutend ((hu z hz).comp hσ.tendsto_atTop)
  refine ⟨σ, hσ, Y 0, hY 0, hjet 0, hvalues, ?_⟩
  apply m65ProjectedChart_limit_equation (fun k => P (σ k)) (fun k => c (σ k))
    (fun k => hc (σ k)) p hΩ hΩtime (fun k => hchart (σ k)) (hY 0) (hjet 0)
  intro z hz
  have hval := hvalues z hz
  exact ⟨by simpa only [m65LimitChartJet, hval.1] using hΩtime z hz,
    hKtarget hval.2.1, hvmin.trans_le hval.2.2.1⟩

private theorem m65CompactTarget_subsequence {D N : Type*} [PseudoMetricSpace D]
    [SigmaCompactSpace D] [LocallyCompactSpace D] [EMetricSpace N] [CompactSpace N]
    (f : ℕ → C(D, N)) (L : ℝ≥0) (hL : ∀ k, LipschitzWith L (f k : D → N)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ g : C(D, N),
      Tendsto (f ∘ σ) atTop (𝓝 g) := by
  let A : Set C(D, N) := {g | LipschitzWith L (g : D → N)}
  have himage : ContinuousMap.toFun '' A = {g : D → N | LipschitzWith L g} := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact hh
    · intro hg
      exact ⟨⟨g, hg.continuous⟩, hg, rfl⟩
  have himageCompact : IsCompact (ContinuousMap.toFun '' A) := by
    rw [himage]
    exact (isClosed_setOfPred_lipschitzWith L).isCompact
  have heq : Equicontinuous ((↑) : A → D → N) :=
    (LipschitzWith.uniformEquicontinuous ((↑) : A → D → N) L (fun g => g.property)).equicontinuous
  have hA := ArzelaAscoli.isCompact_of_equicontinuous A himageCompact heq
  have : Filter.IsCountablyGenerated (uniformity C(D, N)) := inferInstance
  have : FirstCountableTopology C(D, N) := UniformSpace.firstCountableTopology C(D, N)
  obtain ⟨g, _hg, σ, hσ, hlim⟩ := hA.tendsto_subseq hL
  exact ⟨σ, hσ, g, hlim⟩

omit [T2Space M] in
private theorem m65ReferenceNorm_bound {r s C : ℝ} (hrs : r ≤ s)
    (hsub : Icc r s ⊆ Icc a b) (hC : 0 ≤ C)
    (hRm : ∀ t ∈ Icc r s, ∀ q : M, (F.connection t).curvatureTensorNorm q ≤ C)
    {t : ℝ} (ht : t ∈ Icc r s) (q : M) (V : TangentSpace (𝓡 n) q) :
    (F.metric s).tangentNorm q V ≤
      Real.exp ((n : ℝ) * C * (s - r)) * (F.metric t).tangentNorm q V := by
  have h := (M04.tangentNorm_comparison_at_of_curvature_bound F (hsub ht)
    (hsub (right_mem_Icc.mpr hrs)) ht.2 hC q
    (fun τ hτ => hRm τ ⟨ht.1.trans hτ.1, hτ.2⟩ q) V).2
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left ht.1 s) (by positivity)

omit [T2Space M] in
private theorem m65Path_edist_bound (g : RiemannianMetric n M) {γ : ℝ → M}
    {l r B : ℝ} (hlr : l ≤ r) (hB : 0 ≤ B)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc l r))
    (hv : ∀ t ∈ Icc l r, g.tangentNorm (γ t) (curveVelocity (n := n) γ t) ≤ B) :
    g.edist (γ l) (γ r) ≤ ENNReal.ofReal (B * (r - l)) := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist (𝓡 n) (γ l) (γ r) ≤ _
  apply (Manifold.riemannianEDist_le_pathELength hγ rfl rfl hlr).trans
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  have hnorm (t : ℝ) : ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1‖ₑ =
      ENNReal.ofReal (g.tangentNorm (γ t) (curveVelocity (n := n) γ t)) := by
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  simp_rw [hnorm]
  calc
    _ ≤ ∫⁻ _ in Icc l r, ENNReal.ofReal B :=
      MeasureTheory.setLIntegral_mono' measurableSet_Icc
        (fun t ht => ENNReal.ofReal_le_ofReal (hv t ht))
    _ = ENNReal.ofReal (B * (r - l)) := by
      rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
        Real.volume_Icc, ENNReal.ofReal_mul hB]

private theorem m65ActualProjection_uniform_modulus {κ : Type*} {circumference : κ → ℝ}
    (P : ∀ k, M62.CircleProductData F (circumference k))
    (c : ∀ k, ℝ → ℝ → (P k).charts.Point)
    (hc : ∀ k, M62ShrinkingCurve (P k).flow (c k))
    {r s C B₀ B₁ : ℝ} (hrs : r ≤ s) (hsub : Icc r s ⊆ Ioo a b)
    (hC : 0 ≤ C) (hB₀ : 0 ≤ B₀) (_hB₁ : 0 ≤ B₁)
    (hRm : ∀ t ∈ Icc r s, ∀ q : M, (F.connection t).curvatureTensorNorm q ≤ C)
    (hv : ∀ k t x, t ∈ Icc r s → curveSpeed (P k).flow (c k) t x ≤ B₀)
    (hcurv : ∀ k t x, t ∈ Icc r s → m62Curvature (P k).flow (c k) t x ≤ B₁) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k t u x y, t ∈ Icc r s → u ∈ Icc r s →
      (F.metric s).edist (c k x t).1 (c k y u).1 ≤
        ENNReal.ofReal (B * (|t - u| + |x - y|)) := by
  let g := F.metric s
  let D := Real.exp ((n : ℝ) * C * (s - r))
  let B := D * max B₀ B₁
  have hD : 0 ≤ D := Real.exp_nonneg _
  have hB : 0 ≤ B := mul_nonneg hD (hB₀.trans (le_max_left _ _))
  let := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := .ofRiemannianMetric (𝓡 n) M
  have hnorm {t : ℝ} (ht : t ∈ Icc r s) (q : M) (V : TangentSpace (𝓡 n) q) :=
    m65ReferenceNorm_bound hrs (fun _ h => Ioo_subset_Icc_self (hsub h)) hC hRm ht q V
  have hspace (k : κ) (t : ℝ) (ht : t ∈ Icc r s) (x y : ℝ) (hxy : x ≤ y) :
      edist (c k x t).1 (c k y t).1 ≤ ENNReal.ofReal (B * (y - x)) := by
    let := (P k).charts.chartedSpace
    have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : (P k).charts.Point → M) :=
      contMDiff_fst.comp (P k).charts.to_product_smooth
    have hfst1 : ContMDiff (𝓡 (n + 1)) (𝓡 n) 1 (Prod.fst : (P k).charts.Point → M) :=
      hfst.of_le (by simp)
    have hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 1 (fun z => c k z t) :=
      ((hc k).spatial_regular t (Ioo_subset_Icc_self (hsub ht))).of_le (by norm_num)
    apply m65Path_edist_bound g hxy hB (hfst1.comp hc1).contMDiffOn
    intro z _hz
    have hproj : curveSpeed F (fun x t => (c k x t).1) t z ≤
        curveSpeed (P k).flow (c k) t z := by
      have heq := m65Projection_speed_sq (P k) (c k) (hc k)
        (Ioo_subset_Icc_self (hsub ht)) z
      have hp := M62.speed_nonneg F (fun x t => (c k x t).1) t z
      have hvp := M62.speed_nonneg (P k).flow (c k) t z
      nlinarith [mul_nonneg (sq_nonneg (curveSpeed (P k).flow (c k) t z))
        (sq_nonneg (m62Slope (P k) (c k) t z))]
    exact (hnorm ht _ _).trans (mul_le_mul_of_nonneg_left
      ((hproj.trans (hv k t z ht)).trans (le_max_left _ _)) hD)
  have htime (k : κ) (t u : ℝ) (ht : t ∈ Icc r s) (hu : u ∈ Icc r s)
      (x : ℝ) (htu : t ≤ u) :
      edist (c k x t).1 (c k x u).1 ≤ ENNReal.ofReal (B * (u - t)) := by
    let := (P k).charts.chartedSpace
    have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : (P k).charts.Point → M) :=
      contMDiff_fst.comp (P k).charts.to_product_smooth
    have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun τ => (c k x τ).1) (Icc t u) :=
      hfst.comp_contMDiffOn ((hc k).joint_smooth.comp
        (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn
        (fun τ hτ => ⟨mem_univ _, hsub ⟨ht.1.trans hτ.1, hτ.2.trans hu.2⟩⟩))
    apply m65Path_edist_bound g htu hB (hcurve.of_le (by simp))
    intro τ hτ
    have hτcell : τ ∈ Icc r s := ⟨ht.1.trans hτ.1, hτ.2.trans hu.2⟩
    exact (hnorm hτcell _ _).trans (mul_le_mul_of_nonneg_left
      (((m65Projection_timeVelocity_le_curvature (P k) (c k) (hc k) (hsub hτcell) x).trans
        (hcurv k τ x hτcell)).trans (le_max_right _ _)) hD)
  have hspace' (k : κ) (t : ℝ) (ht : t ∈ Icc r s) (x y : ℝ) :
      edist (c k x t).1 (c k y t).1 ≤ ENNReal.ofReal (B * |x - y|) := by
    rcases le_total x y with hxy | hyx
    · simpa only [abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr hxy)] using
        hspace k t ht x y hxy
    · rw [edist_comm]
      simpa only [abs_of_nonneg (sub_nonneg.mpr hyx)] using hspace k t ht y x hyx
  have htime' (k : κ) (t u : ℝ) (ht : t ∈ Icc r s) (hu : u ∈ Icc r s) (x : ℝ) :
      edist (c k x t).1 (c k x u).1 ≤ ENNReal.ofReal (B * |t - u|) := by
    rcases le_total t u with htu | hut
    · simpa only [abs_sub_comm t u, abs_of_nonneg (sub_nonneg.mpr htu)] using
        htime k t u ht hu x htu
    · rw [edist_comm]
      simpa only [abs_of_nonneg (sub_nonneg.mpr hut)] using htime k u t hu ht x hut
  refine ⟨B, hB, ?_⟩
  intro k t u x y ht hu
  change edist (c k x t).1 (c k y u).1 ≤ _
  calc
    _ ≤ edist (c k x t).1 (c k x u).1 + edist (c k x u).1 (c k y u).1 :=
      edist_triangle _ _ _
    _ ≤ ENNReal.ofReal (B * |t - u|) + ENNReal.ofReal (B * |x - y|) :=
      add_le_add (htime' k t u ht hu x) (hspace' k u hu x y)
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity), mul_add]

noncomputable def m65ProjectedContinuousMap {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) {r s : ℝ} (hsub : Icc r s ⊆ Ioo a b) :
    C((Ioo r s ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)), M) := by
  let := P.charts.chartedSpace
  have h : ContinuousOn (fun z : ℝ × ℝ => (c z.2 z.1).1) (Ioo r s ×ˢ univ) :=
    continuous_fst.comp_continuousOn (hc.continuous.comp
      (continuous_snd.prodMk continuous_fst).continuousOn
      (fun _ hz => ⟨mem_univ _, Ioo_subset_Icc_self (hsub (Ioo_subset_Icc_self hz.1))⟩))
  exact ⟨fun z => (c z.1.2 z.1.1).1, h.domRestrict⟩

theorem m65Projected_exists_continuous_subsequence
    (hcompact : IsCompact (univ : Set M)) {circumference : ℕ → ℝ}
    (P : ∀ k, M62.CircleProductData F (circumference k))
    (c : ∀ k, ℝ → ℝ → (P k).charts.Point)
    (hc : ∀ k, M62ShrinkingCurve (P k).flow (c k))
    {r s C B₀ B₁ : ℝ} (hrs : r ≤ s) (hsub : Icc r s ⊆ Ioo a b)
    (hC : 0 ≤ C) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hRm : ∀ t ∈ Icc r s, ∀ q : M, (F.connection t).curvatureTensorNorm q ≤ C)
    (hv : ∀ k t x, t ∈ Icc r s → curveSpeed (P k).flow (c k) t x ≤ B₀)
    (hcurv : ∀ k t x, t ∈ Icc r s → m62Curvature (P k).flow (c k) t x ≤ B₁) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ q : C((Ioo r s ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)), M),
        Tendsto (fun k => m65ProjectedContinuousMap (P (σ k)) (c (σ k)) (hc (σ k)) hsub)
          atTop (𝓝 q) := by
  obtain ⟨B, hB, hb⟩ :=
    m65ActualProjection_uniform_modulus P c hc hrs hsub hC hB₀ hB₁ hRm hv hcurv
  let := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric s).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨(F.metric s).inner, (F.metric s).contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := .ofRiemannianMetric (𝓡 n) M
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let Ω : Set (ℝ × ℝ) := Ioo r s ×ˢ univ
  let : LocallyCompactSpace Ω := (isOpen_Ioo.prod isOpen_univ).locallyCompactSpace
  let f (k : ℕ) := m65ProjectedContinuousMap (P k) (c k) (hc k) hsub
  have hLip (k : ℕ) : LipschitzWith ⟨2 * B, by positivity⟩ (f k : Ω → M) := by
    intro z w
    have h := hb k z.1.1 w.1.1 z.1.2 w.1.2
      (Ioo_subset_Icc_self z.2.1) (Ioo_subset_Icc_self w.2.1)
    have hfst : |z.1.1 - w.1.1| ≤ dist z w := by
      rw [Subtype.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact le_max_left _ _
    have hsnd : |z.1.2 - w.1.2| ≤ dist z w := by
      rw [Subtype.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact le_max_right _ _
    refine h.trans ?_
    calc
      _ ≤ ENNReal.ofReal ((2 * B) * dist z w) :=
        ENNReal.ofReal_le_ofReal (by
          nlinarith [mul_le_mul_of_nonneg_left hfst hB,
            mul_le_mul_of_nonneg_left hsnd hB])
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), edist_dist,
          ENNReal.ofReal_eq_coe_nnreal (by positivity)]
        rfl
  exact m65CompactTarget_subsequence f ⟨2 * B, by positivity⟩ hLip

end PoincareConjecture
