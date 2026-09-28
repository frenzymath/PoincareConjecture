import PoincareConjecture.Proofs.M03.Existence.DeTurckMetricDomainNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckCompletedOutputNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckJetAffineNative
import PoincareConjecture.Proofs.M03.Existence.FiniteChartCommonTimeNative

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Manifold ContDiff Bundle Topology BigOperators SchwartzMap ENNReal

namespace PoincareConjecture.DeTurckStateApproximationNative

open TensorProbeNative TensorHilbertNative ChartMeasureNative ParsevalTensorNative
  DeTurckCompatibleJetNative DeTurckJetCoordinatesNative DeTurckJetAffineNative
  DeTurckMetricDomainNative DeTurckNestedLocalizationNative
  DeTurckDomainRegularityNative DeTurckHigherDomainNative
  DeTurckCompletedOutputNative EuclideanDerivativeNative NativeChartScalarLocalization
  ChartPushforwardLpNative DeTurckInverseCompositionNative LpFiniteCoordinatesNative
  EuclideanTranslationNative

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {g0 : RiemannianMetric n M} (d : Data g0)
  (L : FiniteChartLocalizationData d.charts)

local notation "E" => EuclideanSpace ℝ (Fin n)

def patchCore (a : L.patches) : Set E :=
  (L.chart a).target ∩ (L.chart a).symm ⁻¹'
    interior {x | (nativeCutoffs d L a).eta x = 1}

theorem patchCore_isOpen (a : L.patches) : IsOpen (patchCore d L a) :=
  (L.chart a).isOpen_inter_preimage_symm isOpen_interior

theorem nativeCoordinateSupport_subset_core (a : L.patches) :
    nativeCoordinateSupport d L a ⊆ patchCore d L a := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨(L.chart a).map_source (L.weight_support_source a hx), ?_⟩
  change (L.chart a).symm (L.chart a x) ∈
    interior {x | (nativeCutoffs d L a).eta x = 1}
  rw [(L.chart a).left_inv (L.weight_support_source a hx)]
  exact mem_interior_iff_mem_nhds.mpr ((nativeCutoffs d L a).eta_one x hx)

theorem exists_common_patch_radius :
    ∃ r : ℝ, 0 < r ∧ ∀ a : L.patches,
      cthickening r (nativeCoordinateSupport d L a) ⊆ patchCore d L a := by
  classical
  choose r hr hsub using fun a : L.patches =>
    (nativeCoordinateSupport_isCompact d L a).exists_cthickening_subset_open
      (patchCore_isOpen d L a) (nativeCoordinateSupport_subset_core d L a)
  obtain ⟨s, hs, hsr⟩ := exists_common_positive_time Finset.univ r (fun a _ => hr a)
  exact ⟨s, hs, fun a => (cthickening_mono (hsr a (Finset.mem_univ a)) _).trans (hsub a)⟩

def liftSchwartz (a : L.patches) (φ : 𝓢(E, ℝ)) : M → ℝ :=
  fun x => (nativeCutoffs d L a).eta x * φ (L.chart a x)

theorem liftSchwartz_contMDiff (a : L.patches) (φ : 𝓢(E, ℝ)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (liftSchwartz d L a φ) :=
  FiniteChartData.contMDiff_weight_mul_chart a.val.1.val
    (nativeCutoffs d L a).eta_smooth (nativeCutoffs d L a).eta_support
    (φ.smooth (⊤ : ℕ∞)).contDiffOn

theorem liftSchwartz_support_eta (a : L.patches) (φ : 𝓢(E, ℝ)) :
    tsupport (liftSchwartz d L a φ) ⊆ tsupport (nativeCutoffs d L a).eta :=
  tsupport_mul_subset_left

theorem liftSchwartz_eq_on_source (a : L.patches) (φ : 𝓢(E, ℝ))
    (hφ : tsupport φ ⊆ patchCore d L a) {x : M} (hx : x ∈ (L.chart a).source) :
    liftSchwartz d L a φ x = φ (L.chart a x) := by
  by_cases hz : φ (L.chart a x) = 0
  · simp only [liftSchwartz, hz, mul_zero]
  · have hcore := hφ (subset_tsupport φ hz)
    have heta := interior_subset hcore.2
    rw [(L.chart a).left_inv hx] at heta
    change (nativeCutoffs d L a).eta x = (1 : ℝ) at heta
    simp only [liftSchwartz, heta, one_mul]

theorem liftSchwartz_support (a : L.patches) (φ : 𝓢(E, ℝ))
    (hcompact : HasCompactSupport φ) (hφ : tsupport φ ⊆ patchCore d L a) :
    tsupport (liftSchwartz d L a φ) ⊆ (L.chart a).symm '' tsupport φ := by
  apply closure_minimal
  · intro x hx
    have hxeta : (nativeCutoffs d L a).eta x ≠ 0 :=
      (mul_ne_zero_iff.mp hx).1
    have hxU := (nativeCutoffs d L a).eta_support (subset_tsupport _ hxeta)
    exact ⟨L.chart a x, subset_tsupport φ (mul_ne_zero_iff.mp hx).2,
      (L.chart a).left_inv hxU⟩
  · exact (hcompact.image_of_continuousOn
      ((L.chart a).symm.continuousOn.mono (fun x hx => (hφ hx).1))).isClosed

theorem cutoffNativeField_word_lift (a : L.patches) (φ : 𝓢(E, ℝ))
    (hcompact : HasCompactSupport φ) (hφ : tsupport φ ⊆ patchCore d L a)
    (w : List (Fin d.fieldCount)) (x : M) :
    directionalWord (cutoffNativeField d L a) w (liftSchwartz d L a φ) x =
      directionalWord d.fields w (liftSchwartz d L a φ) x := by
  by_cases hx : x ∈ tsupport (liftSchwartz d L a φ)
  · obtain ⟨y, hy, rfl⟩ := liftSchwartz_support d L a φ hcompact hφ hx
    have hone : (nativeCutoffs d L a).eta =ᶠ[𝓝 ((L.chart a).symm y)] 1 :=
      mem_interior_iff_mem_nhds.mp (hφ hy).2
    apply (directionalWord_fields_eventuallyEq
      (cutoffNativeField d L a) d.fields w (liftSchwartz d L a φ) ?_).eq_of_nhds
    intro i
    filter_upwards [hone] with z hz
    change (nativeCutoffs d L a).eta z • d.fields i z = d.fields i z
    rw [hz, Pi.one_apply, one_smul]
  · rw [directionalWord_zero_off_closed (cutoffNativeField d L a) w
      (isClosed_tsupport _) (fun y hy => image_eq_zero_of_notMem_tsupport hy) hx,
      directionalWord_zero_off_closed d.fields w
        (isClosed_tsupport _) (fun y hy => image_eq_zero_of_notMem_tsupport hy) hx]

def patchExtensionConstant (a : L.patches) : ℝ≥0∞ :=
  (d.charts.exists_measure_restrict_le_chart a.val.1.val
    (isClosed_tsupport (nativeCutoffs d L a).eta).isCompact
    (nativeCutoffs d L a).eta_support).choose

theorem patchExtensionConstant_ne_top (a : L.patches) : patchExtensionConstant d L a ≠ ⊤ :=
  (d.charts.exists_measure_restrict_le_chart a.val.1.val
    (isClosed_tsupport (nativeCutoffs d L a).eta).isCompact
    (nativeCutoffs d L a).eta_support).choose_spec.1

theorem patchExtensionMeasureBound (a : L.patches) :
    d.charts.measure.restrict (tsupport (nativeCutoffs d L a).eta) ≤
      patchExtensionConstant d L a •
        coordinatePushforward (L.chart a) (tsupport (nativeCutoffs d L a).eta) :=
  (d.charts.exists_measure_restrict_le_chart a.val.1.val
    (isClosed_tsupport (nativeCutoffs d L a).eta).isCompact
    (nativeCutoffs d L a).eta_support).choose_spec.2

def patchExtensionL2 (a : L.patches) : ScalarL2 n →L[ℝ] Lp ℝ 2 d.charts.measure :=
  chartExtensionL2 (L.chart a) (isClosed_tsupport (nativeCutoffs d L a).eta).measurableSet
    (nativeCutoffs d L a).eta_support (patchExtensionConstant_ne_top d L a)
    (patchExtensionMeasureBound d L a)

theorem patchExtensionL2_derivative (a : L.patches) (φ : 𝓢(E, ℝ))
    (hφ : tsupport φ ⊆ patchCore d L a) (w : List (Fin n)) :
    patchExtensionL2 d L a ((orderedSchwartzDerivative w φ).toLp 2 volume) =ᵐ[d.charts.measure]
      directionalWord (nativeCutoffs d L a).field w (liftSchwartz d L a φ) := by
  apply (chartExtensionL2_toLp_coe (L.chart a)
    (isClosed_tsupport (nativeCutoffs d L a).eta).measurableSet
    (nativeCutoffs d L a).eta_support (patchExtensionConstant_ne_top d L a)
    (patchExtensionMeasureBound d L a) ((orderedSchwartzDerivative w φ).memLp 2 volume)).trans
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ tsupport (nativeCutoffs d L a).eta
  · rw [indicator_of_mem hx]
    symm
    apply (directionalWord_chartPullback_eventuallyEq a.val.1.val
      (nativeCutoffs d L a).field ((nativeCutoffs d L a).eta_support hx)
      (fun i => (nativeCutoffs d L a).field_eventuallyEq
        ((nativeCutoffs d L a).zeta_one x hx) i) w φ ?_).eq_of_nhds
    filter_upwards [(L.chart a).open_source.mem_nhds
      ((nativeCutoffs d L a).eta_support hx)] with y hy
    exact liftSchwartz_eq_on_source d L a φ hφ hy
  · rw [indicator_of_notMem hx]
    exact (directionalWord_zero_off_closed (nativeCutoffs d L a).field w
      (isClosed_tsupport (nativeCutoffs d L a).eta)
      (fun y hy => by
        simp only [liftSchwartz, image_eq_zero_of_notMem_tsupport hy, zero_mul]) hx).symm

def patchCoordinateJet (a : L.patches) (k : ℕ) :
    (WordIndex (Fin n) k → ScalarL2 n) →L[ℝ]
      (WordIndex (Fin n) k → Lp ℝ 2 d.charts.measure) :=
  ContinuousLinearMap.pi (fun w => (patchExtensionL2 d L a).comp
    (ContinuousLinearMap.proj w))

def patchNativeJet (a : L.patches) (k : ℕ) :
    (WordIndex (Fin n) k → ScalarL2 n) →L[ℝ]
      (WordIndex (Fin d.fieldCount) k → Lp ℝ 2 d.charts.measure) :=
  ContinuousLinearMap.pi (fun w =>
    (termsL2 d.charts.measure (nativeWordTerms d L a (List.ofFn w.2))
      (fun t ht => (nativeWordTerms_order d L a (List.ofFn w.2) t ht).trans
        (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt))).comp
      (patchCoordinateJet d L a k))

theorem patchNativeJet_schwartz (a : L.patches) (k : ℕ) (φ : 𝓢(E, ℝ))
    (hcompact : HasCompactSupport φ) (hφ : tsupport φ ⊆ patchCore d L a)
    (w : List (Fin d.fieldCount)) (hw : w.length ≤ k) :
    patchNativeJet d L a k (schwartzWordTuple k φ) (wordIndex w hw) =ᵐ[d.charts.measure]
      directionalWord d.fields w (liftSchwartz d L a φ) := by
  change termsL2 d.charts.measure (nativeWordTerms d L a (List.ofFn (wordIndex w hw).2)) _
    (patchCoordinateJet d L a k (schwartzWordTuple k φ)) =ᵐ[_] _
  simp only [wordIndex_word]
  have hjet : ∀ v (hv : v.length ≤ k),
      patchCoordinateJet d L a k (schwartzWordTuple k φ) (wordIndex v hv) =ᵐ[d.charts.measure]
        directionalWord (nativeCutoffs d L a).field v (liftSchwartz d L a φ) := by
    intro v hv
    simpa only [patchCoordinateJet, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      schwartzWordTuple, wordIndex_word] using patchExtensionL2_derivative d L a φ hφ v
  apply (termsL2_ae_eq (nativeCutoffs d L a).field d.charts.measure
    (nativeWordTerms d L a w) _ (patchCoordinateJet d L a k (schwartzWordTuple k φ))
    (liftSchwartz d L a φ) hjet).trans
  apply Eventually.of_forall
  intro x
  rw [nativeWordTerms_eq d L a w (liftSchwartz_contMDiff d L a φ),
    cutoffNativeField_word_lift d L a φ hcompact hφ]

theorem patchExtension_localization_smooth (a : L.patches) (f : M → ℝ)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hfLp : MemLp f 2 d.charts.measure) :
    patchExtensionL2 d L a (L.localizationL2 a (hfLp.toLp f)) =
      (L.globalProduct_memLp a hf).toLp (fun x => L.weight a x * f x) := by
  rw [L.localizationL2_toLp_eq a hf hfLp]
  have hzero : ∀ x ∉ tsupport (nativeCutoffs d L a).eta, L.weight a x * f x = 0 := by
    intro x hx
    have hxw : x ∉ tsupport (L.weight a) :=
      fun h => hx ((nativeCutoffs d L a).mem_eta_support h)
    rw [image_eq_zero_of_notMem_tsupport hxw, zero_mul]
  exact chartExtension_chartScalar a.val.1.val ((L.weight_smooth a).mul hf)
    (isClosed_tsupport (nativeCutoffs d L a).eta).isCompact
    (nativeCutoffs d L a).eta_support hzero (L.globalProduct_memLp a hf)
    (patchExtensionConstant_ne_top d L a) (patchExtensionMeasureBound d L a)

theorem patchExtension_localization (a : L.patches) (q : Lp ℝ 2 d.charts.measure) :
    patchExtensionL2 d L a (L.localizationL2 a q) =
      DeTurckJetCoordinatesNative.coefficientL2 d.charts.measure
        (L.weight a) (L.weight_smooth a) q := by
  classical
  let K : Set M := tsupport (nativeCutoffs d L a).eta
  have hK : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have hKs : K ⊆ (L.chart a).source := (nativeCutoffs d L a).eta_support
  have hac : (d.charts.measure.restrict K).map (measurableChart (L.chart a)) ≪ volume :=
    Measure.absolutelyContinuous_of_le_smul
      (map_restrict_le_smul_volume (L.chart a) hK hKs (patchExtensionMeasureBound d L a))
  have hp := ae_eq_comp' (measurable_measurableChart (L.chart a)).aemeasurable
    (L.localizationL2_coe a q) hac
  have hlocal : (fun x => (L.localizationL2 a q) (L.chart a x)) =ᵐ[d.charts.measure.restrict K]
      fun x => L.weight a x * q x := by
    filter_upwards [hp, ae_restrict_mem hK] with x hx hxK
    have hxU := hKs hxK
    simp only [Function.comp_apply, measurableChart_of_mem (L.chart a) hxU] at hx
    rw [L.scalarCutoff_mul_eq_chartScalar a q,
      chartScalar_of_mem a.val.1.val _ ((L.chart a).map_source hxU)] at hx
    change (L.localizationL2 a q) (L.chart a x) =
      L.weight a ((L.chart a).symm (L.chart a x)) * q ((L.chart a).symm (L.chart a x)) at hx
    rw [(L.chart a).left_inv hxU] at hx
    exact hx
  have hext : patchExtensionL2 d L a (L.localizationL2 a q) =ᵐ[d.charts.measure]
      K.indicator (fun x => (L.localizationL2 a q) (L.chart a x)) :=
    chartExtensionL2_coe (L.chart a) hK hKs (patchExtensionConstant_ne_top d L a)
      (patchExtensionMeasureBound d L a) (L.localizationL2 a q)
  have hrec := hext.trans ((ae_eq_restrict_iff_indicator_ae_eq hK).mp hlocal)
  apply Lp.ext
  filter_upwards [hrec, DeTurckJetCoordinatesNative.coefficientL2_coe d.charts.measure
    (L.weight a) (L.weight_smooth a) q] with x hx hq
  rw [hq]
  by_cases hxK : x ∈ K
  · simpa only [indicator_of_mem hxK] using hx
  · have hxw : x ∉ tsupport (L.weight a) :=
      fun h => hxK ((nativeCutoffs d L a).mem_eta_support h)
    simpa only [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxw, zero_mul] using hx

theorem sum_patchExtension_localization (q : Lp ℝ 2 d.charts.measure) :
    (∑ a : L.patches, patchExtensionL2 d L a (L.localizationL2 a q)) = q := by
  simp_rw [patchExtension_localization]
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun a : L.patches => DeTurckJetCoordinatesNative.coefficientL2 d.charts.measure
        (L.weight a) (L.weight_smooth a) q),
    ae_all_iff.mpr (fun a : L.patches =>
      DeTurckJetCoordinatesNative.coefficientL2_coe d.charts.measure
        (L.weight a) (L.weight_smooth a) q)] with x hsum hterms
  rw [hsum]
  simp only [hterms]
  rw [← Finset.sum_mul, L.weight_sum, one_mul]

theorem patchNativeJet_nil (a : L.patches) (k : ℕ)
    (Q : WordIndex (Fin n) k → ScalarL2 n) :
    patchNativeJet d L a k Q (wordIndex [] (by simp)) =
      patchExtensionL2 d L a (Q (wordIndex [] (by simp))) := by
  simp only [patchNativeJet, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    wordIndex_word, nativeWordTerms, wordTerms, termsL2,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply, add_zero,
    ContinuousLinearMap.proj_apply, patchCoordinateJet]
  apply Lp.ext
  filter_upwards [DeTurckJetCoordinatesNative.coefficientL2_coe (n := n) d.charts.measure
    (fun _ : M => (1 : ℝ)) contMDiff_const
    (patchExtensionL2 d L a (Q (wordIndex [] (by simp))))] with x hx
  simpa only [one_mul] using hx

include L in

theorem exists_smooth_probe_approximation (k : ℕ)
    (z : SpectralHeatNative.State d.SymmetricIndex) :
    ∃ f : ℕ → d.ProbeIndex → M → ℝ,
      (∀ j ab, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j ab)) ∧
      ∃ P : ℕ → ProbeTuples d k, ∃ Q : ProbeTuples d k,
        Tendsto P atTop (𝓝 Q) ∧
        (∀ j ab w (hw : w.length ≤ k),
          P j ab (wordIndex w hw) =ᵐ[d.charts.measure] directionalWord d.fields w (f j ab)) ∧
        ∀ ab, Q ab (wordIndex [] (by simp)) =
          d.valueCoefficient ab (d.symmetricScaleValue k z : d.Value) := by
  classical
  obtain ⟨r, hr, hcore⟩ := exists_common_patch_radius d L
  choose q hq0 hq using fun (a : L.patches) (ab : d.ProbeIndex) =>
    exists_symmetricScale_localized_weakJet d k L a ab z
  have hsupported (a : L.patches) (ab : d.ProbeIndex) :
      ∀ᵐ x ∂volume, x ∉ nativeCoordinateSupport d L a → q a ab [] x = 0 := by
    rw [hq0]
    exact localizedScaleValue_ae_support d L a ab k z
  choose S hsupport hS using fun (a : L.patches) (ab : d.ProbeIndex) =>
    exists_schwartz_approximation_of_finite_weak_jets (q a ab) k
      (nativeCoordinateSupport_isCompact d L a) (hsupported a ab)
      (fun w hw i φ => by
        simpa only [inner_schwartz, SchwartzMap.lineDerivOp_apply_eq_fderiv]
          using hq a ab w hw i φ) hr
  let f : ℕ → d.ProbeIndex → M → ℝ :=
    fun j ab x => ∑ a : L.patches, liftSchwartz d L a (S a ab j) x
  let P : ℕ → ProbeTuples d k := fun j ab =>
    ∑ a : L.patches, patchNativeJet d L a k (schwartzWordTuple k (S a ab j))
  let Q : ProbeTuples d k := fun ab =>
    ∑ a : L.patches, patchNativeJet d L a k (fun w => q a ab (List.ofFn w.2))
  have hf (j : ℕ) (ab : d.ProbeIndex) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j ab) :=
    contMDiff_finsetSum (fun a _ => liftSchwartz_contMDiff d L a (S a ab j))
  refine ⟨f, hf, P, Q, ?_, ?_, ?_⟩
  · apply tendsto_pi_nhds.mpr
    intro ab
    apply tendsto_finset_sum
    intro a _
    apply ((patchNativeJet d L a k).continuous.tendsto _).comp
    apply tendsto_pi_nhds.mpr
    intro w
    exact hS a ab (List.ofFn w.2)
      (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt)
  · intro j ab w hw
    have hterm (a : L.patches) := patchNativeJet_schwartz d L a k (S a ab j)
      (hsupport a ab j).1 ((hsupport a ab j).2.trans (hcore a)) w hw
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
        (fun a : L.patches => patchNativeJet d L a k
          (schwartzWordTuple k (S a ab j)) (wordIndex w hw)),
      ae_all_iff.mpr hterm] with x hsum hterms
    simp only [P, Finset.sum_apply]
    rw [hsum]
    simp only [hterms]
    exact (DeTurckInverseCompositionNative.directionalWord_sum Finset.univ d.fields w
      (fun a => liftSchwartz d L a (S a ab j))
      (fun a _ => liftSchwartz_contMDiff d L a (S a ab j)) x).symm
  · intro ab
    simp only [Q, Finset.sum_apply]
    simp only [patchNativeJet_nil, wordIndex_word, hq0]
    exact sum_patchExtension_localization d L _

def decodedTensor (f : d.ProbeIndex → M → ℝ)
    (hf : ∀ ab, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f ab)) : SmoothTensor (n := n) (M := M) :=
  smoothDecode g0 d.fields (fun x => WithLp.toLp 2 (fun ab => f ab x)) hf

def symmetricDecodedTensor (f : d.ProbeIndex → M → ℝ)
    (hf : ∀ ab, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f ab)) : SmoothTensor (n := n) (M := M) :=
  (1 / 2 : ℝ) • (decodedTensor d f hf + d.transposeSmooth (decodedTensor d f hf))

theorem symmetricDecodedTensor_symm (f : d.ProbeIndex → M → ℝ)
    (hf : ∀ ab, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f ab))
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    symmetricDecodedTensor d f hf x v w = symmetricDecodedTensor d f hf x w v := by
  change (1 / 2 : ℝ) * (decodedTensor d f hf x v w +
      d.transposeSmooth (decodedTensor d f hf) x v w) =
    (1 / 2 : ℝ) * (decodedTensor d f hf x w v +
      d.transposeSmooth (decodedTensor d f hf) x w v)
  rw [d.transposeSmooth_apply, d.transposeSmooth_apply, add_comm]

def symmetricKernel (a b : d.ProbeIndex) (x : M) : ℝ :=
  (1 / 2 : ℝ) * (projectionKernel g0 d.fields x a b +
    projectionKernel g0 d.fields x (a.2, a.1) b)

theorem symmetricKernel_contMDiff (a b : d.ProbeIndex) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (symmetricKernel d a b) :=
  contMDiff_const.mul ((projectionKernel_contMDiff d.fields g0 a b).add
    (projectionKernel_contMDiff d.fields g0 (a.2, a.1) b))

theorem scalarProbe_decodedTensor (f : d.ProbeIndex → M → ℝ)
    (hf : ∀ ab, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f ab)) (a : d.ProbeIndex) (x : M) :
    scalarProbe d.fields (decodedTensor d f hf) a x =
      ∑ b : d.ProbeIndex, projectionKernel g0 d.fields x a b * f b x := by
  change probes d.fields (decodedTensor d f hf) x a = _
  rw [decodedTensor, probes_smoothDecode, nativeProjection_eq_kernel]
  exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)

theorem scalarProbe_symmetricDecodedTensor (f : d.ProbeIndex → M → ℝ)
    (hf : ∀ ab, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f ab)) (a : d.ProbeIndex) (x : M) :
    scalarProbe d.fields (symmetricDecodedTensor d f hf) a x =
      ∑ b : d.ProbeIndex, symmetricKernel d a b x * f b x := by
  change (1 / 2 : ℝ) * (scalarProbe d.fields (decodedTensor d f hf) a x +
    d.transposeSmooth (decodedTensor d f hf) x (d.fields a.1 x) (d.fields a.2 x)) = _
  rw [d.transposeSmooth_apply]
  change (1 / 2 : ℝ) * (scalarProbe d.fields (decodedTensor d f hf) a x +
    scalarProbe d.fields (decodedTensor d f hf) (a.2, a.1) x) = _
  rw [scalarProbe_decodedTensor, scalarProbe_decodedTensor,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [symmetricKernel]
  ring

def identityCoefficient (i j : Fin d.fieldCount) (_ : M) : ℝ := if i = j then 1 else 0

theorem identityCoefficient_contMDiff (i j : Fin d.fieldCount) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (identityCoefficient d i j) := contMDiff_const

theorem fields_eq_identityCoefficient (i : Fin d.fieldCount) (x : M) :
    d.fields i x = ∑ j, identityCoefficient d i j x • d.fields j x := by
  simp [identityCoefficient]

def decodedWordTerms (a b : d.ProbeIndex) (w : List (Fin d.fieldCount)) :
    List (DirectionalTerm (n := n) (M := M) (iota := Fin d.fieldCount)) :=
  weightedWordTerms d.fields (identityCoefficient d) (identityCoefficient_contMDiff d)
    (symmetricKernel d a b) (symmetricKernel_contMDiff d a b) w

theorem decodedWordTerms_order (a b : d.ProbeIndex) (w : List (Fin d.fieldCount)) :
    ∀ t ∈ decodedWordTerms d a b w, t.word.length ≤ w.length :=
  weightedWordTerms_order d.fields (identityCoefficient d) (identityCoefficient_contMDiff d)
    (symmetricKernel d a b) (symmetricKernel_contMDiff d a b) w

theorem decodedWordTerms_eq (f : d.ProbeIndex → M → ℝ)
    (hf : ∀ ab, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f ab))
    (a : d.ProbeIndex) (w : List (Fin d.fieldCount)) (x : M) :
    (∑ b : d.ProbeIndex, directionalTerms d.fields (decodedWordTerms d a b w) (f b) x) =
      directionalWord d.fields w (scalarProbe d.fields (symmetricDecodedTensor d f hf) a) x := by
  have hterm (b : d.ProbeIndex) := weightedWordTerms_eq d.fields
    (identityCoefficient d) (identityCoefficient_contMDiff d) d.fields
    (fields_eq_identityCoefficient d) (symmetricKernel d a b)
    (symmetricKernel_contMDiff d a b) w (hf b) x
  simp only [decodedWordTerms, hterm]
  rw [← directionalWord_sum Finset.univ d.fields w
    (fun b y => symmetricKernel d a b y * f b y)
    (fun b _ => (symmetricKernel_contMDiff d a b).mul (hf b)) x]
  exact congrArg (fun g : M → ℝ => directionalWord d.fields w g x)
    (funext (fun y => (scalarProbe_symmetricDecodedTensor d f hf a y).symm))

def decodedProbeJet (k : ℕ) : ProbeTuples d k →L[ℝ] ProbeTuples d k :=
  ContinuousLinearMap.pi (fun a => ContinuousLinearMap.pi (fun w =>
    ∑ b : d.ProbeIndex,
      (termsL2 d.charts.measure (decodedWordTerms d a b (List.ofFn w.2))
        (fun t ht => (decodedWordTerms_order d a b (List.ofFn w.2) t ht).trans
          (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt))).comp
        (ContinuousLinearMap.proj b)))

theorem decodedProbeJet_ae_eq (k : ℕ) (P : ProbeTuples d k)
    (f : d.ProbeIndex → M → ℝ)
    (hf : ∀ ab, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f ab))
    (hP : ∀ b w (hw : w.length ≤ k),
      P b (wordIndex w hw) =ᵐ[d.charts.measure] directionalWord d.fields w (f b))
    (a : d.ProbeIndex) (w : List (Fin d.fieldCount)) (hw : w.length ≤ k) :
    decodedProbeJet d k P a (wordIndex w hw) =ᵐ[d.charts.measure]
      directionalWord d.fields w (scalarProbe d.fields (symmetricDecodedTensor d f hf) a) := by
  let H (b : d.ProbeIndex) : Lp ℝ 2 d.charts.measure :=
    termsL2 d.charts.measure (decodedWordTerms d a b w)
      (fun t ht => (decodedWordTerms_order d a b w t ht).trans hw) (P b)
  have hH (b : d.ProbeIndex) : H b =ᵐ[d.charts.measure]
      directionalTerms d.fields (decodedWordTerms d a b w) (f b) :=
    termsL2_ae_eq d.fields d.charts.measure (decodedWordTerms d a b w)
      (fun t ht => (decodedWordTerms_order d a b w t ht).trans hw) (P b) (f b) (hP b)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ H, ae_all_iff.mpr hH]
    with x hsum hterms
  simp only [decodedProbeJet, ContinuousLinearMap.pi_apply, wordIndex_word,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  change (∑ b : d.ProbeIndex, H b) x = _
  rw [hsum]
  simp only [hterms]
  exact decodedWordTerms_eq d f hf a w x

def rawValue (k : ℕ) : ProbeTuples d k →L[ℝ]
    Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure :=
  ∑ b : d.ProbeIndex, (insertionLp d.charts.measure b).comp
    ((ContinuousLinearMap.proj (wordIndex ([] : List (Fin d.fieldCount)) (by simp)) :
        (WordIndex (Fin d.fieldCount) k → Lp ℝ 2 d.charts.measure) →L[ℝ]
          Lp ℝ 2 d.charts.measure).comp (ContinuousLinearMap.proj b))

theorem rawValue_eq_of_coordinates (k : ℕ) (Q : ProbeTuples d k) (v : d.Value)
    (hQ : ∀ b, Q b (wordIndex [] (by simp)) = d.valueCoefficient b v) :
    rawValue d k Q = (v : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure) := by
  simp only [rawValue, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, hQ]
  exact sum_insertion_coordinate (ι := d.ProbeIndex) d.charts.measure
    (v : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure)

theorem rawValue_ae_eq (k : ℕ) (P : ProbeTuples d k) (f : d.ProbeIndex → M → ℝ)
    (hP : ∀ b, P b (wordIndex [] (by simp)) =ᵐ[d.charts.measure] f b) :
    rawValue d k P =ᵐ[d.charts.measure] fun x => WithLp.toLp 2 (fun b => f b x) := by
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun b : d.ProbeIndex => insertionLp d.charts.measure b (P b (wordIndex [] (by simp)))),
    ae_all_iff.mpr (fun b : d.ProbeIndex => insertionLp_coe d.charts.measure b
      (P b (wordIndex [] (by simp)))), ae_all_iff.mpr hP] with x hsum hinsert hcoord
  simp only [rawValue, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  change (∑ b : d.ProbeIndex, insertionLp d.charts.measure b (P b (wordIndex [] (by simp)))) x = _
  rw [hsum]
  simp only [hinsert, hcoord]
  exact sum_coordinates (WithLp.toLp 2 (fun b => f b x))

def symmetricRawValue (k : ℕ) : ProbeTuples d k →L[ℝ] d.SymmetricValue :=
  (d.valueSymmetrize.codRestrict d.symmetricValue d.valueSymmetrize_mem).comp
    ((projectedValue d).comp (rawValue d k))

theorem symmetricRawValue_eq_of_coordinates (k : ℕ) (Q : ProbeTuples d k)
    (v : d.SymmetricValue)
    (hQ : ∀ b, Q b (wordIndex [] (by simp)) = d.valueCoefficient b (v : d.Value)) :
    symmetricRawValue d k Q = v := by
  have hproj : projectedValue d (rawValue d k Q) = (v : d.Value) := by
    rw [rawValue_eq_of_coordinates d k Q (v : d.Value) hQ]
    exact projectedValue_eq_self d (v : d.Value)
  apply Subtype.ext
  change d.valueSymmetrize (projectedValue d (rawValue d k Q)) = (v : d.Value)
  rw [hproj]
  exact d.valueSymmetrize_eq_self_of_mem v.property

theorem symmetricRawValue_eq (k : ℕ) (P : ProbeTuples d k)
    (f : d.ProbeIndex → M → ℝ)
    (hf : ∀ ab, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f ab))
    (hP : ∀ b, P b (wordIndex [] (by simp)) =ᵐ[d.charts.measure] f b) :
    symmetricRawValue d k P =
      d.intoSymmetricValue (symmetricDecodedTensor d f hf) (symmetricDecodedTensor_symm d f hf) := by
  have hproj : projectedValue d (rawValue d k P) =
      intoTensorL2 d.fields d.charts.measure (decodedTensor d f hf) := by
    apply projectedValue_eq_of_projection d (rawValue d k P)
      (intoTensorL2 d.fields d.charts.measure (decodedTensor d f hf))
    apply Lp.ext
    filter_upwards [projectionL2_coe g0 d.fields d.parseval d.charts.measure (rawValue d k P),
      rawValue_ae_eq d k P f hP,
      tensorToLp_coe d.fields d.charts.measure (decodedTensor d f hf)] with x hp hraw ht
    change projectionL2 g0 d.fields d.parseval d.charts.measure (rawValue d k P) x =
      tensorToLp d.fields d.charts.measure (decodedTensor d f hf) x
    rw [hp, hraw, ht]
    exact (probes_smoothDecode g0 d.fields (fun y => WithLp.toLp 2 (fun b => f b y)) hf x).symm
  apply Subtype.ext
  change d.valueSymmetrize (projectedValue d (rawValue d k P)) =
    intoTensorL2 d.fields d.charts.measure (symmetricDecodedTensor d f hf)
  rw [hproj, d.valueSymmetrize_apply, d.valueTranspose_into]
  simp only [symmetricDecodedTensor, map_smul, map_add]

include L in

theorem exists_smooth_symmetric_approximation (r : ℕ)
    (z : SpectralHeatNative.State d.SymmetricIndex) :
    ∃ h : ℕ → SmoothTensor (n := n) (M := M),
      ∃ hs : ∀ j (x : M) (v w : TangentSpace (𝓡 n) x), h j x v w = h j x w v,
        Tendsto (fun j => d.smoothTensorCoordinates (2 * r) (h j) (hs j)) atTop (𝓝 z) := by
  obtain ⟨f, hf, P, Q, hPQ, hP, hQ⟩ := exists_smooth_probe_approximation d L (2 * r) z
  let h (j : ℕ) := symmetricDecodedTensor d (f j) (hf j)
  have hs (j : ℕ) (x : M) (v w : TangentSpace (𝓡 n) x) : h j x v w = h j x w v :=
    symmetricDecodedTensor_symm d (f j) (hf j) x v w
  let q := evenOutput d r (decodedProbeJet d (2 * r) Q)
  have hcoords : Tendsto (fun j => d.smoothTensorCoordinates (2 * r) (h j) (hs j))
      atTop (𝓝 q) := by
    have hlim := ((evenOutput d r).continuous.tendsto _).comp
      (((decodedProbeJet d (2 * r)).continuous.tendsto _).comp hPQ)
    have hid (j : ℕ) : evenOutput d r (decodedProbeJet d (2 * r) (P j)) =
        d.smoothTensorCoordinates (2 * r) (h j) (hs j) :=
      evenOutput_eq d r _ (h j) (hs j)
        (decodedProbeJet_ae_eq d (2 * r) (P j) (f j) (hf j) (hP j))
    simpa only [Function.comp_def, hid] using hlim
  have hvalue : Tendsto (fun j => d.intoSymmetricValue (h j) (hs j))
      atTop (𝓝 (d.symmetricScaleValue (2 * r) z)) := by
    have hlim := ((symmetricRawValue d (2 * r)).continuous.tendsto _).comp hPQ
    have hid (j : ℕ) : symmetricRawValue d (2 * r) (P j) =
        d.intoSymmetricValue (h j) (hs j) :=
      symmetricRawValue_eq d (2 * r) (P j) (f j) (hf j)
        (fun b => hP j b [] (by simp))
    simpa only [Function.comp_def, hid, symmetricRawValue_eq_of_coordinates d (2 * r) Q _ hQ]
      using hlim
  have hdecode : Tendsto (fun j => d.intoSymmetricValue (h j) (hs j))
      atTop (𝓝 (d.symmetricScaleValue (2 * r) q)) := by
    simpa only [Function.comp_def, d.symmetricScaleValue_smoothTensorCoordinates] using
      ((d.symmetricScaleValue (2 * r)).continuous.tendsto _).comp hcoords
  have heq : q = z := (d.symmetricScaleValue_injective (2 * r)) (tendsto_nhds_unique hdecode hvalue)
  exact ⟨h, hs, heq ▸ hcoords⟩

theorem nativeProbeTupleL2_eq_smoothProbeTuples (k : ℕ)
    (h : SmoothTensor (n := n) (M := M))
    (hs : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    nativeProbeTupleL2 d L k k le_rfl (d.smoothTensorCoordinates k h hs) =
      smoothProbeTuples d k h := by
  funext b w
  apply Lp.ext
  have hw : (List.ofFn w.2).length ≤ k := by
    simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt
  exact (nativeWordL2_smoothTensorCoordinates d L b k (List.ofFn w.2) hw h hs).trans
    (ContinuousMap.coeFn_toLp (p := (2 : ENNReal)) (𝕜 := ℝ) d.charts.measure
      (⟨directionalWord d.fields (List.ofFn w.2) (scalarProbe d.fields h b),
        (directionalWord_contMDiff d.fields (List.ofFn w.2)
          (scalarProbe_contMDiff d.fields h b)).continuous⟩ : C(M, ℝ))).symm

theorem evenOutput_nativeProbeTupleL2 (r : ℕ)
    (z : SpectralHeatNative.State d.SymmetricIndex) :
    evenOutput d r (nativeProbeTupleL2 d L (2 * r) (2 * r) le_rfl z) = z := by
  obtain ⟨h, hs, hlim⟩ := exists_smooth_symmetric_approximation d L r z
  have hout := ((evenOutput d r).continuous.tendsto _).comp
    (((nativeProbeTupleL2 d L (2 * r) (2 * r) le_rfl).continuous.tendsto _).comp hlim)
  have hid (j : ℕ) : evenOutput d r
      (nativeProbeTupleL2 d L (2 * r) (2 * r) le_rfl
        (d.smoothTensorCoordinates (2 * r) (h j) (hs j))) =
      d.smoothTensorCoordinates (2 * r) (h j) (hs j) := by
    rw [nativeProbeTupleL2_eq_smoothProbeTuples, evenOutput_smoothProbeTuples]
  exact tendsto_nhds_unique (by simpa only [Function.comp_def, hid] using hout) hlim

end PoincareConjecture.DeTurckStateApproximationNative

end
