import PoincareConjecture.Proofs.M03.Existence.DeTurckNestedLocalizationNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckJetCoordinatesNative
import PoincareConjecture.Proofs.M03.Existence.EuclideanFourierCoordinatesNative
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped Manifold ContDiff Bundle Topology BigOperators SchwartzMap LineDeriv
  BoundedContinuousFunction

namespace PoincareConjecture.DeTurckMetricDomainNative

open TensorProbeNative TensorHilbertNative ChartMeasureNative DeTurckNative
  DeTurckCompatibleJetNative DeTurckJetCoordinatesNative DeTurckNestedLocalizationNative
  DeTurckInverseCompositionNative DeTurckDomainRegularityNative
  DeTurckHigherDomainNative EuclideanDerivativeNative NativeChartScalarLocalization
  EuclideanFourierCoordinatesNative EuclideanSobolevContinuousNative EuclideanTranslationNative

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {g0 : RiemannianMetric n M} (d : Data g0)
  (L : FiniteChartLocalizationData d.charts)

local notation "E" => EuclideanSpace ℝ (Fin n)

def nativeCutoffs (a : L.patches) : Cutoffs (n := n) a.val.1.val (tsupport (L.weight a)) :=
  Classical.choice (exists_cutoffs a.val.1.val (isClosed_tsupport (L.weight a)).isCompact
    (L.weight_support_source a))

def cutoffNativeField (a : L.patches) (i : Fin d.fieldCount) :
    SmoothField (n := n) (M := M) :=
  ⟨fun x => (nativeCutoffs d L a).eta x • d.fields i x,
    (nativeCutoffs d L a).eta_smooth.smul_section (d.fields i).contMDiff⟩

def nativeChartCoefficient (a : L.patches) (i : Fin d.fieldCount) (j : Fin n)
    (x : M) : ℝ :=
  (nativeCutoffs d L a).eta x *
    chartField a.val.1.val (d.fields i) (chartAt E a.val.1.val x) j

theorem nativeChartCoefficient_contMDiff (a : L.patches)
    (i : Fin d.fieldCount) (j : Fin n) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (nativeChartCoefficient d L a i j) :=
  FiniteChartData.contMDiff_weight_mul_chart a.val.1.val
    (nativeCutoffs d L a).eta_smooth (nativeCutoffs d L a).eta_support
    (contDiffOn_chartField_coordinate a.val.1.val (d.fields i) j)

theorem sum_chartField_frame (p : M) (V : SmoothField (n := n) (M := M))
    {x : M} (hx : x ∈ (chartAt E p).source) :
    (∑ j, chartField p V (chartAt E p x) j • chartFrame p j x) = V x := by
  let e := chartDifferentialEquiv p x hx
  have hcoord : chartField p V (chartAt E p x) = e (V x) := by
    change mfderiv (𝓡 n) 𝓘(ℝ, E) (chartAt E p)
      ((chartAt E p).symm (chartAt E p x)) (V ((chartAt E p).symm (chartAt E p x))) = _
    rw [(chartAt E p).left_inv hx]
    change mfderiv (𝓡 n) 𝓘(ℝ, E) (chartAt E p) x (V x) =
      (chartDifferentialEquiv p x hx : TangentSpace (𝓡 n) x →L[ℝ] E) (V x)
    rw [chartDifferentialEquiv_coe]
    rfl
  calc
    _ = e.symm (∑ j, chartField p V (chartAt E p x) j • (PiLp.basisFun 2 ℝ (Fin n)) j) := by
      simp only [map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro j _
      rw [chartFrame_eq_basis p x hx j]
      rfl
    _ = e.symm (chartField p V (chartAt E p x)) := by
      congr 1
      simpa only [PiLp.basisFun_repr] using
        (PiLp.basisFun 2 ℝ (Fin n)).sum_repr (chartField p V (chartAt E p x))
    _ = V x := by rw [hcoord]; exact e.symm_apply_apply (V x)

theorem cutoffNativeField_eq_sum (a : L.patches) (i : Fin d.fieldCount) (x : M) :
    cutoffNativeField d L a i x =
      ∑ j, nativeChartCoefficient d L a i j x • (nativeCutoffs d L a).field j x := by
  let C := nativeCutoffs d L a
  change C.eta x • d.fields i x =
    ∑ j, (C.eta x * chartField a.val.1.val (d.fields i) (chartAt E a.val.1.val x) j) • C.field j x
  by_cases hz : C.eta x = 0
  · simp only [hz, zero_smul, zero_mul, Finset.sum_const_zero]
  · have hxeta : x ∈ tsupport C.eta := subset_tsupport C.eta hz
    have hx : x ∈ (chartAt E a.val.1.val).source := C.eta_support hxeta
    have hfield (j : Fin n) : C.field j x = chartFrame a.val.1.val j x :=
      (C.field_eventuallyEq (C.zeta_one x hxeta) j).eq_of_nhds
    simp_rw [hfield, mul_smul]
    rw [← Finset.smul_sum, sum_chartField_frame a.val.1.val (d.fields i) hx]

def nativeWordTerms (a : L.patches) (w : List (Fin d.fieldCount)) :
    List (DirectionalTerm (n := n) (M := M) (iota := Fin n)) :=
  wordTerms (nativeCutoffs d L a).field (nativeChartCoefficient d L a)
    (nativeChartCoefficient_contMDiff d L a) w

theorem nativeWordTerms_order (a : L.patches) (w : List (Fin d.fieldCount)) :
    ∀ t ∈ nativeWordTerms d L a w, t.word.length ≤ w.length :=
  wordTerms_order (nativeCutoffs d L a).field (nativeChartCoefficient d L a)
    (nativeChartCoefficient_contMDiff d L a) w

theorem nativeWordTerms_eq (a : L.patches) (w : List (Fin d.fieldCount))
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    directionalTerms (nativeCutoffs d L a).field (nativeWordTerms d L a w) f x =
      directionalWord (cutoffNativeField d L a) w f x :=
  wordTerms_eq (nativeCutoffs d L a).field (nativeChartCoefficient d L a)
    (nativeChartCoefficient_contMDiff d L a) (cutoffNativeField d L a)
    (cutoffNativeField_eq_sum d L a) w hf x

def reconstructedCoordinateTuple (a : L.patches) (ab : d.ProbeIndex) (k s : ℕ)
    (hs : s ≤ k) : SpectralHeatNative.State d.SymmetricIndex →L[ℝ]
      (WordIndex (Fin n) s → Lp ℝ 2 d.charts.measure) :=
  ContinuousLinearMap.pi (fun w => (L.reconstructionL2 a).comp
    (localizedScaleDerivative d L a ab k (List.ofFn w.2)
      ((show (List.ofFn w.2).length ≤ s by
        simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt).trans hs)))

theorem reconstructedCoordinateTuple_scaleDecode (a : L.patches) (ab : d.ProbeIndex)
    (k l s : ℕ) (hs : s ≤ k) (x : SpectralHeatNative.State d.SymmetricIndex) :
    reconstructedCoordinateTuple d L a ab (k + l) s (by omega) x =
      reconstructedCoordinateTuple d L a ab k s hs
        (SpectralHeatNative.scaleDecode d.symmetricParameters l x) := by
  funext w
  change L.reconstructionL2 a (localizedScaleDerivative d L a ab (k + l)
      (List.ofFn w.2) _ x) =
    L.reconstructionL2 a (localizedScaleDerivative d L a ab k (List.ofFn w.2) _
      (SpectralHeatNative.scaleDecode d.symmetricParameters l x))
  exact congrArg (L.reconstructionL2 a)
    (localizedScaleDerivative_scaleDecode d L a ab k l (List.ofFn w.2)
      ((show (List.ofFn w.2).length ≤ s by
        simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt).trans hs) x)

def nativeWordL2 (ab : d.ProbeIndex) (k : ℕ) (w : List (Fin d.fieldCount))
    (hw : w.length ≤ k) :
    SpectralHeatNative.State d.SymmetricIndex →L[ℝ] Lp ℝ 2 d.charts.measure :=
  ∑ a : L.patches,
    (termsL2 d.charts.measure (nativeWordTerms d L a w) (nativeWordTerms_order d L a w)).comp
      (reconstructedCoordinateTuple d L a ab k w.length hw)

theorem nativeWordL2_scaleDecode (ab : d.ProbeIndex) (k l : ℕ)
    (w : List (Fin d.fieldCount)) (hw : w.length ≤ k)
    (x : SpectralHeatNative.State d.SymmetricIndex) :
    nativeWordL2 d L ab (k + l) w (by omega) x =
      nativeWordL2 d L ab k w hw (SpectralHeatNative.scaleDecode d.symmetricParameters l x) := by
  simp only [nativeWordL2, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [reconstructedCoordinateTuple_scaleDecode d L a ab k l w.length hw x]

theorem localizedScaleValue_smoothTensorCoordinates (a : L.patches) (ab : d.ProbeIndex)
    (k : ℕ) (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    localizedScaleValue d L a ab k (d.smoothTensorCoordinates k h hsymm) =
      (d.localizedSchwartz L a ab h).toLp 2 volume := by
  change L.localizationL2 a
    (d.valueCoefficient ab (d.symmetricScaleValue k (d.smoothTensorCoordinates k h hsymm))) = _
  rw [d.symmetricScaleValue_smoothTensorCoordinates]
  exact d.localizedValue_into L a ab h

theorem localizedScaleDerivative_smoothTensorCoordinates (a : L.patches)
    (ab : d.ProbeIndex) (k : ℕ) (w : List (Fin n)) (hw : w.length ≤ k)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v v' : TangentSpace (𝓡 n) x), h x v v' = h x v' v) :
    localizedScaleDerivative d L a ab k w hw (d.smoothTensorCoordinates k h hsymm) =
      (orderedSchwartzDerivative w (d.localizedSchwartz L a ab h)).toLp 2 volume := by
  apply localizedScaleDerivative_eq_jet d L a ab k w hw
    (d.smoothTensorCoordinates k h hsymm)
    (fun v => (orderedSchwartzDerivative v (d.localizedSchwartz L a ab h)).toLp 2 volume)
  · exact (localizedScaleValue_smoothTensorCoordinates d L a ab k h hsymm).symm
  · intro v _ i φ
    change inner ℝ
      ((∂_{EuclideanSpace.single i (1 : ℝ)}
        (orderedSchwartzDerivative v (d.localizedSchwartz L a ab h))).toLp 2 volume)
      (φ.toLp 2 volume) = _
    have hid := inner_schwartzLineDeriv
      (orderedSchwartzDerivative v (d.localizedSchwartz L a ab h)) φ
      (EuclideanSpace.single i (1 : ℝ))
    linarith only [hid]

theorem directionalWord_zero {ι : Type*} (F : ι → SmoothField (n := n) (M := M))
    (w : List ι) : directionalWord F w (0 : M → ℝ) = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [directionalWord_cons, ih]
    funext x
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun _ : M => (0 : ℝ)) x (F i x) = 0
    simp

theorem directionalWord_zero_off_closed {ι : Type*}
    (F : ι → SmoothField (n := n) (M := M)) (w : List ι)
    {f : M → ℝ} {K : Set M} (hK : IsClosed K) (hf : ∀ x ∉ K, f x = 0)
    {x : M} (hx : x ∉ K) : directionalWord F w f x = 0 := by
  induction w generalizing x with
  | nil => exact hf x hx
  | cons i w ih =>
    have hz : directionalWord F w f =ᶠ[𝓝 x] 0 := by
      filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
      exact ih hy
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (directionalWord F w f) x (F i x) = 0
    calc
      _ = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun _ : M => (0 : ℝ)) x (F i x) :=
        congrArg (fun A : TangentSpace (𝓡 n) x →L[ℝ] ℝ => A (F i x))
          (hz.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)))
      _ = 0 := by simp

theorem directionalWord_fields_eventuallyEq {ι : Type*}
    (F G : ι → SmoothField (n := n) (M := M)) (w : List ι) (f : M → ℝ) {x : M}
    (hFG : ∀ i, (F i : (y : M) → TangentSpace (𝓡 n) y) =ᶠ[𝓝 x] G i) :
    directionalWord F w f =ᶠ[𝓝 x] directionalWord G w f := by
  induction w with
  | nil => exact Filter.EventuallyEq.rfl
  | cons i w ih =>
    filter_upwards [ih.eventuallyEq_nhds, hFG i] with y hy hiy
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (directionalWord F w f) y (F i y) =
      mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (directionalWord G w f) y (G i y)
    exact (congrArg (fun A => A (F i y))
      (hy.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)))).trans
      (congrArg (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (directionalWord G w f) y) hiy)

theorem chartDifferential_chartFrame (p : M) {x : M}
    (hx : x ∈ (chartAt E p).source) (i : Fin n) :
    mfderiv (𝓡 n) 𝓘(ℝ, E) (chartAt E p) x (chartFrame p i x) =
      EuclideanSpace.single i (1 : ℝ) := by
  rw [chartFrame_eq_basis p x hx i]
  change @Eq E
    ((mfderiv (𝓡 n) 𝓘(ℝ, E) (extChartAt (𝓡 n) p) x : TangentSpace (𝓡 n) x →L[ℝ] E)
      ((chartDifferentialEquiv p x hx).symm ((PiLp.basisFun 2 ℝ (Fin n)) i)))
    (EuclideanSpace.single i (1 : ℝ))
  rw [← chartDifferentialEquiv_coe p x hx]
  change (chartDifferentialEquiv p x hx)
    ((chartDifferentialEquiv p x hx).symm ((PiLp.basisFun 2 ℝ (Fin n)) i)) =
    EuclideanSpace.single i (1 : ℝ)
  exact ((chartDifferentialEquiv p x hx).apply_symm_apply _).trans
    (PiLp.basisFun_apply 2 ℝ (Fin n) i)

theorem directionalWord_chartPullback_eventuallyEq (p : M)
    (F : Fin n → SmoothField (n := n) (M := M))
    {x : M} (hx : x ∈ (chartAt E p).source)
    (hF : ∀ i, (F i : (y : M) → TangentSpace (𝓡 n) y) =ᶠ[𝓝 x] chartFrame p i)
    (w : List (Fin n)) (φ : 𝓢(E, ℝ)) {f : M → ℝ}
    (hf : f =ᶠ[𝓝 x] fun y => φ (chartAt E p y)) :
    directionalWord F w f =ᶠ[𝓝 x]
      fun y => orderedSchwartzDerivative w φ (chartAt E p y) := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
    filter_upwards [ih.eventuallyEq_nhds, hF i,
      (chartAt E p).open_source.mem_nhds hx] with y hy hiy hyU
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (directionalWord F w f) y (F i y) =
      fderiv ℝ (orderedSchwartzDerivative w φ) (chartAt E p y)
        (EuclideanSpace.single i (1 : ℝ))
    rw [hy.mfderiv_eq, hiy]
    have hchain := mfderiv_comp_apply y
      (((orderedSchwartzDerivative w φ).smooth (⊤ : ℕ∞)).contMDiff.mdifferentiable
        (by simp) (chartAt E p y))
      ((mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt hyU)
      (chartFrame p i y)
    rw [mfderiv_eq_fderiv, chartDifferential_chartFrame p hyU i] at hchain
    exact hchain

theorem cutoffNativeField_word_localized (a : L.patches) (w : List (Fin d.fieldCount))
    (f : M → ℝ) (x : M) :
    directionalWord (cutoffNativeField d L a) w (fun y => L.weight a y * f y) x =
      directionalWord d.fields w (fun y => L.weight a y * f y) x := by
  by_cases hx : x ∈ tsupport (L.weight a)
  · apply (directionalWord_fields_eventuallyEq
      (cutoffNativeField d L a) d.fields w (fun y => L.weight a y * f y) ?_).eq_of_nhds
    intro i
    filter_upwards [(nativeCutoffs d L a).eta_one x hx] with y hy
    change (nativeCutoffs d L a).eta y • d.fields i y = d.fields i y
    rw [hy, Pi.one_apply, one_smul]
  · rw [directionalWord_zero_off_closed (cutoffNativeField d L a) w
      (isClosed_tsupport (L.weight a)) (fun y hy => by
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]) hx,
      directionalWord_zero_off_closed d.fields w (isClosed_tsupport (L.weight a))
        (fun y hy => by rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]) hx]

theorem chartWord_localizedSchwartz (a : L.patches) (ab : d.ProbeIndex)
    (h : SmoothTensor (n := n) (M := M)) (w : List (Fin n))
    {x : M} (hx : x ∈ tsupport (L.weight a)) :
    directionalWord (nativeCutoffs d L a).field w
        (fun y => L.weight a y * scalarProbe d.fields h ab y) x =
      orderedSchwartzDerivative w (d.localizedSchwartz L a ab h) (L.chart a x) := by
  let C := nativeCutoffs d L a
  have hxU := L.weight_support_source a hx
  have hxeta : x ∈ tsupport C.eta := by
    apply subset_tsupport C.eta
    change C.eta x ≠ 0
    rw [show C.eta x = (1 : ℝ) by
      simpa only [Pi.one_apply] using (C.eta_one x hx).eq_of_nhds]
    exact one_ne_zero
  apply (directionalWord_chartPullback_eventuallyEq a.val.1.val C.field hxU
    (fun i => C.field_eventuallyEq (C.zeta_one x hxeta) i)
    w (d.localizedSchwartz L a ab h) ?_).eq_of_nhds
  filter_upwards [(chartAt E a.val.1.val).open_source.mem_nhds hxU] with y hy
  rw [d.localizedSchwartz_apply,
    chartScalar_of_mem a.val.1.val _ ((chartAt E a.val.1.val).map_source hy),
    (chartAt E a.val.1.val).left_inv hy]

theorem reconstruction_ordered_localizedSchwartz (a : L.patches) (ab : d.ProbeIndex)
    (h : SmoothTensor (n := n) (M := M)) (w : List (Fin n)) :
    L.reconstructionL2 a ((orderedSchwartzDerivative w
      (d.localizedSchwartz L a ab h)).toLp 2 volume) =ᵐ[d.charts.measure]
        directionalWord (nativeCutoffs d L a).field w
          (fun y => L.weight a y * scalarProbe d.fields h ab y) := by
  have hrec := ChartPushforwardLpNative.chartExtensionL2_toLp_coe (L.chart a)
    (isClosed_tsupport (L.weight a)).measurableSet (L.weight_support_source a)
    (L.reconstructionConstant_ne_top a) (L.reconstructionMeasureBound a)
    ((orderedSchwartzDerivative w (d.localizedSchwartz L a ab h)).memLp 2 volume)
  apply hrec.trans
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ tsupport (L.weight a)
  · rw [indicator_of_mem hx]
    exact (chartWord_localizedSchwartz d L a ab h w hx).symm
  · rw [indicator_of_notMem hx]
    exact (directionalWord_zero_off_closed (nativeCutoffs d L a).field w
      (isClosed_tsupport (L.weight a))
      (fun y hy => by rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]) hx).symm

theorem reconstructedCoordinateTuple_smoothTensorCoordinates (a : L.patches)
    (ab : d.ProbeIndex) (k s : ℕ) (hs : s ≤ k)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v v' : TangentSpace (𝓡 n) x), h x v v' = h x v' v)
    (w : List (Fin n)) (hw : w.length ≤ s) :
    reconstructedCoordinateTuple d L a ab k s hs (d.smoothTensorCoordinates k h hsymm)
      (wordIndex w hw) =ᵐ[d.charts.measure]
        directionalWord (nativeCutoffs d L a).field w
          (fun y => L.weight a y * scalarProbe d.fields h ab y) := by
  change L.reconstructionL2 a (localizedScaleDerivative d L a ab k
    (List.ofFn (wordIndex w hw).2) _ (d.smoothTensorCoordinates k h hsymm)) =ᵐ[_] _
  rw [localizedScaleDerivative_smoothTensorCoordinates, wordIndex_word]
  exact reconstruction_ordered_localizedSchwartz d L a ab h w

theorem nativeWordL2_smoothTensorCoordinates (ab : d.ProbeIndex) (k : ℕ)
    (w : List (Fin d.fieldCount)) (hw : w.length ≤ k)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v v' : TangentSpace (𝓡 n) x), h x v v' = h x v' v) :
    nativeWordL2 d L ab k w hw (d.smoothTensorCoordinates k h hsymm) =ᵐ[d.charts.measure]
      directionalWord d.fields w (scalarProbe d.fields h ab) := by
  let q (a : L.patches) : Lp ℝ 2 d.charts.measure :=
    termsL2 d.charts.measure (nativeWordTerms d L a w) (nativeWordTerms_order d L a w)
      (reconstructedCoordinateTuple d L a ab k w.length hw
        (d.smoothTensorCoordinates k h hsymm))
  have hq (a : L.patches) : q a =ᵐ[d.charts.measure]
      directionalWord d.fields w (fun y => L.weight a y * scalarProbe d.fields h ab y) := by
    apply (termsL2_ae_eq (nativeCutoffs d L a).field d.charts.measure
      (nativeWordTerms d L a w) (nativeWordTerms_order d L a w)
      (reconstructedCoordinateTuple d L a ab k w.length hw
        (d.smoothTensorCoordinates k h hsymm))
      (fun y => L.weight a y * scalarProbe d.fields h ab y)
      (reconstructedCoordinateTuple_smoothTensorCoordinates d L a ab k w.length hw
        h hsymm)).trans
    apply Eventually.of_forall
    intro x
    have hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => L.weight a y * scalarProbe d.fields h ab y) :=
      (L.weight_smooth a).mul (scalarProbe_contMDiff d.fields h ab)
    rw [nativeWordTerms_eq d L a w hf, cutoffNativeField_word_localized]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ q, ae_all_iff.mpr hq] with x hsum hqx
  simp only [nativeWordL2, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  change (∑ a : L.patches, q a) x = _
  rw [hsum]
  have hpartition : (fun y => ∑ a : L.patches, L.weight a y * scalarProbe d.fields h ab y) =
      scalarProbe d.fields h ab := by
    funext y
    rw [← Finset.sum_mul, L.weight_sum, one_mul]
  calc
    _ = ∑ a : L.patches, directionalWord d.fields w
        (fun y => L.weight a y * scalarProbe d.fields h ab y) x :=
      Finset.sum_congr rfl (fun a _ => hqx a)
    _ = directionalWord d.fields w
        (fun y => ∑ a : L.patches, L.weight a y * scalarProbe d.fields h ab y) x :=
      (directionalWord_sum Finset.univ d.fields w
        (fun a y => L.weight a y * scalarProbe d.fields h ab y)
        (fun a _ => (L.weight_smooth a).mul (scalarProbe_contMDiff d.fields h ab)) x).symm
    _ = _ := congrArg (fun f => directionalWord d.fields w f x) hpartition

def nativeProbeTupleL2 (k s : ℕ) (hs : s ≤ k) :
    SpectralHeatNative.State d.SymmetricIndex →L[ℝ]
      (d.ProbeIndex → WordIndex (Fin d.fieldCount) s → Lp ℝ 2 d.charts.measure) :=
  ContinuousLinearMap.pi (fun ab => ContinuousLinearMap.pi (fun w =>
    nativeWordL2 d L ab k (List.ofFn w.2)
      ((show (List.ofFn w.2).length ≤ s by
        simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt).trans hs)))

theorem nativeProbeTupleL2_scaleDecode (k l s : ℕ) (hs : s ≤ k)
    (x : SpectralHeatNative.State d.SymmetricIndex) :
    nativeProbeTupleL2 d L (k + l) s (by omega) x =
      nativeProbeTupleL2 d L k s hs (SpectralHeatNative.scaleDecode d.symmetricParameters l x) := by
  funext ab w
  exact nativeWordL2_scaleDecode d L ab k l (List.ofFn w.2)
    ((show (List.ofFn w.2).length ≤ s by
      simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt).trans hs) x

theorem nativeProbeTupleL2_smoothTensorCoordinates (k s : ℕ) (hs : s ≤ k)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v v' : TangentSpace (𝓡 n) x), h x v v' = h x v' v)
    (ab : d.ProbeIndex) (w : List (Fin d.fieldCount)) (hw : w.length ≤ s) :
    nativeProbeTupleL2 d L k s hs (d.smoothTensorCoordinates k h hsymm) ab
      (wordIndex w hw) =ᵐ[d.charts.measure] directionalWord d.fields w (scalarProbe d.fields h ab) := by
  change nativeWordL2 d L ab k (List.ofFn (wordIndex w hw).2) _
    (d.smoothTensorCoordinates k h hsymm) =ᵐ[_] _
  simp only [wordIndex_word]
  exact nativeWordL2_smoothTensorCoordinates d L ab k w (hw.trans hs) h hsymm

def schwartzWordTuple (k : ℕ) (φ : 𝓢(E, ℝ)) : WordIndex (Fin n) k → ScalarL2 n :=
  fun w => (orderedSchwartzDerivative (List.ofFn w.2) φ).toLp 2 volume

def finiteJetFrequency (k : ℕ) : (p : ℕ) → (w : List (Fin n)) →
    2 * p + w.length ≤ k →
    (WordIndex (Fin n) k → ScalarL2 n) →L[ℝ] FrequencyL2 n
  | 0, w, hw => ((fourierCLM ℂ (FrequencyL2 n)).restrictScalars ℝ).comp
      (coordinateComplexification.comp
        (ContinuousLinearMap.proj (wordIndex w (by omega))))
  | p + 1, w, hw => finiteJetFrequency k p w (by omega) -
      (laplacianFactor : ℂ) • ∑ i : Fin n,
        finiteJetFrequency k p (i :: i :: w) (by simp only [List.length_cons]; omega)

theorem finiteJetFrequency_schwartz (k p : ℕ) (w : List (Fin n))
    (hw : 2 * p + w.length ≤ k) (φ : 𝓢(E, ℝ)) :
    finiteJetFrequency k p w hw (schwartzWordTuple k φ) =
      frequencyCoordinates (2 * (p : ℝ))
        ((orderedSchwartzDerivative w φ).postcompCLM Complex.ofRealCLM) := by
  induction p generalizing w with
  | zero =>
    simp only [finiteJetFrequency, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, schwartzWordTuple, wordIndex_word]
    change 𝓕 (coordinateComplexification ((orderedSchwartzDerivative w φ).toLp 2 volume)) = _
    rw [coordinateComplexification_schwartz, SchwartzMap.toLp_fourier_eq]
    simp only [Nat.cast_zero, mul_zero, frequencyCoordinates,
      ContinuousLinearMap.comp_apply, SchwartzMap.toLpCLM_apply, weightedFourier_zero]
  | succ p ih =>
    simp only [finiteJetFrequency, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
    rw [ih w (by omega), Nat.cast_add_one, mul_add, mul_one, frequencyCoordinates_add_two]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    rw [ih (i :: i :: w) (by simp only [List.length_cons]; omega)]
    congr 1
    simp only [orderedSchwartzDerivative, coordinateSecond, schwartz_lineDeriv_complexification]

def finiteJetContinuous (k p : ℕ) (w : List (Fin n)) (hw : 2 * p + w.length ≤ k)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) :
    (WordIndex (Fin n) k → ScalarL2 n) →L[ℝ] E →ᵇ ℝ :=
  (realSobolevRealization hp).comp (finiteJetFrequency k p w hw)

theorem finiteJetContinuous_schwartz (k p : ℕ) (w : List (Fin n))
    (hw : 2 * p + w.length ≤ k) (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) (φ : 𝓢(E, ℝ)) :
    finiteJetContinuous k p w hw hp (schwartzWordTuple k φ) =
      (orderedSchwartzDerivative w φ).toBoundedContinuousFunction := by
  ext x
  change realSobolevRealization hp (finiteJetFrequency k p w hw (schwartzWordTuple k φ)) x = _
  rw [finiteJetFrequency_schwartz]
  exact congrFun (realSobolevRealization_frequencyCoordinates hp
    (orderedSchwartzDerivative w φ)) x

theorem finiteJetContinuous_tendsto (q : List (Fin n) → ScalarL2 n) (k p : ℕ)
    (w : List (Fin n)) (hw : 2 * p + w.length ≤ k)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) (S : ℕ → 𝓢(E, ℝ))
    (hS : ∀ v : List (Fin n), v.length ≤ k →
      Tendsto (fun j => (orderedSchwartzDerivative v (S j)).toLp 2 volume) atTop (𝓝 (q v))) :
    Tendsto (fun j => (orderedSchwartzDerivative w (S j)).toBoundedContinuousFunction)
      atTop (𝓝 (finiteJetContinuous k p w hw hp (fun v => q (List.ofFn v.2)))) := by
  have ht : Tendsto (fun j => schwartzWordTuple k (S j)) atTop
      (𝓝 (fun v : WordIndex (Fin n) k => q (List.ofFn v.2))) := by
    apply tendsto_pi_nhds.mpr
    intro v
    exact hS (List.ofFn v.2)
      (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ v.1.isLt)
  simpa only [Function.comp_def, finiteJetContinuous_schwartz] using
    ((finiteJetContinuous k p w hw hp).continuous.tendsto _).comp ht

theorem finiteJetContinuous_ae_eq (q : List (Fin n) → ScalarL2 n) (k p : ℕ)
    (w : List (Fin n)) (hw : 2 * p + w.length ≤ k)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) (hq : IsWeakSchwartzJet q k)
    {K : Set E} (hK : IsCompact K) (hqK : ∀ᵐ y ∂volume, y ∉ K → q [] y = 0) :
    finiteJetContinuous k p w hw hp (fun v => q (List.ofFn v.2)) =ᵐ[volume] q w := by
  have hwk : w.length ≤ k := by omega
  obtain ⟨S, _, hS⟩ := exists_schwartz_approximation_of_finite_weak_jets q k hK hqK
    (fun v hv i φ => by
      simpa only [inner_schwartz, SchwartzMap.lineDerivOp_apply_eq_fderiv]
        using hq v hv i φ) (by norm_num : (0 : ℝ) < 1)
  have hc := finiteJetContinuous_tendsto q k p w hw hp S hS
  obtain ⟨b, hb, hae⟩ := (tendstoInMeasure_of_tendsto_Lp (hS w hwk)).exists_seq_tendsto_ae
  filter_upwards [hae, ae_all_iff.mpr
    (fun j : ℕ => (orderedSchwartzDerivative w (S (b j))).coeFn_toLp 2 volume)] with x hx hpoint
  have hd := ((BoundedContinuousFunction.evalCLM ℝ x).continuous.tendsto _).comp
    (hc.comp hb.tendsto_atTop)
  have hs : Tendsto (fun j => orderedSchwartzDerivative w (S (b j)) x) atTop (𝓝 (q w x)) := by
    simpa only [hpoint] using hx
  exact tendsto_nhds_unique hd hs

theorem finiteJetContinuous_zero_off (q : List (Fin n) → ScalarL2 n) (k p : ℕ)
    (w : List (Fin n)) (hw : 2 * p + w.length ≤ k)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) (hq : IsWeakSchwartzJet q k)
    {K : Set E} (hK : IsCompact K) (hqK : ∀ᵐ y ∂volume, y ∉ K → q [] y = 0)
    {x : E} (hx : x ∉ K) :
    finiteJetContinuous k p w hw hp (fun v => q (List.ofFn v.2)) x = 0 := by
  obtain ⟨r, hr, hKr⟩ := hK.exists_cthickening_subset_open isClosed_singleton.isOpen_compl
    (show K ⊆ ({x} : Set E)ᶜ by intro y hy hxy; exact hx (hxy ▸ hy))
  have hxr : x ∉ Metric.cthickening r K := by
    intro h
    exact hKr h rfl
  obtain ⟨S, hsupport, hS⟩ := exists_schwartz_approximation_of_finite_weak_jets q k hK hqK
    (fun v hv i φ => by
      simpa only [inner_schwartz, SchwartzMap.lineDerivOp_apply_eq_fderiv]
        using hq v hv i φ) hr
  have hzero (j : ℕ) : orderedSchwartzDerivative w (S j) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hxr
      ((hsupport j).2 (tsupport_orderedSchwartzDerivative_subset w (S j) h)))
  have hlim : Tendsto (fun j => orderedSchwartzDerivative w (S j) x) atTop
      (𝓝 (finiteJetContinuous k p w hw hp (fun v => q (List.ofFn v.2)) x)) :=
    ((BoundedContinuousFunction.evalCLM ℝ x).continuous.tendsto _).comp
      (finiteJetContinuous_tendsto q k p w hw hp S hS)
  exact tendsto_nhds_unique hlim (by simpa only [hzero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))

def localizedCoordinateTuple (a : L.patches) (ab : d.ProbeIndex) (k s : ℕ) (hs : s ≤ k) :
    SpectralHeatNative.State d.SymmetricIndex →L[ℝ] (WordIndex (Fin n) s → ScalarL2 n) :=
  ContinuousLinearMap.pi (fun w => localizedScaleDerivative d L a ab k (List.ofFn w.2)
    ((show (List.ofFn w.2).length ≤ s by
      simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt).trans hs))

theorem localizedCoordinateTuple_scaleDecode (a : L.patches) (ab : d.ProbeIndex)
    (k l s : ℕ) (hs : s ≤ k) (x : SpectralHeatNative.State d.SymmetricIndex) :
    localizedCoordinateTuple d L a ab (k + l) s (by omega) x =
      localizedCoordinateTuple d L a ab k s hs
        (SpectralHeatNative.scaleDecode d.symmetricParameters l x) := by
  funext w
  exact localizedScaleDerivative_scaleDecode d L a ab k l (List.ofFn w.2)
    ((show (List.ofFn w.2).length ≤ s by
      simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt).trans hs) x

theorem localizedCoordinateTuple_smoothTensorCoordinates (a : L.patches) (ab : d.ProbeIndex)
    (k s : ℕ) (hs : s ≤ k) (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v v' : TangentSpace (𝓡 n) x), h x v v' = h x v' v) :
    localizedCoordinateTuple d L a ab k s hs (d.smoothTensorCoordinates k h hsymm) =
      schwartzWordTuple s (d.localizedSchwartz L a ab h) := by
  funext w
  exact localizedScaleDerivative_smoothTensorCoordinates d L a ab k (List.ofFn w.2)
    ((show (List.ofFn w.2).length ≤ s by
      simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt).trans hs) h hsymm

def nativeCoordinateSupport (a : L.patches) : Set E :=
  L.chart a '' tsupport (L.weight a)

theorem nativeCoordinateSupport_isCompact (a : L.patches) :
    IsCompact (nativeCoordinateSupport d L a) :=
  (L.weight_compactSupport a).image_of_continuousOn
    ((L.chart a).continuousOn.mono (L.weight_support_source a))

theorem localizedScaleValue_ae_support (a : L.patches) (ab : d.ProbeIndex)
    (k : ℕ) (z : SpectralHeatNative.State d.SymmetricIndex) :
    ∀ᵐ x ∂volume, x ∉ nativeCoordinateSupport d L a → localizedScaleValue d L a ab k z x = 0 := by
  filter_upwards [L.localizationL2_coe a (d.valueCoefficient ab (d.symmetricScaleValue k z))]
    with x hx hnot
  change L.localizationL2 a (d.valueCoefficient ab (d.symmetricScaleValue k z)) x = 0
  rw [hx]
  have hz : L.scalarCutoff a x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    apply hnot
    exact tsupport_chartScalar_subset a.val.1.val (L.weight_compactSupport a)
      (L.weight_support_source a) (L.weight_zero_off_support a) hs
  rw [hz, zero_mul]

def localizedWordContinuous (a : L.patches) (ab : d.ProbeIndex)
    (k s p : ℕ) (hs : 2 * p + s ≤ k) (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (w : List (Fin n)) (hw : w.length ≤ s) :
    SpectralHeatNative.State d.SymmetricIndex →L[ℝ] E →ᵇ ℝ :=
  (finiteJetContinuous (2 * p + s) p w (by omega) hp).comp
    (localizedCoordinateTuple d L a ab k (2 * p + s) hs)

theorem localizedWordContinuous_scaleDecode (a : L.patches) (ab : d.ProbeIndex)
    (k l s p : ℕ) (hs : 2 * p + s ≤ k) (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (w : List (Fin n)) (hw : w.length ≤ s) (z : SpectralHeatNative.State d.SymmetricIndex) :
    localizedWordContinuous d L a ab (k + l) s p (by omega) hp w hw z =
      localizedWordContinuous d L a ab k s p hs hp w hw
        (SpectralHeatNative.scaleDecode d.symmetricParameters l z) := by
  simp only [localizedWordContinuous, ContinuousLinearMap.comp_apply]
  rw [localizedCoordinateTuple_scaleDecode d L a ab k l (2 * p + s) hs z]

theorem localizedWordContinuous_ae_eq (a : L.patches) (ab : d.ProbeIndex)
    (k s p : ℕ) (hs : 2 * p + s ≤ k) (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (w : List (Fin n)) (hw : w.length ≤ s) (z : SpectralHeatNative.State d.SymmetricIndex) :
    localizedWordContinuous d L a ab k s p hs hp w hw z =ᵐ[volume]
      localizedScaleDerivative d L a ab k w (by omega) z := by
  obtain ⟨q, hq0, hq⟩ := exists_symmetricScale_localized_weakJet d k L a ab z
  have ht : localizedCoordinateTuple d L a ab k (2 * p + s) hs z =
      fun v => q (List.ofFn v.2) := by
    funext v
    exact localizedScaleDerivative_eq_jet d L a ab k (List.ofFn v.2) _ z q hq0 hq
  have hsupport : ∀ᵐ x ∂volume, x ∉ nativeCoordinateSupport d L a → q [] x = 0 := by
    rw [hq0]
    exact localizedScaleValue_ae_support d L a ab k z
  change finiteJetContinuous (2 * p + s) p w _ hp
    (localizedCoordinateTuple d L a ab k (2 * p + s) hs z) =ᵐ[volume] _
  rw [ht, localizedScaleDerivative_eq_jet d L a ab k w (by omega) z q hq0 hq]
  exact finiteJetContinuous_ae_eq q (2 * p + s) p w (by omega) hp (hq.mono hs)
    (nativeCoordinateSupport_isCompact d L a) hsupport

theorem localizedWordContinuous_zero_off (a : L.patches) (ab : d.ProbeIndex)
    (k s p : ℕ) (hs : 2 * p + s ≤ k) (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (w : List (Fin n)) (hw : w.length ≤ s) (z : SpectralHeatNative.State d.SymmetricIndex)
    {x : E} (hx : x ∉ nativeCoordinateSupport d L a) :
    localizedWordContinuous d L a ab k s p hs hp w hw z x = 0 := by
  obtain ⟨q, hq0, hq⟩ := exists_symmetricScale_localized_weakJet d k L a ab z
  have ht : localizedCoordinateTuple d L a ab k (2 * p + s) hs z =
      fun v => q (List.ofFn v.2) := by
    funext v
    exact localizedScaleDerivative_eq_jet d L a ab k (List.ofFn v.2) _ z q hq0 hq
  have hsupport : ∀ᵐ y ∂volume, y ∉ nativeCoordinateSupport d L a → q [] y = 0 := by
    rw [hq0]
    exact localizedScaleValue_ae_support d L a ab k z
  change finiteJetContinuous (2 * p + s) p w _ hp
    (localizedCoordinateTuple d L a ab k (2 * p + s) hs z) x = 0
  rw [ht]
  exact finiteJetContinuous_zero_off q (2 * p + s) p w (by omega) hp (hq.mono hs)
    (nativeCoordinateSupport_isCompact d L a) hsupport hx

def cutoffChartPullback (a : L.patches) : (E →ᵇ ℝ) →L[ℝ] C(M, ℝ) := by
  let C := nativeCutoffs d L a
  let P : (E →ᵇ ℝ) →ₗ[ℝ] C(M, ℝ) := {
    toFun := fun f => ⟨fun x => C.eta x * f (L.chart a x), by
      apply continuous_iff_continuousAt.mpr
      intro x
      by_cases hx : x ∈ tsupport C.eta
      · exact C.eta_smooth.continuous.continuousAt.mul
          (f.continuous.continuousAt.comp
            ((L.chart a).continuousOn.continuousAt
              ((L.chart a).open_source.mem_nhds (C.eta_support hx))))
      · have heq : (fun y => C.eta y * f (L.chart a y)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
          rw [hy, Pi.zero_apply, zero_mul]
        exact continuousAt_const.congr_of_eventuallyEq heq⟩
    map_add' := by intro f g; ext x; exact mul_add _ _ _
    map_smul' := by
      intro c f
      ext x
      change C.eta x * (c * f (L.chart a x)) = c * (C.eta x * f (L.chart a x))
      ring }
  exact P.mkContinuous 1 (fun f => by
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro x
    change ‖C.eta x * f (L.chart a x)‖ ≤ ‖f‖
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (C.eta_bounds x).1]
    exact (mul_le_mul (C.eta_bounds x).2 (f.norm_coe_le_norm (L.chart a x))
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

@[simp] theorem cutoffChartPullback_apply (a : L.patches) (f : E →ᵇ ℝ) (x : M) :
    cutoffChartPullback d L a f x = (nativeCutoffs d L a).eta x * f (L.chart a x) := rfl

theorem cutoffChartPullback_localizedWord_ae_eq (a : L.patches) (ab : d.ProbeIndex)
    (k s p : ℕ) (hs : 2 * p + s ≤ k) (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (w : List (Fin n)) (hw : w.length ≤ s) (z : SpectralHeatNative.State d.SymmetricIndex) :
    L.reconstructionL2 a (localizedScaleDerivative d L a ab k w (by omega) z) =ᵐ[d.charts.measure]
      cutoffChartPullback d L a (localizedWordContinuous d L a ab k s p hs hp w hw z) := by
  let f := localizedWordContinuous d L a ab k s p hs hp w hw z
  have hae : (f : E → ℝ) =ᵐ[volume] localizedScaleDerivative d L a ab k w (by omega) z :=
    localizedWordContinuous_ae_eq d L a ab k s p hs hp w hw z
  have hf : MemLp (f : E → ℝ) 2 volume :=
    (Lp.memLp (localizedScaleDerivative d L a ab k w (by omega) z)).ae_eq hae.symm
  have heq : hf.toLp f = localizedScaleDerivative d L a ab k w (by omega) z :=
    Lp.ext (hf.coeFn_toLp.trans hae)
  rw [← heq]
  apply (ChartPushforwardLpNative.chartExtensionL2_toLp_coe (L.chart a)
    (isClosed_tsupport (L.weight a)).measurableSet (L.weight_support_source a)
    (L.reconstructionConstant_ne_top a) (L.reconstructionMeasureBound a) hf).trans
  apply Eventually.of_forall
  intro x
  rw [cutoffChartPullback_apply]
  by_cases hx : x ∈ tsupport (L.weight a)
  · rw [indicator_of_mem hx, ((nativeCutoffs d L a).eta_one x hx).eq_of_nhds,
      Pi.one_apply, one_mul]
  · rw [indicator_of_notMem hx]
    by_cases hxU : x ∈ (L.chart a).source
    · have hxcoord : L.chart a x ∉ nativeCoordinateSupport d L a := by
        rintro ⟨y, hy, hexy⟩
        have hyx : y = x :=
          (L.chart a).injOn (L.weight_support_source a hy) hxU hexy
        exact hx (hyx ▸ hy)
      have hz := localizedWordContinuous_zero_off d L a ab k s p hs hp w hw z hxcoord
      change 0 = (nativeCutoffs d L a).eta x * f (L.chart a x)
      rw [hz, mul_zero]
    · rw [show (nativeCutoffs d L a).eta x = 0 from
        image_eq_zero_of_notMem_tsupport (fun h => hxU ((nativeCutoffs d L a).eta_support h)),
        zero_mul]

def reconstructedCoordinateTupleContinuous (a : L.patches) (ab : d.ProbeIndex)
    (k s p : ℕ) (hs : 2 * p + s ≤ k) (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) :
    SpectralHeatNative.State d.SymmetricIndex →L[ℝ] (WordIndex (Fin n) s → C(M, ℝ)) :=
  ContinuousLinearMap.pi (fun w => (cutoffChartPullback d L a).comp
    (localizedWordContinuous d L a ab k s p hs hp (List.ofFn w.2)
      (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt)))

theorem reconstructedCoordinateTupleContinuous_scaleDecode (a : L.patches) (ab : d.ProbeIndex)
    (k l s p : ℕ) (hs : 2 * p + s ≤ k) (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (z : SpectralHeatNative.State d.SymmetricIndex) :
    reconstructedCoordinateTupleContinuous d L a ab (k + l) s p (by omega) hp z =
      reconstructedCoordinateTupleContinuous d L a ab k s p hs hp
        (SpectralHeatNative.scaleDecode d.symmetricParameters l z) := by
  funext w
  exact congrArg (cutoffChartPullback d L a)
    (localizedWordContinuous_scaleDecode d L a ab k l s p hs hp (List.ofFn w.2)
      (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt) z)

theorem reconstructedCoordinateTupleContinuous_ae_eq (a : L.patches) (ab : d.ProbeIndex)
    (k s p : ℕ) (hs : 2 * p + s ≤ k) (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (z : SpectralHeatNative.State d.SymmetricIndex) (w : WordIndex (Fin n) s) :
    reconstructedCoordinateTuple d L a ab k s (by omega) z w =ᵐ[d.charts.measure]
      reconstructedCoordinateTupleContinuous d L a ab k s p hs hp z w :=
  cutoffChartPullback_localizedWord_ae_eq d L a ab k s p hs hp (List.ofFn w.2)
    (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt) z

theorem termsL2_ae_eq_termsContinuous {ι : Type*} (μ : Measure M) [IsFiniteMeasure μ]
    {k : ℕ} (terms : List (DirectionalTerm (n := n) (M := M) (iota := ι)))
    (h : ∀ t ∈ terms, t.word.length ≤ k)
    (Q : WordIndex ι k → Lp ℝ 2 μ) (R : WordIndex ι k → C(M, ℝ))
    (hQ : ∀ w, Q w =ᵐ[μ] R w) :
    termsL2 μ terms h Q =ᵐ[μ] termsContinuous terms h R := by
  induction terms with
  | nil => exact Lp.coeFn_zero ℝ 2 μ
  | cons t terms ih =>
    let w := wordIndex t.word (h t List.mem_cons_self)
    let rest := termsL2 μ terms (fun s hs => h s (List.mem_cons_of_mem t hs)) Q
    have hrest : rest =ᵐ[μ] termsContinuous terms
        (fun s hs => h s (List.mem_cons_of_mem t hs)) R := ih _
    filter_upwards [coefficientL2_coe μ t.coefficient t.smooth (Q w), hQ w, hrest,
      Lp.coeFn_add (coefficientL2 μ t.coefficient t.smooth (Q w)) rest]
      with x hc hqx hr hadd
    change (coefficientL2 μ t.coefficient t.smooth (Q w) + rest) x = _
    rw [hadd, Pi.add_apply, hc, hqx, hr]
    rfl

def nativeWordContinuous (ab : d.ProbeIndex) (k p : ℕ) (w : List (Fin d.fieldCount))
    (hw : 2 * p + w.length ≤ k) (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) :
    SpectralHeatNative.State d.SymmetricIndex →L[ℝ] C(M, ℝ) :=
  ∑ a : L.patches,
    (termsContinuous (nativeWordTerms d L a w) (nativeWordTerms_order d L a w)).comp
      (reconstructedCoordinateTupleContinuous d L a ab k w.length p hw hp)

theorem nativeWordContinuous_scaleDecode (ab : d.ProbeIndex) (k l p : ℕ)
    (w : List (Fin d.fieldCount)) (hw : 2 * p + w.length ≤ k)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) (z : SpectralHeatNative.State d.SymmetricIndex) :
    nativeWordContinuous d L ab (k + l) p w (by omega) hp z =
      nativeWordContinuous d L ab k p w hw hp
        (SpectralHeatNative.scaleDecode d.symmetricParameters l z) := by
  simp only [nativeWordContinuous, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [reconstructedCoordinateTupleContinuous_scaleDecode d L a ab k l w.length p hw hp z]

theorem nativeWordContinuous_ae_eq (ab : d.ProbeIndex) (k p : ℕ)
    (w : List (Fin d.fieldCount)) (hw : 2 * p + w.length ≤ k)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) (z : SpectralHeatNative.State d.SymmetricIndex) :
    nativeWordL2 d L ab k w (by omega) z =ᵐ[d.charts.measure]
      nativeWordContinuous d L ab k p w hw hp z := by
  let Q (a : L.patches) := reconstructedCoordinateTuple d L a ab k w.length (by omega) z
  let R (a : L.patches) := reconstructedCoordinateTupleContinuous d L a ab k w.length p hw hp z
  let q (a : L.patches) :=
    termsL2 d.charts.measure (nativeWordTerms d L a w) (nativeWordTerms_order d L a w) (Q a)
  have hq (a : L.patches) : q a =ᵐ[d.charts.measure]
      termsContinuous (nativeWordTerms d L a w) (nativeWordTerms_order d L a w) (R a) :=
    termsL2_ae_eq_termsContinuous d.charts.measure (nativeWordTerms d L a w)
      (nativeWordTerms_order d L a w) (Q a) (R a)
      (reconstructedCoordinateTupleContinuous_ae_eq d L a ab k w.length p hw hp z)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ q, ae_all_iff.mpr hq] with x hsum hqx
  simp only [nativeWordL2, nativeWordContinuous, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousMap.sum_apply]
  change (∑ a : L.patches, q a) x = _
  rw [hsum]
  exact Finset.sum_congr rfl (fun a _ => hqx a)

theorem nativeWordContinuous_smoothTensorCoordinates (ab : d.ProbeIndex) (k p : ℕ)
    (w : List (Fin d.fieldCount)) (hw : 2 * p + w.length ≤ k)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v v' : TangentSpace (𝓡 n) x), h x v v' = h x v' v) (x : M) :
    nativeWordContinuous d L ab k p w hw hp (d.smoothTensorCoordinates k h hsymm) x =
      directionalWord d.fields w (scalarProbe d.fields h ab) x := by
  apply congrFun (MeasureTheory.Measure.eq_of_ae_eq
    ((nativeWordContinuous_ae_eq d L ab k p w hw hp (d.smoothTensorCoordinates k h hsymm)).symm.trans
      (nativeWordL2_smoothTensorCoordinates d L ab k w (by omega) h hsymm))
    (nativeWordContinuous d L ab k p w hw hp (d.smoothTensorCoordinates k h hsymm)).continuous
    (directionalWord_contMDiff d.fields w (scalarProbe_contMDiff d.fields h ab)).continuous) x

def nativeProbeTupleContinuous (k s p : ℕ) (hs : 2 * p + s ≤ k)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) :
    SpectralHeatNative.State d.SymmetricIndex →L[ℝ]
      (d.ProbeIndex → WordIndex (Fin d.fieldCount) s → C(M, ℝ)) :=
  ContinuousLinearMap.pi (fun ab => ContinuousLinearMap.pi (fun w =>
    nativeWordContinuous d L ab k p (List.ofFn w.2)
      (by have h := Nat.le_of_lt_succ w.1.isLt; simp only [List.length_ofFn]; omega) hp))

theorem nativeProbeTupleContinuous_scaleDecode (k l s p : ℕ) (hs : 2 * p + s ≤ k)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) (z : SpectralHeatNative.State d.SymmetricIndex) :
    nativeProbeTupleContinuous d L (k + l) s p (by omega) hp z =
      nativeProbeTupleContinuous d L k s p hs hp
        (SpectralHeatNative.scaleDecode d.symmetricParameters l z) := by
  funext ab w
  exact nativeWordContinuous_scaleDecode d L ab k l p (List.ofFn w.2)
    (by have h := Nat.le_of_lt_succ w.1.isLt; simp only [List.length_ofFn]; omega) hp z

theorem nativeProbeTupleContinuous_ae_eq (k s p : ℕ) (hs : 2 * p + s ≤ k)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) (z : SpectralHeatNative.State d.SymmetricIndex)
    (ab : d.ProbeIndex) (w : WordIndex (Fin d.fieldCount) s) :
    nativeProbeTupleL2 d L k s (by omega) z ab w =ᵐ[d.charts.measure]
      nativeProbeTupleContinuous d L k s p hs hp z ab w :=
  nativeWordContinuous_ae_eq d L ab k p (List.ofFn w.2)
    (by have h := Nat.le_of_lt_succ w.1.isLt; simp only [List.length_ofFn]; omega) hp z

theorem nativeProbeTupleContinuous_smoothTensorCoordinates (k s p : ℕ) (hs : 2 * p + s ≤ k)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v v' : TangentSpace (𝓡 n) x), h x v v' = h x v' v)
    (ab : d.ProbeIndex) (w : List (Fin d.fieldCount)) (hw : w.length ≤ s) (x : M) :
    nativeProbeTupleContinuous d L k s p hs hp (d.smoothTensorCoordinates k h hsymm) ab
      (wordIndex w hw) x = directionalWord d.fields w (scalarProbe d.fields h ab) x := by
  change nativeWordContinuous d L ab k p (List.ofFn (wordIndex w hw).2) _ hp
    (d.smoothTensorCoordinates k h hsymm) x = _
  simp only [wordIndex_word]
  exact nativeWordContinuous_smoothTensorCoordinates d L ab k p w (by omega) hp h hsymm x

end PoincareConjecture.DeTurckMetricDomainNative

end
