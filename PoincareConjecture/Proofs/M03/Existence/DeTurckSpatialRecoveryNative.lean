import PoincareConjecture.Proofs.M03.Existence.DeTurckStatePullbackContinuityNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckSpatialParameterNative







set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators ENNReal

namespace PoincareConjecture.DeTurckSpatialRecoveryNative

open TensorProbeNative TensorHilbertNative ParsevalTensorNative ChartMeasureNative
  DeTurckJetCoordinatesNative DeTurckMetricDomainNative DeTurckStateApproximationNative
  DeTurckStatePullbackNative DeTurckStatePullbackContinuityNative
  DeTurckParameterBackgroundNative DeTurckSpatialParameterNative SpectralHeatNative

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {g0 : RiemannianMetric n M} (d : Data g0)
  (L : FiniteChartLocalizationData d.charts)

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓡 n

variable (r p : ℕ) (hpr : p ≤ r) (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))

def zeroProbe (ab : d.ProbeIndex) : State d.SymmetricIndex →L[ℝ] C(M, ℝ) :=
  nativeWordContinuous d L ab (2 * r) p [] (by simp only [List.length_nil]; omega) hp

def probeEvaluation (ab : d.ProbeIndex) (x : M) : State d.SymmetricIndex →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ x).comp (zeroProbe d L r p hpr hp ab)

theorem probeEvaluation_smoothTensorCoordinates
    (h : SmoothTensor (n := n) (M := M))
    (hs : ∀ (x : M) (v w : TangentSpace I x), h x v w = h x w v)
    (ab : d.ProbeIndex) (x : M) :
    probeEvaluation d L r p hpr hp ab x (d.smoothTensorCoordinates (2 * r) h hs) =
      scalarProbe d.fields h ab x :=
  nativeWordContinuous_smoothTensorCoordinates d L ab (2 * r) p []
    (by simp only [List.length_nil]; omega) hp h hs x

def stateCoefficients (z : State d.SymmetricIndex) (x : M) : Coefficients (Fin d.fieldCount) :=
  WithLp.toLp 2 (fun ab : d.ProbeIndex => probeEvaluation d L r p hpr hp ab x z)

def stateTensor (z : State d.SymmetricIndex) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  nativeDecode g0 d.fields x (stateCoefficients d L r p hpr hp z x)

def tensorEvaluation (x : M) (v w : TangentSpace I x) : State d.SymmetricIndex →L[ℝ] ℝ :=
  ∑ ab : d.ProbeIndex,
    (g0.inner x (d.fields ab.1 x) v * g0.inner x (d.fields ab.2 x) w) •
      probeEvaluation d L r p hpr hp ab x

theorem tensorEvaluation_apply (z : State d.SymmetricIndex) (x : M)
    (v w : TangentSpace I x) :
    tensorEvaluation d L r p hpr hp x v w z = stateTensor d L r p hpr hp z x v w := by
  classical
  rw [stateTensor, nativeDecode_apply]
  simp only [tensorEvaluation, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro ab _
  change _ = probeEvaluation d L r p hpr hp ab x z *
    g0.inner x (d.fields ab.1 x) v * g0.inner x (d.fields ab.2 x) w
  ring

theorem stateTensor_smoothTensorCoordinates
    (h : SmoothTensor (n := n) (M := M))
    (hs : ∀ (x : M) (v w : TangentSpace I x), h x v w = h x w v) (x : M) :
    stateTensor d L r p hpr hp (d.smoothTensorCoordinates (2 * r) h hs) x = h x := by
  have heq : stateCoefficients d L r p hpr hp
      (d.smoothTensorCoordinates (2 * r) h hs) x = probes d.fields h x := by
    ext ab
    exact probeEvaluation_smoothTensorCoordinates d L r p hpr hp h hs ab x
  rw [stateTensor, heq]
  exact nativeDecode_probes g0 d.fields d.parseval h x

theorem tensorEvaluation_smoothTensorCoordinates
    (h : SmoothTensor (n := n) (M := M))
    (hs : ∀ (x : M) (v w : TangentSpace I x), h x v w = h x w v)
    (x : M) (v w : TangentSpace I x) :
    tensorEvaluation d L r p hpr hp x v w (d.smoothTensorCoordinates (2 * r) h hs) = h x v w := by
  rw [tensorEvaluation_apply, stateTensor_smoothTensorCoordinates]


theorem stateTensor_probe (z : State d.SymmetricIndex) (ab : d.ProbeIndex) (x : M) :
    stateTensor d L r p hpr hp z x (d.fields ab.1 x) (d.fields ab.2 x) =
      probeEvaluation d L r p hpr hp ab x z := by
  obtain ⟨h, hs, hlim⟩ := exists_smooth_symmetric_approximation d L r z
  have hleft := ((tensorEvaluation d L r p hpr hp x (d.fields ab.1 x)
    (d.fields ab.2 x)).continuous.tendsto z).comp hlim
  have hright := ((probeEvaluation d L r p hpr hp ab x).continuous.tendsto z).comp hlim
  have hid (j : ℕ) : tensorEvaluation d L r p hpr hp x (d.fields ab.1 x) (d.fields ab.2 x)
      (d.smoothTensorCoordinates (2 * r) (h j) (hs j)) =
      probeEvaluation d L r p hpr hp ab x (d.smoothTensorCoordinates (2 * r) (h j) (hs j)) := by
    rw [tensorEvaluation_smoothTensorCoordinates, probeEvaluation_smoothTensorCoordinates]
    rfl
  rw [← tensorEvaluation_apply]
  exact tendsto_nhds_unique (by simpa only [Function.comp_def, hid] using hleft) hright

theorem stateTensor_symmetric (z : State d.SymmetricIndex) (x : M)
    (v w : TangentSpace I x) :
    stateTensor d L r p hpr hp z x v w = stateTensor d L r p hpr hp z x w v := by
  obtain ⟨h, hs, hlim⟩ := exists_smooth_symmetric_approximation d L r z
  have hleft := ((tensorEvaluation d L r p hpr hp x v w).continuous.tendsto z).comp hlim
  have hright := ((tensorEvaluation d L r p hpr hp x w v).continuous.tendsto z).comp hlim
  have hid (j : ℕ) : tensorEvaluation d L r p hpr hp x v w
      (d.smoothTensorCoordinates (2 * r) (h j) (hs j)) =
      tensorEvaluation d L r p hpr hp x w v
        (d.smoothTensorCoordinates (2 * r) (h j) (hs j)) := by
    rw [tensorEvaluation_smoothTensorCoordinates, tensorEvaluation_smoothTensorCoordinates]
    exact hs j x v w
  rw [← tensorEvaluation_apply, ← tensorEvaluation_apply]
  exact tendsto_nhds_unique (by simpa only [Function.comp_def, hid] using hleft) hright


theorem stateTensor_evenPullback (Phi : Diffeomorph I I M M ∞) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hdom : d.charts.measure.map Phi ≤ C • d.charts.measure)
    (z : State d.SymmetricIndex) (x : M) (v w : TangentSpace I x) :
    stateTensor d L r p hpr hp (evenPullback d Phi hC hdom L r z) x v w =
      stateTensor d L r p hpr hp z (Phi x)
        (mfderiv I I Phi x v) (mfderiv I I Phi x w) := by
  obtain ⟨h, hs, hlim⟩ := exists_smooth_symmetric_approximation d L r z
  have hleft := ((tensorEvaluation d L r p hpr hp x v w).continuous.tendsto _).comp
    (((evenPullback d Phi hC hdom L r).continuous.tendsto z).comp hlim)
  have hright := ((tensorEvaluation d L r p hpr hp (Phi x)
    (mfderiv I I Phi x v) (mfderiv I I Phi x w)).continuous.tendsto z).comp hlim
  have hid (j : ℕ) : tensorEvaluation d L r p hpr hp x v w
      (evenPullback d Phi hC hdom L r (d.smoothTensorCoordinates (2 * r) (h j) (hs j))) =
      tensorEvaluation d L r p hpr hp (Phi x) (mfderiv I I Phi x v) (mfderiv I I Phi x w)
        (d.smoothTensorCoordinates (2 * r) (h j) (hs j)) := by
    rw [evenPullback_smoothTensorCoordinates, tensorEvaluation_smoothTensorCoordinates,
      tensorEvaluation_smoothTensorCoordinates, smoothPullback_apply]
  rw [← tensorEvaluation_apply, ← tensorEvaluation_apply]
  exact tendsto_nhds_unique (by simpa only [Function.comp_def, hid] using hleft) hright


theorem probeEvaluation_inverse_formula (Phi : Diffeomorph I I M M ∞) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hdom : d.charts.measure.map Phi ≤ C • d.charts.measure)
    (z : State d.SymmetricIndex) (ab : d.ProbeIndex) (x : M) :
    probeEvaluation d L r p hpr hp ab (Phi x) z =
      ∑ cd : d.ProbeIndex,
        (transportCoefficient d Phi.symm ab.1 cd.1 x *
          transportCoefficient d Phi.symm ab.2 cd.2 x) *
        probeEvaluation d L r p hpr hp cd x (evenPullback d Phi hC hdom L r z) := by
  classical
  let v := DiffeomorphNative.pullField Phi (d.fields ab.1) x
  let w := DiffeomorphNative.pullField Phi (d.fields ab.2) x
  have hvalue := stateTensor_evenPullback d L r p hpr hp Phi hC hdom z x v w
  dsimp only [v, w] at hvalue
  rw [DiffeomorphNative.mfderiv_pullField, DiffeomorphNative.mfderiv_pullField,
    stateTensor_probe] at hvalue
  rw [← hvalue, stateTensor, nativeDecode_apply]
  apply Finset.sum_congr rfl
  intro cd _
  change probeEvaluation d L r p hpr hp cd x (evenPullback d Phi hC hdom L r z) *
      g0.inner x (d.fields cd.1 x) v * g0.inner x (d.fields cd.2 x) w = _
  simp only [transportCoefficient, transportedField]
  change _ = (g0.inner x (d.fields cd.1 x) v * g0.inner x (d.fields cd.2 x) w) * _
  ring

section Paths

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def probePathEvaluation (ab : d.ProbeIndex) (x : M) :
    C(K, State d.SymmetricIndex) →L[ℝ] C(K, ℝ) :=
  (probeEvaluation d L r p hpr hp ab x).compLeftContinuous ℝ K

def probePath (z : C(K, State d.SymmetricIndex)) (ab : d.ProbeIndex) (x : M) : C(K, ℝ) :=
  probePathEvaluation d L r p hpr hp ab x z

@[simp] theorem probePath_apply (z : C(K, State d.SymmetricIndex))
    (ab : d.ProbeIndex) (x : M) (t : K) :
    probePath d L r p hpr hp z ab x t = zeroProbe d L r p hpr hp ab (z t) x := rfl

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def reconstructedProbePath (Phi : P → Diffeomorph I I M M ∞)
    (orbit : P → C(K, State d.SymmetricIndex)) (ab : d.ProbeIndex) (x : M)
    (a : P) : C(K, ℝ) :=
  ∑ cd : d.ProbeIndex,
    (transportCoefficient d (Phi a).symm ab.1 cd.1 x *
      transportCoefficient d (Phi a).symm ab.2 cd.2 x) •
      probePath d L r p hpr hp (orbit a) cd x

theorem contDiffAt_inverseCoefficient {U : Set P} (hU : IsOpen U) (h0 : 0 ∈ U)
    (Phi : P → Diffeomorph I I M M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ))
    (hInv : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => (Phi q.1).symm q.2) (U ×ˢ univ))
    (i j : Fin d.fieldCount) (x : M) :
    ContDiffAt ℝ ∞ (fun a => transportCoefficient d (Phi a).symm i j x) 0 := by
  have hback : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => ((Phi q.1).symm).symm q.2) (U ×ˢ univ) := by
    exact hPhi
  have h := contMDiffOn_transportCoefficient d (fun a => (Phi a).symm) hInv hback i j
  have hslice := h.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
    (fun a ha => ⟨ha, mem_univ x⟩)
  exact (hslice.contMDiffAt (hU.mem_nhds h0)).contDiffAt

theorem contDiffAt_reconstructedProbePath {U : Set P} (hU : IsOpen U) (h0 : 0 ∈ U)
    (Phi : P → Diffeomorph I I M M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ))
    (hInv : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => (Phi q.1).symm q.2) (U ×ˢ univ))
    (orbit : P → C(K, State d.SymmetricIndex)) (horbit : ContDiffAt ℝ ∞ orbit 0)
    (ab : d.ProbeIndex) (x : M) :
    ContDiffAt ℝ ∞ (reconstructedProbePath d L r p hpr hp Phi orbit ab x) 0 := by
  apply ContDiffAt.sum
  intro cd _
  let A : C(K, State d.SymmetricIndex) →L[ℝ] C(K, ℝ) :=
    probePathEvaluation d L r p hpr hp cd x
  have hpath : ContDiffAt ℝ ∞
      (fun a => probePath d L r p hpr hp (orbit a) cd x) 0 := by
    simpa only [Function.comp_def, A, probePath] using (A.contDiff.contDiffAt.comp 0 horbit)
  exact ((contDiffAt_inverseCoefficient d hU h0 Phi hPhi hInv ab.1 cd.1 x).mul
    (contDiffAt_inverseCoefficient d hU h0 Phi hPhi hInv ab.2 cd.2 x)).smul hpath

theorem reconstructedProbePath_eq {Phi : P → Diffeomorph I I M M ∞}
    {orbit : P → C(K, State d.SymmetricIndex)}
    (z : C(K, State d.SymmetricIndex)) (a : P) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hdom : d.charts.measure.map (Phi a) ≤ C • d.charts.measure)
    (horbit : ∀ t : K, orbit a t = evenPullback d (Phi a) hC hdom L r (z t))
    (ab : d.ProbeIndex) (x : M) :
    reconstructedProbePath d L r p hpr hp Phi orbit ab x a =
      probePath d L r p hpr hp z ab (Phi a x) := by
  classical
  ext t
  simp only [reconstructedProbePath, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul]
  change (∑ cd : d.ProbeIndex, _ * probeEvaluation d L r p hpr hp cd x (orbit a t)) = _
  simp only [horbit t]
  exact (probeEvaluation_inverse_formula d L r p hpr hp (Phi a) hC hdom (z t) ab x).symm


theorem contMDiffAt_probePath_of_orbit (z : C(K, State d.SymmetricIndex)) (x : M)
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (h0 : 0 ∈ U)
    (Phi : (Fin n → ℝ) → Diffeomorph I I M M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, Fin n → ℝ).prod I) I ∞
      (fun q : (Fin n → ℝ) × M => Phi q.1 q.2) (U ×ˢ univ))
    (hInv : ContMDiffOn (𝓘(ℝ, Fin n → ℝ).prod I) I ∞
      (fun q : (Fin n → ℝ) × M => (Phi q.1).symm q.2) (U ×ˢ univ))
    (inv : E → (Fin n → ℝ)) (hinv : ContDiffAt ℝ ∞ inv (extChartAt I x x))
    (hinv0 : inv (extChartAt I x x) = 0)
    (hright : ∀ᶠ y in 𝓝 (extChartAt I x x), Phi (inv y) x = (extChartAt I x).symm y)
    (orbit : (Fin n → ℝ) → C(K, State d.SymmetricIndex))
    (hsmooth : ContDiffAt ℝ ∞ orbit 0)
    {V : Set (Fin n → ℝ)} (hV : V ∈ 𝓝 0) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hdom : ∀ a ∈ V, d.charts.measure.map (Phi a) ≤ C • d.charts.measure)
    (horbit : ∀ a (ha : a ∈ V) (t : K),
      orbit a t = evenPullback d (Phi a) hC (hdom a ha) L r (z t))
    (ab : d.ProbeIndex) :
    ContMDiffAt I 𝓘(ℝ, C(K, ℝ)) ∞ (probePath d L r p hpr hp z ab) x := by
  let Q := reconstructedProbePath d L r p hpr hp Phi orbit ab x
  have hQ : ContDiffAt ℝ ∞ Q (inv (extChartAt I x x)) := by
    rw [hinv0]
    exact contDiffAt_reconstructedProbePath d L r p hpr hp hU h0 Phi hPhi hInv
      orbit hsmooth ab x
  have htend : Tendsto inv (𝓝 (extChartAt I x x)) (𝓝 0) := by
    simpa only [hinv0] using hinv.continuousAt.tendsto
  have heq : (fun y => probePath d L r p hpr hp z ab ((extChartAt I x).symm y)) =ᶠ[
      𝓝 (extChartAt I x x)] (fun y => Q (inv y)) := by
    filter_upwards [hright, htend hV] with y hy hyV
    rw [← hy]
    exact (reconstructedProbePath_eq d L r p hpr hp z (inv y) hC (hdom _ hyV)
      (horbit _ hyV) ab x).symm
  rw [contMDiffAt_iff_source]
  exact ((hQ.comp (extChartAt I x x) hinv).congr_of_eventuallyEq heq).contMDiffAt.contMDiffWithinAt


def recoveredTensor (z : C(K, State d.SymmetricIndex))
    (hspatial : ∀ ab : d.ProbeIndex,
      ContMDiff I 𝓘(ℝ, C(K, ℝ)) ∞ (probePath d L r p hpr hp z ab))
    (t : K) : SmoothTensor (n := n) (M := M) :=
  smoothDecode g0 d.fields (stateCoefficients d L r p hpr hp (z t))
    (fun ab => (ContinuousMap.evalCLM ℝ t).contMDiff.comp (hspatial ab))

@[simp] theorem recoveredTensor_apply (z : C(K, State d.SymmetricIndex))
    (hspatial : ∀ ab : d.ProbeIndex,
      ContMDiff I 𝓘(ℝ, C(K, ℝ)) ∞ (probePath d L r p hpr hp z ab))
    (t : K) (x : M) :
    recoveredTensor d L r p hpr hp z hspatial t x = stateTensor d L r p hpr hp (z t) x := rfl

theorem recoveredTensor_symmetric (z : C(K, State d.SymmetricIndex))
    (hspatial : ∀ ab : d.ProbeIndex,
      ContMDiff I 𝓘(ℝ, C(K, ℝ)) ∞ (probePath d L r p hpr hp z ab))
    (t : K) (x : M) (v w : TangentSpace I x) :
    recoveredTensor d L r p hpr hp z hspatial t x v w =
      recoveredTensor d L r p hpr hp z hspatial t x w v :=
  stateTensor_symmetric d L r p hpr hp (z t) x v w

theorem scalarProbe_recoveredTensor (z : C(K, State d.SymmetricIndex))
    (hspatial : ∀ ab : d.ProbeIndex,
      ContMDiff I 𝓘(ℝ, C(K, ℝ)) ∞ (probePath d L r p hpr hp z ab))
    (t : K) (ab : d.ProbeIndex) (x : M) :
    scalarProbe d.fields (recoveredTensor d L r p hpr hp z hspatial t) ab x =
      probePath d L r p hpr hp z ab x t :=
  stateTensor_probe d L r p hpr hp (z t) ab x

def tensorPairPath (z : C(K, State d.SymmetricIndex))
    (V W : (x : M) → TangentSpace I x) (x : M) : C(K, ℝ) :=
  ∑ ab : d.ProbeIndex,
    (g0.inner x (d.fields ab.1 x) (V x) * g0.inner x (d.fields ab.2 x) (W x)) •
      probePath d L r p hpr hp z ab x

theorem tensorPairPath_apply (z : C(K, State d.SymmetricIndex))
    (V W : (x : M) → TangentSpace I x) (x : M) (t : K) :
    tensorPairPath d L r p hpr hp z V W x t =
      stateTensor d L r p hpr hp (z t) x (V x) (W x) := by
  classical
  rw [tensorPairPath, stateTensor, nativeDecode_apply]
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro ab _
  change (g0.inner x (d.fields ab.1 x) (V x) * g0.inner x (d.fields ab.2 x) (W x)) *
      probeEvaluation d L r p hpr hp ab x (z t) =
      probeEvaluation d L r p hpr hp ab x (z t) *
        g0.inner x (d.fields ab.1 x) (V x) * g0.inner x (d.fields ab.2 x) (W x)
  ring

theorem contMDiffOn_nativePair {S : Set M} (V : (x : M) → TangentSpace I x)
    (hV : ContMDiffOn I ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle I M)) S) (a : Fin d.fieldCount) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => g0.inner x (d.fields a x) (V x)) S := by
  have hpair := ContMDiffOn.clm_bundle_apply₂
    (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I) (E₂ := TangentSpace I) (E₃ := fun _ : M => ℝ)
    (b := id) (ψ := fun x => g0.inner x) g0.contMDiff.contMDiffOn
    (d.fields a).contMDiff.contMDiffOn hV
  intro x hx
  exact (Bundle.contMDiffWithinAt_totalSpace.mp (hpair x hx)).2

theorem contMDiffOn_tensorPairPath (z : C(K, State d.SymmetricIndex))
    (hspatial : ∀ ab : d.ProbeIndex,
      ContMDiff I 𝓘(ℝ, C(K, ℝ)) ∞ (probePath d L r p hpr hp z ab))
    {S : Set M} (V W : (x : M) → TangentSpace I x)
    (hV : ContMDiffOn I ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle I M)) S)
    (hW : ContMDiffOn I ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, W x⟩ : TangentBundle I M)) S) :
    ContMDiffOn I 𝓘(ℝ, C(K, ℝ)) ∞ (tensorPairPath d L r p hpr hp z V W) S := by
  apply contMDiffOn_finsetSum
  intro ab _
  exact ((contMDiffOn_nativePair d V hV ab.1).mul
    (contMDiffOn_nativePair d W hW ab.2)).smul (hspatial ab).contMDiffOn

def chartTensorPath (z : C(K, State d.SymmetricIndex))
    (base : M) (i j : Fin n) (x : M) : C(K, ℝ) :=
  tensorPairPath d L r p hpr hp z (DeTurckNative.chartFrame base i)
    (DeTurckNative.chartFrame base j) x

theorem chartTensorPath_apply (z : C(K, State d.SymmetricIndex))
    (base : M) (i j : Fin n) (x : M) (t : K) :
    chartTensorPath d L r p hpr hp z base i j x t =
      stateTensor d L r p hpr hp (z t) x
        (DeTurckNative.chartFrame base i x) (DeTurckNative.chartFrame base j x) :=
  tensorPairPath_apply d L r p hpr hp z _ _ x t

theorem contMDiffOn_chartTensorPath (z : C(K, State d.SymmetricIndex))
    (hspatial : ∀ ab : d.ProbeIndex,
      ContMDiff I 𝓘(ℝ, C(K, ℝ)) ∞ (probePath d L r p hpr hp z ab))
    (base : M) (i j : Fin n) :
    ContMDiffOn I 𝓘(ℝ, C(K, ℝ)) ∞ (chartTensorPath d L r p hpr hp z base i j)
      (chartAt E base).source :=
  contMDiffOn_tensorPairPath d L r p hpr hp z hspatial _ _
    (DeTurckNative.chartFrame_contMDiffOn base i)
    (DeTurckNative.chartFrame_contMDiffOn base j)


theorem contMDiff_probePath_of_parameter_orbits (z : C(K, State d.SymmetricIndex))
    (horbits : ∀ (U : Set (Fin n → ℝ)), IsOpen U → 0 ∈ U →
      ∀ (Phi : (Fin n → ℝ) → Diffeomorph I I M M ∞),
        Phi 0 = Diffeomorph.refl I M ∞ →
        ContMDiffOn (𝓘(ℝ, Fin n → ℝ).prod I) I ∞
          (fun q : (Fin n → ℝ) × M => Phi q.1 q.2) (U ×ˢ univ) →
        ContMDiffOn (𝓘(ℝ, Fin n → ℝ).prod I) I ∞
          (fun q : (Fin n → ℝ) × M => (Phi q.1).symm q.2) (U ×ˢ univ) →
        ∃ V : Set (Fin n → ℝ), V ∈ 𝓝 0 ∧
          ∃ (C : ℝ≥0∞) (hC : C ≠ ⊤)
            (hdom : ∀ a ∈ V, d.charts.measure.map (Phi a) ≤ C • d.charts.measure)
            (orbit : (Fin n → ℝ) → C(K, State d.SymmetricIndex)),
            ContDiffAt ℝ ∞ orbit 0 ∧
              ∀ a (ha : a ∈ V) (t : K),
                orbit a t = evenPullback d (Phi a) hC (hdom a ha) L r (z t))
    (ab : d.ProbeIndex) :
    ContMDiff I 𝓘(ℝ, C(K, ℝ)) ∞ (probePath d L r p hpr hp z ab) := by
  intro x
  obtain ⟨U, hU, h0, Phi, hPhi0, hPhi, hInv, inv, hinv, hinv0, hright⟩ :=
    exists_coordinate_parameter_inverse (n := n) x
  obtain ⟨V, hV, C, hC, hdom, orbit, hsmooth, horbit⟩ :=
    horbits U hU h0 Phi hPhi0 hPhi hInv
  exact contMDiffAt_probePath_of_orbit d L r p hpr hp z x hU h0 Phi hPhi hInv
    inv hinv hinv0 (hright.mono fun _ hy => hy.2) orbit hsmooth hV hC hdom horbit ab

end Paths

end PoincareConjecture.DeTurckSpatialRecoveryNative

end
