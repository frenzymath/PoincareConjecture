import PoincareConjecture.Proofs.M03.Existence.DeTurckSpatialRecoveryNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckPullbackForcingNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckEndpointCalculusNative








set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.DeTurckIntegralPDENative

open TensorProbeNative TensorHilbertNative ParsevalTensorNative ChartMeasureNative DeTurckNative
  DeTurckJetCoordinatesNative DeTurckCompletedOutputNative
  DeTurckStateApproximationNative DeTurckStatePullbackNative
  DeTurckSpatialRecoveryNative DeTurckResidualNative
  DeTurckParameterForcingNative DeTurckPullbackForcingNative
  SpectralHeatNative QuasilinearDeTurckNative

section NativePathWords

variable {n : ℕ} {M K iota : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [TopologicalSpace K] [CompactSpace K]

def pathDirectional (V : SmoothField (n := n) (M := M))
    (f : M → C(K, ℝ)) (x : M) : C(K, ℝ) :=
  mfderiv (𝓡 n) 𝓘(ℝ, C(K, ℝ)) f x (V x)

theorem pathDirectional_contMDiff (V : SmoothField (n := n) (M := M))
    {f : M → C(K, ℝ)} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, C(K, ℝ)) ∞ f) :
    ContMDiff (𝓡 n) 𝓘(ℝ, C(K, ℝ)) ∞ (pathDirectional V f) := by
  have ht := hf.contMDiff_tangentMap (m := ∞) (by simp)
  exact (contMDiff_snd_tangentBundle_modelSpace C(K, ℝ) 𝓘(ℝ, C(K, ℝ))).comp
    (ht.comp V.contMDiff)

theorem pathDirectional_eval (V : SmoothField (n := n) (M := M))
    {f : M → C(K, ℝ)} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, C(K, ℝ)) ∞ f)
    (t : K) (x : M) :
    pathDirectional V f x t = scalarDirectional V (fun y => f y t) x := by
  let ev : C(K, ℝ) →L[ℝ] ℝ := ContinuousMap.evalCLM ℝ t
  have hd := ev.hasMFDerivAt.comp x ((hf x).mdifferentiableAt (by simp)).hasMFDerivAt
  have hm := hd.mfderiv
  change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun y => f y t) x =
    ev.comp (mfderiv (𝓡 n) 𝓘(ℝ, C(K, ℝ)) f x) at hm
  change _ = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun y => f y t) x (V x)
  rw [hm]
  rfl

def pathWord (F : iota → SmoothField (n := n) (M := M)) :
    List iota → (M → C(K, ℝ)) → M → C(K, ℝ)
  | [], f => f
  | i :: w, f => pathDirectional (F i) (pathWord F w f)

theorem pathWord_contMDiff (F : iota → SmoothField (n := n) (M := M))
    (w : List iota) {f : M → C(K, ℝ)}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, C(K, ℝ)) ∞ f) :
    ContMDiff (𝓡 n) 𝓘(ℝ, C(K, ℝ)) ∞ (pathWord F w f) := by
  induction w with
  | nil => exact hf
  | cons i w ih => exact pathDirectional_contMDiff (F i) ih

theorem pathWord_eval (F : iota → SmoothField (n := n) (M := M))
    (w : List iota) {f : M → C(K, ℝ)}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, C(K, ℝ)) ∞ f) (t : K) (x : M) :
    pathWord F w f x t = directionalWord F w (fun y => f y t) x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    rw [pathWord, pathDirectional_eval (F i) (pathWord_contMDiff F w hf)]
    change scalarDirectional (F i) (fun y => pathWord F w f y t) x = _
    rw [show (fun y => pathWord F w f y t) = directionalWord F w (fun y => f y t)
      from funext ih]
    rfl

variable [CompactSpace M]

def wordSpatialMap (F : iota → SmoothField (n := n) (M := M))
    (w : List iota) (f : M → C(K, ℝ))
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, C(K, ℝ)) ∞ f) (t : K) : C(M, ℝ) :=
  ⟨fun x => pathWord F w f x t,
    (ContinuousMap.evalCLM ℝ t).continuous.comp (pathWord_contMDiff F w hf).continuous⟩

theorem wordSpatialMap_continuous (F : iota → SmoothField (n := n) (M := M))
    (w : List iota) (f : M → C(K, ℝ))
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, C(K, ℝ)) ∞ f) :
    Continuous (wordSpatialMap F w f hf) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp
    (((pathWord_contMDiff F w hf).continuous.comp continuous_snd).prodMk continuous_fst)

end NativePathWords

section ActualCoordinates

variable {n : ℕ} {M K : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace K] [CompactSpace K]
  {g0 : RiemannianMetric n M} (d : Data g0)

def probeWordTuple (Q : d.ProbeIndex → M → C(K, ℝ))
    (hQ : ∀ ab, ContMDiff (𝓡 n) 𝓘(ℝ, C(K, ℝ)) ∞ (Q ab))
    (k : ℕ) (t : K) : ProbeTuples d k :=
  fun ab w => ContinuousMap.toLp 2 d.charts.measure ℝ
    (wordSpatialMap d.fields (List.ofFn w.2) (Q ab) (hQ ab) t)

theorem probeWordTuple_continuous (Q : d.ProbeIndex → M → C(K, ℝ))
    (hQ : ∀ ab, ContMDiff (𝓡 n) 𝓘(ℝ, C(K, ℝ)) ∞ (Q ab)) (k : ℕ) :
    Continuous (probeWordTuple d Q hQ k) := by
  apply continuous_pi
  intro ab
  apply continuous_pi
  intro w
  exact (ContinuousMap.toLp 2 d.charts.measure ℝ).continuous.comp
    (wordSpatialMap_continuous d.fields (List.ofFn w.2) (Q ab) (hQ ab))

theorem probeWordTuple_eq (Q : d.ProbeIndex → M → C(K, ℝ))
    (hQ : ∀ ab, ContMDiff (𝓡 n) 𝓘(ℝ, C(K, ℝ)) ∞ (Q ab))
    (h : K → SmoothTensor (n := n) (M := M))
    (hprobe : ∀ ab x t, Q ab x t = scalarProbe d.fields (h t) ab x)
    (k : ℕ) (t : K) : probeWordTuple d Q hQ k t = smoothProbeTuples d k (h t) := by
  funext ab w
  apply congrArg (ContinuousMap.toLp 2 d.charts.measure ℝ)
  apply ContinuousMap.ext
  intro x
  change pathWord d.fields (List.ofFn w.2) (Q ab) x t = _
  rw [pathWord_eval d.fields (List.ofFn w.2) (hQ ab)]
  congr 1
  exact funext (fun y => hprobe ab y t)

def evenCoordinatesPath (Q : d.ProbeIndex → M → C(K, ℝ))
    (hQ : ∀ ab, ContMDiff (𝓡 n) 𝓘(ℝ, C(K, ℝ)) ∞ (Q ab)) (r : ℕ) :
    C(K, State d.SymmetricIndex) :=
  ⟨fun t => evenOutput d r (probeWordTuple d Q hQ (2 * r) t),
    (evenOutput d r).continuous.comp (probeWordTuple_continuous d Q hQ (2 * r))⟩

theorem evenCoordinatesPath_apply (Q : d.ProbeIndex → M → C(K, ℝ))
    (hQ : ∀ ab, ContMDiff (𝓡 n) 𝓘(ℝ, C(K, ℝ)) ∞ (Q ab))
    (h : K → SmoothTensor (n := n) (M := M))
    (hs : ∀ t (x : M) (v w : TangentSpace (𝓡 n) x), h t x v w = h t x w v)
    (hprobe : ∀ ab x t, Q ab x t = scalarProbe d.fields (h t) ab x)
    (r : ℕ) (t : K) :
    evenCoordinatesPath d Q hQ r t = d.smoothTensorCoordinates (2 * r) (h t) (hs t) := by
  change evenOutput d r (probeWordTuple d Q hQ (2 * r) t) = _
  rw [probeWordTuple_eq d Q hQ h hprobe, evenOutput_smoothProbeTuples d r (h t) (hs t)]

end ActualCoordinates

section StateIdentification

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {g0 : RiemannianMetric n M} (d : Data g0)
  (L : FiniteChartLocalizationData d.charts)
  (r p : ℕ) (hpr : p ≤ r) (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))

theorem value_eq_of_coefficients (v w : d.Value)
    (h : ∀ ab, d.valueCoefficient ab v = d.valueCoefficient ab w) : v = w := by
  apply Subtype.ext
  apply Lp.ext
  have heq (ab : d.ProbeIndex) :
      (fun x => (v : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure) x ab) =ᵐ[d.charts.measure]
      (fun x => (w : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure) x ab) := by
    have hv := d.valueCoefficient_coe ab v
    rw [h ab] at hv
    exact hv.symm.trans (d.valueCoefficient_coe ab w)
  filter_upwards [ae_all_iff.mpr heq] with x hx
  ext ab
  exact hx ab


theorem toLp_zeroProbe (z : State d.SymmetricIndex) (ab : d.ProbeIndex) :
    ContinuousMap.toLp 2 d.charts.measure ℝ (zeroProbe d L r p hpr hp ab z) =
      d.valueCoefficient ab (d.symmetricScaleValue (2 * r) z : d.Value) := by
  let A := (ContinuousMap.toLp 2 d.charts.measure ℝ).comp (zeroProbe d L r p hpr hp ab)
  let B := (d.valueCoefficient ab).comp
    (d.symmetricValue.subtypeL.comp (d.symmetricScaleValue (2 * r)))
  obtain ⟨h, hs, hlim⟩ := exists_smooth_symmetric_approximation d L r z
  have hid (j : ℕ) : A (d.smoothTensorCoordinates (2 * r) (h j) (hs j)) =
      B (d.smoothTensorCoordinates (2 * r) (h j) (hs j)) := by
    change ContinuousMap.toLp 2 d.charts.measure ℝ
        (zeroProbe d L r p hpr hp ab (d.smoothTensorCoordinates (2 * r) (h j) (hs j))) =
      d.valueCoefficient ab (d.symmetricScaleValue (2 * r)
        (d.smoothTensorCoordinates (2 * r) (h j) (hs j)) : d.Value)
    rw [d.symmetricScaleValue_smoothTensorCoordinates]
    apply Lp.ext
    filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ENNReal))
      (μ := d.charts.measure) (𝕜 := ℝ)
      (zeroProbe d L r p hpr hp ab (d.smoothTensorCoordinates (2 * r) (h j) (hs j))),
      d.valueCoefficient_into_coe ab (h j)] with x hA hB
    rw [hA]
    change _ = d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure (h j)) x
    rw [hB]
    exact probeEvaluation_smoothTensorCoordinates d L r p hpr hp (h j) (hs j) ab x
  change A z = B z
  exact tendsto_nhds_unique
    (by simpa only [Function.comp_def, hid] using (A.continuous.tendsto z).comp hlim)
    ((B.continuous.tendsto z).comp hlim)

theorem state_eq_of_probeEvaluation (z w : State d.SymmetricIndex)
    (h : ∀ ab x, probeEvaluation d L r p hpr hp ab x z =
      probeEvaluation d L r p hpr hp ab x w) : z = w := by
  apply d.symmetricScaleValue_injective (2 * r)
  apply Subtype.ext
  apply value_eq_of_coefficients d
  intro ab
  rw [← toLp_zeroProbe d L r p hpr hp z ab, ← toLp_zeroProbe d L r p hpr hp w ab]
  congr 1
  exact ContinuousMap.ext (h ab)

theorem smoothTensorCoordinates_eq_of_probes
    (h : SmoothTensor (n := n) (M := M))
    (hs : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (z : State d.SymmetricIndex)
    (hprobe : ∀ ab x, scalarProbe d.fields h ab x = probeEvaluation d L r p hpr hp ab x z) :
    d.smoothTensorCoordinates (2 * r) h hs = z := by
  apply state_eq_of_probeEvaluation d L r p hpr hp
  intro ab x
  rw [probeEvaluation_smoothTensorCoordinates]
  exact hprobe ab x


theorem evenCoordinatesPath_scaleDecode_two
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (Q : d.ProbeIndex → M → C(K, ℝ))
    (hQ : ∀ ab, ContMDiff (𝓡 n) 𝓘(ℝ, C(K, ℝ)) ∞ (Q ab))
    (h : K → SmoothTensor (n := n) (M := M))
    (hs : ∀ t (x : M) (v w : TangentSpace (𝓡 n) x), h t x v w = h t x w v)
    (hprobe : ∀ ab x t, Q ab x t = scalarProbe d.fields (h t) ab x)
    (u : K → State d.SymmetricIndex)
    (hu : ∀ ab x t, Q ab x t = probeEvaluation d L r p hpr hp ab x (u t)) (t : K) :
    scaleDecode d.symmetricParameters 2 (evenCoordinatesPath d Q hQ (r + 1) t) = u t := by
  rw [evenCoordinatesPath_apply d Q hQ h hs hprobe]
  rw [show 2 * (r + 1) = 2 * r + 2 by omega,
    scaleDecode_smoothTensorCoordinates]
  apply smoothTensorCoordinates_eq_of_probes d L r p hpr hp
  intro ab x
  exact (hprobe ab x t).symm.trans (hu ab x t)

end StateIdentification

section RecoveredCoordinates

variable {n : ℕ} {M K : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace K] [CompactSpace K]
  {g0 : RiemannianMetric n M} (d : Data g0)
  (L : FiniteChartLocalizationData d.charts)
  (r p : ℕ) (hpr : p ≤ r) (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
  (z : C(K, State d.SymmetricIndex))
  (hspatial : ∀ ab : d.ProbeIndex,
    ContMDiff (𝓡 n) 𝓘(ℝ, C(K, ℝ)) ∞ (probePath d L r p hpr hp z ab))

def recoveredHighPath : C(K, State d.SymmetricIndex) :=
  evenCoordinatesPath d (probePath d L r p hpr hp z) hspatial (r + 1)

theorem recoveredHighPath_apply (t : K) :
    recoveredHighPath d L r p hpr hp z hspatial t =
      d.smoothTensorCoordinates (2 * r + 2)
        (recoveredTensor d L r p hpr hp z hspatial t)
        (recoveredTensor_symmetric d L r p hpr hp z hspatial t) := by
  simpa only [recoveredHighPath, Nat.mul_add, Nat.mul_one] using
    evenCoordinatesPath_apply d (probePath d L r p hpr hp z) hspatial
      (recoveredTensor d L r p hpr hp z hspatial)
      (recoveredTensor_symmetric d L r p hpr hp z hspatial)
      (fun ab x t => (scalarProbe_recoveredTensor d L r p hpr hp z hspatial t ab x).symm)
      (r + 1) t

theorem recoveredHighPath_scaleDecode (t : K) :
    scaleDecode d.symmetricParameters 2 (recoveredHighPath d L r p hpr hp z hspatial t) = z t :=
  evenCoordinatesPath_scaleDecode_two d L r p hpr hp
    (probePath d L r p hpr hp z) hspatial
    (recoveredTensor d L r p hpr hp z hspatial)
    (recoveredTensor_symmetric d L r p hpr hp z hspatial)
    (fun ab x t => (scalarProbe_recoveredTensor d L r p hpr hp z hspatial t ab x).symm)
    z (fun _ _ _ => rfl) t

theorem recoveredTensor_coordinates (t : K) :
    d.smoothTensorCoordinates (2 * r)
      (recoveredTensor d L r p hpr hp z hspatial t)
      (recoveredTensor_symmetric d L r p hpr hp z hspatial t) = z t := by
  apply smoothTensorCoordinates_eq_of_probes d L r p hpr hp
  intro ab x
  exact scalarProbe_recoveredTensor d L r p hpr hp z hspatial t ab x

theorem recoveredTensor_traceCoordinates (t : K) :
    d.smoothTensorCoordinates (2 * r + 1)
      (recoveredTensor d L r p hpr hp z hspatial t)
      (recoveredTensor_symmetric d L r p hpr hp z hspatial t) =
    scaleDecode d.symmetricParameters 1 (recoveredHighPath d L r p hpr hp z hspatial t) := by
  rw [recoveredHighPath_apply]
  have hlevel : 2 * r + 2 = (2 * r + 1) + 1 := by omega
  rw [hlevel, scaleDecode_smoothTensorCoordinates]

end RecoveredCoordinates

section ActualResponse

variable {iota : Type*} [Countable iota] {T : ℝ} (lambda : iota → NNReal)
  (N : SpatialResidual lambda) (hT : 0 ≤ T) (F : ForcingSpace iota T)
  (H : C(Icc (0 : ℝ) T, State iota))

def responseVelocity : C(Icc (0 : ℝ) T, State iota) :=
  ⟨fun t => N.toFun (H t) - (H t - responseState lambda F t),
    (N.continuous.comp H.continuous).sub
      (H.continuous.sub (responsePath hT lambda F).continuous)⟩

theorem scaleDecode_one_high_eq_trace
    (hH : ∀ t : Icc (0 : ℝ) T, scaleDecode lambda 2 (H t) = responseState lambda F t)
    (t : Icc (0 : ℝ) T) :
    scaleDecode lambda 1 (H t) = shiftedTracePath hT lambda F t := by
  apply scaleDecode_injective lambda 1
  calc
    _ = scaleDecode lambda 2 (H t) := by
      rw [← ContinuousLinearMap.comp_apply, ← scaleDecode_add]
    _ = responseState lambda F t := hH t
    _ = _ := (scaleDecode_shiftedTracePath hT lambda F t).symm

include hT in
theorem norm_scaleDecode_one_high_le (hT1 : T ≤ 1)
    (hH : ∀ t : Icc (0 : ℝ) T, scaleDecode lambda 2 (H t) = responseState lambda F t)
    (t : Icc (0 : ℝ) T) : ‖scaleDecode lambda 1 (H t)‖ ≤ 2 * ‖F‖ := by
  rw [scaleDecode_one_high_eq_trace lambda hT F H hH t]
  calc
    _ ≤ ‖shiftedTracePath hT lambda F‖ := ContinuousMap.norm_coe_le_norm _ _
    _ ≤ (Real.sqrt T + 1) * ‖F‖ := norm_shiftedTracePath_le hT lambda F
    _ ≤ 2 * ‖F‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hs : Real.sqrt T ≤ 1 := by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hT1
      linarith

theorem fixedPoint_response_integral (hfix : N.forcingResidual hT F = F)
    (hH : ∀ t : Icc (0 : ℝ) T, scaleDecode lambda 2 (H t) = responseState lambda F t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    responseState lambda F t =
      ∫ s in (0 : ℝ)..t, IccExtend hT (responseVelocity lambda N hT F H) s := by
  let V := responseVelocity lambda N hT F H
  have hV : Continuous (IccExtend hT V) := V.continuous.comp continuous_projIcc
  have hcont : ContinuousOn (responseState lambda F) (Icc (0 : ℝ) t) :=
    (continuousOn_responseState_of_memLp hT (Lp.memLp F) lambda).mono
      (Icc_subset_Icc le_rfl ht.2)
  have hder (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) t) :
      HasDerivAt (responseState lambda F) (IccExtend hT V s) s := by
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
    rw [IccExtend_of_mem hT V hsT]
    exact (N.fixedPoint_hasDerivWithinAt hT F hfix H hH hsT).hasDerivAt
      (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2))
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcont hder
    (hV.intervalIntegrable 0 t)
  simpa only [responseState_zero, sub_zero] using heq.symm

end ActualResponse

section NativeSource

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {g0 : RiemannianMetric n M} (d : Data g0) {r : ℕ} (A : NativeParameterData d r)


theorem spatialVelocity_smoothTensorCoordinates
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (B : LeviCivitaData g0)
    (h : SmoothTensor (n := n) (M := M))
    (hs : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = g0.inner x v w + h x v w)
    (hsmall : ‖d.smoothTensorCoordinates (2 * r + 1) h hs‖ ≤ A.radius) :
    A.spatialResidual.toFun (d.smoothTensorCoordinates (2 * r + 2) h hs) -
      (d.smoothTensorCoordinates (2 * r + 2) h hs - d.smoothTensorCoordinates (2 * r) h hs) =
    d.smoothTensorCoordinates (2 * r) (smoothRicciDeTurckTensor D B)
      (smoothRicciDeTurckTensor_symm D B) := by
  have hraw := rawState_smooth_agreement d A g D B h hs hmetric hsmall
  rw [rawState, A.raw_agreement g D B h hs hmetric hsmall] at hraw
  rw [A.spatialResidual_agreement g D B h hs hmetric hsmall, hraw]
  have hgen : highGenerator d.symmetricParameters
      (d.smoothTensorCoordinates (2 * r + 2) h hs) =
      d.smoothTensorCoordinates (2 * r + 2) h hs - d.smoothTensorCoordinates (2 * r) h hs := by
    change _ - scaleDecode d.symmetricParameters 2
      (d.smoothTensorCoordinates (2 * r + 2) h hs) = _
    rw [scaleDecode_smoothTensorCoordinates]
    rfl
  rw [hgen]
  abel

end NativeSource

section RecoveredPDE

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {g0 : RiemannianMetric n M} (d : Data g0)
  (L : FiniteChartLocalizationData d.charts)
  (r p : ℕ) (hpr : p ≤ r) (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
  {T : ℝ} (hT : 0 ≤ T) (F : ForcingSpace d.SymmetricIndex T)
  (hspatial : ∀ ab : d.ProbeIndex,
    ContMDiff (𝓡 n) 𝓘(ℝ, C(Icc (0 : ℝ) T, ℝ)) ∞
      (probePath d L r p hpr hp (responsePath hT d.symmetricParameters F) ab))

local notation "u" => responsePath hT d.symmetricParameters F
local notation "h" => recoveredTensor d L r p hpr hp u hspatial
local notation "hs" => recoveredTensor_symmetric d L r p hpr hp u hspatial
local notation "H" => recoveredHighPath d L r p hpr hp u hspatial

theorem recoveredTensor_traceCoordinates_eq (t : Icc (0 : ℝ) T) :
    d.smoothTensorCoordinates (2 * r + 1) (h t) (hs t) =
      shiftedTracePath hT d.symmetricParameters F t := by
  rw [recoveredTensor_traceCoordinates]
  exact scaleDecode_one_high_eq_trace d.symmetricParameters hT F H
    (recoveredHighPath_scaleDecode d L r p hpr hp u hspatial) t

theorem recoveredTensor_traceCoordinates_norm_le (hT1 : T ≤ 1) (t : Icc (0 : ℝ) T) :
    ‖d.smoothTensorCoordinates (2 * r + 1) (h t) (hs t)‖ ≤ 2 * ‖F‖ := by
  rw [recoveredTensor_traceCoordinates]
  exact norm_scaleDecode_one_high_le d.symmetricParameters hT F H hT1
    (recoveredHighPath_scaleDecode d L r p hpr hp u hspatial) t

variable (A : NativeParameterData d r)


theorem recovered_responseVelocity_eq (hT1 : T ≤ 1)
    (hsmall : 2 * ‖F‖ ≤ A.radius)
    (g : ℝ → RiemannianMetric n M)
    (hmetric : ∀ (t : Icc (0 : ℝ) T) (x : M) (v w : TangentSpace (𝓡 n) x),
      (g t).inner x v w = g0.inner x v w + h t x v w)
    (t : Icc (0 : ℝ) T) (D : LeviCivitaData (g t)) (B : LeviCivitaData g0) :
    responseVelocity d.symmetricParameters A.spatialResidual hT F H t =
      d.smoothTensorCoordinates (2 * r) (smoothRicciDeTurckTensor D B)
        (smoothRicciDeTurckTensor_symm D B) := by
  change A.spatialResidual.toFun (H t) - (H t - responseState d.symmetricParameters F t) = _
  rw [recoveredHighPath_apply]
  have hcoords := recoveredTensor_coordinates d L r p hpr hp u hspatial t
  simp only [responsePath_apply] at hcoords
  rw [← hcoords]
  exact spatialVelocity_smoothTensorCoordinates d A (g t) D B (h t) (hs t)
    (hmetric t)
    ((recoveredTensor_traceCoordinates_norm_le d L r p hpr hp hT F hspatial hT1 t).trans hsmall)


theorem recoveredTensor_hasDerivWithinAt (hT1 : T ≤ 1)
    (hfix : A.spatialResidual.forcingResidual hT F = F) (hsmall : 2 * ‖F‖ ≤ A.radius)
    (g : ℝ → RiemannianMetric n M)
    (hmetric : ∀ (t : Icc (0 : ℝ) T) (x : M) (v w : TangentSpace (𝓡 n) x),
      (g t).inner x v w = g0.inner x v w + h t x v w)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (D : LeviCivitaData (g t))
    (B : LeviCivitaData g0) (x : M) (v w : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (IccExtend hT (fun s => h s x v w))
      (smoothRicciDeTurckTensor D B x v w) (Icc (0 : ℝ) T) t := by
  let ev := tensorEvaluation d L r p hpr hp x v w
  have hH := recoveredHighPath_scaleDecode d L r p hpr hp u hspatial
  have hd := A.spatialResidual.fixedPoint_hasDerivWithinAt hT F hfix H hH ht
  have hscalar := ev.hasFDerivAt.comp_hasDerivWithinAt t hd
  have hsource := recovered_responseVelocity_eq d L r p hpr hp hT F hspatial A hT1
    hsmall g hmetric ⟨t, ht⟩ D B
  change A.spatialResidual.toFun (H ⟨t, ht⟩) -
    (H ⟨t, ht⟩ - responseState d.symmetricParameters F t) = _ at hsource
  rw [hsource] at hscalar
  change HasDerivWithinAt (fun s => ev (responseState d.symmetricParameters F s))
    (tensorEvaluation d L r p hpr hp x v w
      (d.smoothTensorCoordinates (2 * r) (smoothRicciDeTurckTensor D B)
        (smoothRicciDeTurckTensor_symm D B))) (Icc (0 : ℝ) T) t at hscalar
  rw [tensorEvaluation_smoothTensorCoordinates] at hscalar
  apply hscalar.congr_of_mem _ ht
  intro s hsT
  rw [IccExtend_of_mem hT _ hsT, recoveredTensor_apply]
  exact (tensorEvaluation_apply d L r p hpr hp (u ⟨s, hsT⟩) x v w).symm


theorem recoveredTensor_integral_equation (hT1 : T ≤ 1)
    (hfix : A.spatialResidual.forcingResidual hT F = F) (hsmall : 2 * ‖F‖ ≤ A.radius)
    (g : ℝ → RiemannianMetric n M)
    (hmetric : ∀ (t : Icc (0 : ℝ) T) (x : M) (v w : TangentSpace (𝓡 n) x),
      (g t).inner x v w = g0.inner x v w + h t x v w)
    (D : ∀ t : Icc (0 : ℝ) T, LeviCivitaData (g t)) (B : LeviCivitaData g0)
    (t : Icc (0 : ℝ) T) (x : M) (v w : TangentSpace (𝓡 n) x) :
    h t x v w = ∫ s in (0 : ℝ)..t,
      smoothRicciDeTurckTensor (D (projIcc 0 T hT s)) B x v w := by
  let ev := tensorEvaluation d L r p hpr hp x v w
  let V := responseVelocity d.symmetricParameters A.spatialResidual hT F H
  have hH := recoveredHighPath_scaleDecode d L r p hpr hp u hspatial
  have hint := fixedPoint_response_integral d.symmetricParameters A.spatialResidual hT F H
    hfix hH t.property
  have hV : Continuous (IccExtend hT V) := V.continuous.comp continuous_projIcc
  have hscalar := congrArg ev hint
  rw [← ev.intervalIntegral_comp_comm (hV.intervalIntegrable 0 t)] at hscalar
  calc
    h t x v w = ev (responseState d.symmetricParameters F t) := by
      rw [recoveredTensor_apply]
      exact (tensorEvaluation_apply d L r p hpr hp (u t) x v w).symm
    _ = ∫ s in (0 : ℝ)..t, ev (IccExtend hT V s) := hscalar
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s _
      change ev (V (projIcc 0 T hT s)) = _
      rw [recovered_responseVelocity_eq d L r p hpr hp hT F hspatial A hT1
        hsmall g hmetric (projIcc 0 T hT s) (D (projIcc 0 T hT s)) B]
      exact tensorEvaluation_smoothTensorCoordinates d L r p hpr hp
        (smoothRicciDeTurckTensor (D (projIcc 0 T hT s)) B)
        (smoothRicciDeTurckTensor_symm (D (projIcc 0 T hT s)) B) x v w

theorem recoveredMetric_hasDerivWithinAt (hT1 : T ≤ 1)
    (hfix : A.spatialResidual.forcingResidual hT F = F) (hsmall : 2 * ‖F‖ ≤ A.radius)
    (g : ℝ → RiemannianMetric n M)
    (hmetric : ∀ (t : Icc (0 : ℝ) T) (x : M) (v w : TangentSpace (𝓡 n) x),
      (g t).inner x v w = g0.inner x v w + h t x v w)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (D : LeviCivitaData (g t))
    (B : LeviCivitaData g0) (x : M) (v w : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s => (g s).inner x v w)
      (smoothRicciDeTurckTensor D B x v w) (Icc (0 : ℝ) T) t := by
  have hd := (recoveredTensor_hasDerivWithinAt d L r p hpr hp hT F hspatial A hT1
    hfix hsmall g hmetric ht D B x v w).const_add (g0.inner x v w)
  apply hd.congr_of_mem _ ht
  intro s hsT
  rw [IccExtend_of_mem hT _ hsT]
  exact hmetric ⟨s, hsT⟩ x v w


theorem recoveredMetric_deTurckEquation (hT1 : T ≤ 1)
    (hfix : A.spatialResidual.forcingResidual hT F = F) (hsmall : 2 * ‖F‖ ≤ A.radius)
    (g : ℝ → RiemannianMetric n M)
    (hmetric : ∀ (t : Icc (0 : ℝ) T) (x : M) (v w : TangentSpace (𝓡 n) x),
      (g t).inner x v w = g0.inner x v w + h t x v w)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (x : M) (v w : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s => (g s).inner x v w)
      (MetricFamilyProducerNative.deTurckRHS g0 (g t) x v w) (Ico (0 : ℝ) T) t := by
  have hd := recoveredMetric_hasDerivWithinAt d L r p hpr hp hT F hspatial A hT1
    hfix hsmall g hmetric (Ico_subset_Icc_self ht)
    (MetricFamilyProducerNative.connection (g t))
    (MetricFamilyProducerNative.connection g0) x v w
  rw [smoothRicciDeTurckTensor_apply] at hd
  exact hd.mono Ico_subset_Icc_self

end RecoveredPDE

end PoincareConjecture.DeTurckIntegralPDENative

end
