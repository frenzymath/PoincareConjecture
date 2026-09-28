import PoincareConjecture.Proofs.M03.Existence.DeTurckPullbackResponseNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckParameterBackgroundNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckPositiveStateNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckStatePullbackContinuityNative








set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.DeTurckPullbackForcingNative

open TensorProbeNative TensorHilbertNative ParsevalTensorNative DeTurckNative
  DeTurckJetCoordinatesNative DeTurckJetAffineNative DeTurckResidualNative
  DeTurckStatePullbackNative DeTurckPullbackSourceNative
  DeTurckPullbackResponseNative DeTurckParameterForcingNative
  DeTurckPositiveStateNative DeTurckSmoothForcingNative SpectralHeatNative QuasilinearDeTurckNative
  ChartMeasureNative

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {g0 : RiemannianMetric n M} (d : Data g0)

local notation "StateD" => State d.SymmetricIndex

theorem smoothTensorCoordinates_add (k : ℕ)
    (h1 h2 : SmoothTensor (n := n) (M := M))
    (hs1 : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h1 x v w = h1 x w v)
    (hs2 : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h2 x v w = h2 x w v)
    (hs : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      (h1 + h2) x v w = (h1 + h2) x w v) :
    d.smoothTensorCoordinates k (h1 + h2) hs =
      d.smoothTensorCoordinates k h1 hs1 + d.smoothTensorCoordinates k h2 hs2 := by
  have hinto : d.intoSymmetricValue (h1 + h2) hs =
      d.intoSymmetricValue h1 hs1 + d.intoSymmetricValue h2 hs2 := by
    apply Subtype.ext
    exact map_add (intoTensorL2 d.fields d.charts.measure) h1 h2
  apply lp.ext
  funext i
  change scaleWeight d.symmetricParameters k i *
      d.symmetricBasis.repr (d.intoSymmetricValue (h1 + h2) hs) i =
    scaleWeight d.symmetricParameters k i * d.symmetricBasis.repr (d.intoSymmetricValue h1 hs1) i +
      scaleWeight d.symmetricParameters k i * d.symmetricBasis.repr (d.intoSymmetricValue h2 hs2) i
  rw [hinto, map_add]
  exact mul_add _ _ _

theorem smoothTensorCoordinates_sub (k : ℕ)
    (h1 h2 : SmoothTensor (n := n) (M := M))
    (hs1 : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h1 x v w = h1 x w v)
    (hs2 : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h2 x v w = h2 x w v)
    (hs : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      (h1 - h2) x v w = (h1 - h2) x w v) :
    d.smoothTensorCoordinates k (h1 - h2) hs =
      d.smoothTensorCoordinates k h1 hs1 - d.smoothTensorCoordinates k h2 hs2 := by
  have hinto : d.intoSymmetricValue (h1 - h2) hs =
      d.intoSymmetricValue h1 hs1 - d.intoSymmetricValue h2 hs2 := by
    apply Subtype.ext
    exact map_sub (intoTensorL2 d.fields d.charts.measure) h1 h2
  apply lp.ext
  funext i
  change scaleWeight d.symmetricParameters k i *
      d.symmetricBasis.repr (d.intoSymmetricValue (h1 - h2) hs) i =
    scaleWeight d.symmetricParameters k i * d.symmetricBasis.repr (d.intoSymmetricValue h1 hs1) i -
      scaleWeight d.symmetricParameters k i * d.symmetricBasis.repr (d.intoSymmetricValue h2 hs2) i
  rw [hinto, map_sub]
  exact mul_sub _ _ _

variable {r : ℕ} (K : NativeParameterData d r)

def rawState (z : StateD) : StateD :=
  K.coefficient (shiftedBaseMultiplier d.symmetricParameters z) z +
    K.lower (shiftedBaseMultiplier d.symmetricParameters z)

def shiftedRawState
    (QB : NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) (2 * r + 2))
    (kappa z : StateD) : StateD :=
  rawState d K (kappa + z) +
    K.correction (QB, shiftedBaseMultiplier d.symmetricParameters (kappa + z)) -
    highGenerator d.symmetricParameters kappa

theorem rawState_continuous : Continuous (rawState d K) :=
  ((K.coefficient_smooth.continuous.comp
    (shiftedBaseMultiplier d.symmetricParameters).continuous).clm_apply continuous_id).add
      (K.lower_smooth.continuous.comp (shiftedBaseMultiplier d.symmetricParameters).continuous)

theorem shiftedRawState_continuous
    (QB : NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) (2 * r + 2))
    (kappa : StateD) : Continuous (shiftedRawState d K QB kappa) :=
  (((rawState_continuous d K).comp (continuous_const.add continuous_id)).add
    (K.correction_smooth.continuous.comp
      (continuous_const.prodMk ((shiftedBaseMultiplier d.symmetricParameters).continuous.comp
        (continuous_const.add continuous_id))))).sub continuous_const

theorem rawState_smooth_agreement
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (B0 : LeviCivitaData g0)
    (h : SmoothTensor (n := n) (M := M))
    (hs : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = g0.inner x v w + h x v w)
    (hsmall : ‖d.smoothTensorCoordinates (2 * r + 1) h hs‖ ≤ K.radius) :
    rawState d K (d.smoothTensorCoordinates (2 * r + 2) h hs) =
      highGenerator d.symmetricParameters (d.smoothTensorCoordinates (2 * r + 2) h hs) +
        d.smoothTensorCoordinates (2 * r) (smoothRicciDeTurckTensor D B0)
          (smoothRicciDeTurckTensor_symm D B0) := by
  rw [rawState, K.raw_agreement g D B0 h hs hmetric hsmall,
    highGenerator_smoothTensorCoordinates d (2 * r) h hs]
  exact smoothTensorCoordinates_add d (2 * r)
    (smoothTensorLaplacian d.fields d.charts g0 h) (smoothRicciDeTurckTensor D B0)
    (smoothTensorLaplacian_symm d.fields d.charts g0 h hs)
    (smoothRicciDeTurckTensor_symm D B0) _

theorem rawState_correction_smooth_agreement
    (QB : NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) (2 * r + 2))
    (hQBsmall : ‖QB‖ < K.backgroundRadius)
    (background g : RiemannianMetric n M) (D : LeviCivitaData g)
    (B : LeviCivitaData background) (B0 : LeviCivitaData g0)
    (h : SmoothTensor (n := n) (M := M))
    (hs : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (hQB : ∀ ab w (hw : w.length ≤ 2 * r + 2) x,
      QB ab (wordIndex w hw) x = directionalWord d.fields w
        (probeDifference d.fields background g0 ab) x)
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = g0.inner x v w + h x v w)
    (hsmall : ‖d.smoothTensorCoordinates (2 * r + 1) h hs‖ ≤ K.radius) :
    rawState d K (d.smoothTensorCoordinates (2 * r + 2) h hs) +
      K.correction (QB, shiftedBaseMultiplier d.symmetricParameters
        (d.smoothTensorCoordinates (2 * r + 2) h hs)) =
    highGenerator d.symmetricParameters (d.smoothTensorCoordinates (2 * r + 2) h hs) +
      d.smoothTensorCoordinates (2 * r) (smoothRicciDeTurckTensor D B)
        (smoothRicciDeTurckTensor_symm D B) := by
  have hJ : shiftedBaseMultiplier d.symmetricParameters
      (d.smoothTensorCoordinates (2 * r + 2) h hs) =
      d.smoothTensorCoordinates (2 * r + 1) h hs := by
    simpa only [Nat.add_assoc] using shiftedBase_smoothTensorCoordinates d (2 * r + 1) h hs
  rw [rawState_smooth_agreement d K g D B0 h hs hmetric hsmall, hJ,
    K.correction_agreement QB hQBsmall background g D B B0 h hs hQB hmetric hsmall,
    smoothTensorCoordinates_sub d (2 * r) _ _ (smoothRicciDeTurckTensor_symm D B)
      (smoothRicciDeTurckTensor_symm D B0)]
  abel

section Pullback

variable (L : FiniteChartLocalizationData d.charts)
  (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞) {C : ENNReal}
  (hC : C ≠ ⊤) (hdom : d.charts.measure.map Phi ≤ C • d.charts.measure)

def pullbackSeed (g : RiemannianMetric n M)
    (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞) : SmoothTensor (n := n) (M := M) :=
  metricTensor (smoothPullbackMetric g Phi) - metricTensor g

theorem pullbackSeed_symm (x : M) (v w : TangentSpace (𝓡 n) x) :
    pullbackSeed g0 Phi x v w = pullbackSeed g0 Phi x w v := by
  change (smoothPullbackMetric g0 Phi).inner x v w - g0.inner x v w =
    (smoothPullbackMetric g0 Phi).inner x w v - g0.inner x w v
  rw [(smoothPullbackMetric g0 Phi).symm x v w, g0.symm x v w]

theorem sourceCoordinates_pullback
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (B0 : LeviCivitaData g0)
    (P : LeviCivitaData (smoothPullbackMetric g Phi))
    (Q : LeviCivitaData (smoothPullbackMetric g0 Phi)) :
    d.smoothTensorCoordinates (2 * r) (smoothRicciDeTurckTensor P Q)
        (smoothRicciDeTurckTensor_symm P Q) =
      evenPullback d Phi hC hdom L r
        (d.smoothTensorCoordinates (2 * r) (smoothRicciDeTurckTensor D B0)
          (smoothRicciDeTurckTensor_symm D B0)) := by
  rw [evenPullback_smoothTensorCoordinates]
  have heq : smoothRicciDeTurckTensor P Q =
      smoothPullback d Phi (smoothRicciDeTurckTensor D B0) := by
    ext x v w
    rw [smoothPullback_apply]
    exact smoothRicciDeTurckTensor_pullback g g0 Phi D B0 P Q x v w
  simp only [heq]

def pullbackSeedCoordinates (r : ℕ) : StateD :=
  d.smoothTensorCoordinates (2 * r + 2) (pullbackSeed g0 Phi) (pullbackSeed_symm Phi)

def pulledPerturbation (h : SmoothTensor (n := n) (M := M)) :
    SmoothTensor (n := n) (M := M) :=
  pullbackSeed g0 Phi + smoothPullback d Phi h

theorem pulledPerturbation_symm (h : SmoothTensor (n := n) (M := M))
    (hs : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    pulledPerturbation d Phi h x v w = pulledPerturbation d Phi h x w v := by
  change pullbackSeed g0 Phi x v w + smoothPullback d Phi h x v w =
    pullbackSeed g0 Phi x w v + smoothPullback d Phi h x w v
  rw [pullbackSeed_symm Phi x v w, smoothPullback_symm d Phi h hs x v w]

theorem pulledPerturbation_coordinates
    (h : SmoothTensor (n := n) (M := M))
    (hs : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    d.smoothTensorCoordinates (2 * r + 2) (pulledPerturbation d Phi h)
        (pulledPerturbation_symm d Phi h hs) =
      pullbackSeedCoordinates d Phi r + evenPullback d Phi hC hdom L (r + 1)
        (d.smoothTensorCoordinates (2 * r + 2) h hs) := by
  have hlevel : 2 * (r + 1) = 2 * r + 2 := by omega
  have hpull := evenPullback_smoothTensorCoordinates d Phi hC hdom L (r + 1) h hs
  rw [hlevel] at hpull
  change d.smoothTensorCoordinates (2 * r + 2)
    (pullbackSeed g0 Phi + smoothPullback d Phi h) _ = _
  rw [smoothTensorCoordinates_add d _ _ _ (pullbackSeed_symm Phi)
    (smoothPullback_symm d Phi h hs), ← hpull]
  rfl

theorem pulledMetric_inner (g : RiemannianMetric n M)
    (h : SmoothTensor (n := n) (M := M))
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = g0.inner x v w + h x v w)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    (smoothPullbackMetric g Phi).inner x v w =
      g0.inner x v w + pulledPerturbation d Phi h x v w := by
  change (smoothPullbackMetric g Phi).inner x v w =
    g0.inner x v w + ((smoothPullbackMetric g0 Phi).inner x v w -
      g0.inner x v w + smoothPullback d Phi h x v w)
  rw [smoothPullbackMetric_inner, smoothPullbackMetric_inner, smoothPullback_apply, hmetric]
  ring


theorem shiftedRawState_smooth_covariance
    (QB : NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) (2 * r + 2))
    (hQBsmall : ‖QB‖ < K.backgroundRadius)
    (hQB : ∀ ab w (hw : w.length ≤ 2 * r + 2) x,
      QB ab (wordIndex w hw) x = directionalWord d.fields w
        (probeDifference d.fields (smoothPullbackMetric g0 Phi) g0 ab) x)
    (g : RiemannianMetric n M) (h : SmoothTensor (n := n) (M := M))
    (hs : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = g0.inner x v w + h x v w)
    (hsmall : ‖d.smoothTensorCoordinates (2 * r + 1) h hs‖ ≤ K.radius)
    (hpulled : ‖d.smoothTensorCoordinates (2 * r + 1) (pulledPerturbation d Phi h)
      (pulledPerturbation_symm d Phi h hs)‖ ≤ K.radius) :
    shiftedRawState d K QB (pullbackSeedCoordinates d Phi r)
        (evenPullback d Phi hC hdom L (r + 1)
          (d.smoothTensorCoordinates (2 * r + 2) h hs)) =
      evenPullback d Phi hC hdom L r
          (rawState d K (d.smoothTensorCoordinates (2 * r + 2) h hs)) +
        pullbackCommutator d.symmetricParameters (evenPullback d Phi hC hdom L r)
          (evenPullback d Phi hC hdom L (r + 1))
          (d.smoothTensorCoordinates (2 * r + 2) h hs) := by
  let D : LeviCivitaData g := Classical.choice (exists_leviCivitaData g)
  let B0 : LeviCivitaData g0 := Classical.choice (exists_leviCivitaData g0)
  let P : LeviCivitaData (smoothPullbackMetric g Phi) :=
    Classical.choice (exists_leviCivitaData (smoothPullbackMetric g Phi))
  let Q : LeviCivitaData (smoothPullbackMetric g0 Phi) :=
    Classical.choice (exists_leviCivitaData (smoothPullbackMetric g0 Phi))
  have hcoords := pulledPerturbation_coordinates d L Phi hC hdom (r := r) h hs
  have hsource := sourceCoordinates_pullback d L Phi hC hdom (r := r) g D B0 P Q
  have hnew := rawState_correction_smooth_agreement d K QB hQBsmall
    (smoothPullbackMetric g0 Phi) (smoothPullbackMetric g Phi) P Q B0
    (pulledPerturbation d Phi h) (pulledPerturbation_symm d Phi h hs) hQB
    (pulledMetric_inner d Phi g h hmetric) hpulled
  have hold := rawState_smooth_agreement d K g D B0 h hs hmetric hsmall
  unfold shiftedRawState
  rw [← hcoords, hnew, hcoords, hsource, hold]
  simp only [pullbackCommutator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, map_add]
  abel


theorem shiftedRawState_covariance
    (p : ℕ) (hpr : 2 * p ≤ r) (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (hpositive : K.radius ≤ positivityRadius d L r p hpr hp)
    (QB : NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) (2 * r + 2))
    (hQBsmall : ‖QB‖ < K.backgroundRadius)
    (hQB : ∀ ab w (hw : w.length ≤ 2 * r + 2) x,
      QB ab (wordIndex w hw) x = directionalWord d.fields w
        (probeDifference d.fields (smoothPullbackMetric g0 Phi) g0 ab) x)
    (z : StateD) (hz : ‖shiftedBaseMultiplier d.symmetricParameters z‖ < K.radius)
    (hpulled : ‖shiftedBaseMultiplier d.symmetricParameters
      (pullbackSeedCoordinates d Phi r + evenPullback d Phi hC hdom L (r + 1) z)‖ < K.radius) :
    shiftedRawState d K QB (pullbackSeedCoordinates d Phi r)
        (evenPullback d Phi hC hdom L (r + 1) z) =
      evenPullback d Phi hC hdom L r (rawState d K z) +
        pullbackCommutator d.symmetricParameters (evenPullback d Phi hC hdom L r)
          (evenPullback d Phi hC hdom L (r + 1)) z := by
  obtain ⟨h, hs, g, hlim, hsmall, hmetric, _⟩ :=
    exists_positive_smooth_approximation d L r p hpr hp K.radius_pos hpositive z hz
  let Z (j : ℕ) := d.smoothTensorCoordinates (2 * r + 2) (h j) (hs j)
  let PB := evenPullback d Phi hC hdom L r
  let PH := evenPullback d Phi hC hdom L (r + 1)
  let kappa := pullbackSeedCoordinates d Phi r
  have hnew : Tendsto
      (fun j => shiftedBaseMultiplier d.symmetricParameters (kappa + PH (Z j))) atTop
      (𝓝 (shiftedBaseMultiplier d.symmetricParameters (kappa + PH z))) :=
    ((shiftedBaseMultiplier d.symmetricParameters).continuous.tendsto _).comp
      (tendsto_const_nhds.add ((PH.continuous.tendsto z).comp hlim))
  have hbound : ∀ᶠ j in atTop,
      ‖shiftedBaseMultiplier d.symmetricParameters (kappa + PH (Z j))‖ < K.radius :=
    hnew.norm (Iio_mem_nhds hpulled)
  have heq : (fun j => shiftedRawState d K QB kappa (PH (Z j))) =ᶠ[atTop]
      (fun j => PB (rawState d K (Z j)) +
        pullbackCommutator d.symmetricParameters PB PH (Z j)) := by
    filter_upwards [hbound] with j hj
    have htrace : shiftedBaseMultiplier d.symmetricParameters (kappa + PH (Z j)) =
        d.smoothTensorCoordinates (2 * r + 1) (pulledPerturbation d Phi (h j))
          (pulledPerturbation_symm d Phi (h j) (hs j)) := by
      change shiftedBaseMultiplier d.symmetricParameters
        (pullbackSeedCoordinates d Phi r +
          evenPullback d Phi hC hdom L (r + 1)
            (d.smoothTensorCoordinates (2 * r + 2) (h j) (hs j))) = _
      rw [← pulledPerturbation_coordinates d L Phi hC hdom]
      simpa only [Nat.add_assoc] using shiftedBase_smoothTensorCoordinates d
        (2 * r + 1) (pulledPerturbation d Phi (h j)) (pulledPerturbation_symm d Phi (h j) (hs j))
    rw [htrace] at hj
    exact shiftedRawState_smooth_covariance d K L Phi hC hdom QB hQBsmall hQB
      (g j) (h j) (hs j) (hmetric j) (hsmall j).le hj.le
  have hleft := ((shiftedRawState_continuous d K QB kappa).tendsto (PH z)).comp
    ((PH.continuous.tendsto z).comp hlim)
  have hright := ((PB.continuous.tendsto (rawState d K z)).comp
    (((rawState_continuous d K).tendsto z).comp hlim)).add
      (((pullbackCommutator d.symmetricParameters PB PH).continuous.tendsto z).comp hlim)
  exact tendsto_nhds_unique (hleft.congr' heq) hright

end Pullback

section TimeForcing

theorem fixedPoint_rawState_ae {T : ℝ} (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (F : ForcingSpace d.SymmetricIndex T)
    (hfix : K.spatialResidual.forcingResidual hT F = F)
    (hsmall : ‖F‖ ≤ K.spatialResidual.forcingRadius) :
    F =ᵐ[timeMeasure T] fun t => rawState d K (shiftedHighOperator hT d.symmetricParameters F t) := by
  have huncut : uncutForcing d.symmetricParameters K.coefficientMap K.lowerMap hT F = F :=
    (uncutForcing_eq_cutoff_forcing d.symmetricParameters K.coefficientMap K.lowerMap
      hT hT1 K.radius_pos K.principalConstant K.lowerConstant K.mixed F hsmall).trans hfix
  have hrep := uncutForcing_coe d.symmetricParameters K.coefficientMap K.lowerMap hT F
  rw [huncut] at hrep
  exact hrep

theorem forcing_shiftedRawState_ae {T : ℝ} (hT : 0 ≤ T)
    (QB : NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) (2 * r + 2))
    (kappa : StateD) (F : ForcingSpace d.SymmetricIndex T) :
    K.forcing hT ((QB, kappa), F) =ᵐ[timeMeasure T]
      fun t => shiftedRawState d K QB kappa (shiftedHighOperator hT d.symmetricParameters F t) :=
  parameterForcing_coe d.symmetricParameters K.coefficientMap K.lowerMap K.correctionMap
    hT QB kappa F


theorem nativePullbackForcing_fixedPoint
    (L : FiniteChartLocalizationData d.charts)
    (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞) {C : ENNReal}
    (hC : C ≠ ⊤) (hdom : d.charts.measure.map Phi ≤ C • d.charts.measure)
    (p : ℕ) (hpr : 2 * p ≤ r) (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (hpositive : K.radius ≤ positivityRadius d L r p hpr hp)
    (QB : NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) (2 * r + 2))
    (hQBsmall : ‖QB‖ < K.backgroundRadius)
    (hQB : ∀ ab w (hw : w.length ≤ 2 * r + 2) x,
      QB ab (wordIndex w hw) x = directionalWord d.fields w
        (probeDifference d.fields (smoothPullbackMetric g0 Phi) g0 ab) x)
    {T : ℝ} (hT : 0 ≤ T) (hT1 : T ≤ 1) (F : ForcingSpace d.SymmetricIndex T)
    (hfix : K.spatialResidual.forcingResidual hT F = F)
    (hsmall : ‖F‖ ≤ K.spatialResidual.forcingRadius / 3)
    (hseed : ‖shiftedBaseMultiplier d.symmetricParameters (pullbackSeedCoordinates d Phi r)‖ <
      K.spatialResidual.forcingRadius / 2)
    (htransport : ‖nativePullbackForcing d L Phi hC hdom r hT F‖ <
      K.spatialResidual.forcingRadius / 2) :
    K.forcing hT ((QB, pullbackSeedCoordinates d Phi r),
        nativePullbackForcing d L Phi hC hdom r hT F) =
      nativePullbackForcing d L Phi hC hdom r hT F := by
  let G := nativePullbackForcing d L Phi hC hdom r hT F
  let PB := evenPullback d Phi hC hdom L r
  let PH := evenPullback d Phi hC hdom L (r + 1)
  let kappa := pullbackSeedCoordinates d Phi r
  have hradius := K.forcingRadius_lt
  have hRpos := K.spatialResidual.forcingRadius_pos
  have hFball : ‖F‖ ≤ K.spatialResidual.forcingRadius := by linarith
  apply Lp.ext
  filter_upwards [forcing_shiftedRawState_ae d K hT QB kappa G,
    shiftedHigh_nativePullbackForcing_ae d L Phi hC hdom r hT F,
    fixedPoint_rawState_ae d K hT hT1 F hfix hFball,
    pullbackForcing_coe d.symmetricParameters hT PB PH F,
    intermediate_high_bound hT hT1 d.symmetricParameters F,
    intermediate_high_bound hT hT1 d.symmetricParameters G]
      with t hparam hhigh hbase htrans hbound hboundG
  have hOld : ‖shiftedBaseMultiplier d.symmetricParameters
      (shiftedHighOperator hT d.symmetricParameters F t)‖ < K.radius := by linarith
  have hNew : ‖shiftedBaseMultiplier d.symmetricParameters
      (kappa + PH (shiftedHighOperator hT d.symmetricParameters F t))‖ < K.radius := by
    calc
      _ ≤ ‖shiftedBaseMultiplier d.symmetricParameters kappa‖ +
          ‖shiftedBaseMultiplier d.symmetricParameters
            (PH (shiftedHighOperator hT d.symmetricParameters F t))‖ := by
        rw [map_add]
        exact norm_add_le _ _
      _ ≤ ‖shiftedBaseMultiplier d.symmetricParameters kappa‖ + 2 * ‖G‖ := by
        apply add_le_add le_rfl
        rw [← hhigh]
        exact hboundG
      _ < K.radius := by change _ + 2 * ‖G‖ < _; linarith
  rw [hparam, hhigh]
  rw [shiftedRawState_covariance d K L Phi hC hdom p hpr hp hpositive QB hQBsmall hQB
    (shiftedHighOperator hT d.symmetricParameters F t) hOld hNew, ← hbase]
  change PB (F t) + pullbackCommutator d.symmetricParameters PB PH
    (shiftedHighOperator hT d.symmetricParameters F t) = G t
  change G t = _ at htrans
  rw [htrans]
  change PB (F t) +
    (highGenerator d.symmetricParameters (PH (shiftedHighOperator hT d.symmetricParameters F t)) -
      PB (highGenerator d.symmetricParameters (shiftedHighOperator hT d.symmetricParameters F t))) = _
  abel

end TimeForcing

section ParameterContinuity

open DeTurckStatePullbackContinuityNative DeTurckCompletedOutputNative DeTurckMetricDomainNative

variable (L : FiniteChartLocalizationData d.charts)

theorem nativePullbackForcing_eq
    (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞) {C : ENNReal}
    (hC : C ≠ ⊤) (hdom : d.charts.measure.map Phi ≤ C • d.charts.measure)
    {T : ℝ} (hT : 0 ≤ T) (F : ForcingSpace d.SymmetricIndex T) :
    nativePullbackForcing d L Phi hC hdom r hT F =
      (evenPullback d Phi hC hdom L r).compLpL 2 (timeMeasure T) F +
        (highGenerator d.symmetricParameters).compLpL 2 (timeMeasure T)
          ((evenPullback d Phi hC hdom L (r + 1)).compLpL 2 (timeMeasure T)
            (shiftedHighOperator hT d.symmetricParameters F)) -
        (evenPullback d Phi hC hdom L r).compLpL 2 (timeMeasure T)
          ((highGenerator d.symmetricParameters).compLpL 2 (timeMeasure T)
            (shiftedHighOperator hT d.symmetricParameters F)) := by
  let PB := evenPullback d Phi hC hdom L r
  let PH := evenPullback d Phi hC hdom L (r + 1)
  let A2 := highGenerator d.symmetricParameters
  let H := shiftedHighOperator hT d.symmetricParameters F
  let X := PB.compLpL 2 (timeMeasure T) F
  let Y := A2.compLpL 2 (timeMeasure T) (PH.compLpL 2 (timeMeasure T) H)
  let Z := PB.compLpL 2 (timeMeasure T) (A2.compLpL 2 (timeMeasure T) H)
  apply Lp.ext
  filter_upwards [pullbackForcing_coe d.symmetricParameters hT PB PH F,
    PB.coeFn_compLpL F, A2.coeFn_compLpL (PH.compLpL 2 (timeMeasure T) H),
    PB.coeFn_compLpL (A2.compLpL 2 (timeMeasure T) H),
    PH.coeFn_compLpL H, A2.coeFn_compLpL H, Lp.coeFn_add X Y, Lp.coeFn_sub (X + Y) Z]
      with t hG hX hY hZ hPH hA hadd hsub
  change _ = (X + Y - Z) t
  rw [hsub, Pi.sub_apply, hadd, Pi.add_apply, hX, hY, hZ, hPH, hA]
  exact hG

theorem nativePullbackForcing_refl {C : ENNReal} (hC : C ≠ ⊤)
    (hdom : d.charts.measure.map (Diffeomorph.refl (𝓡 n) M ∞) ≤ C • d.charts.measure)
    {T : ℝ} (hT : 0 ≤ T) (F : ForcingSpace d.SymmetricIndex T) :
    nativePullbackForcing d L (Diffeomorph.refl (𝓡 n) M ∞) hC hdom r hT F = F := by
  apply Lp.ext
  filter_upwards [pullbackForcing_coe d.symmetricParameters hT
    (evenPullback d (Diffeomorph.refl (𝓡 n) M ∞) hC hdom L r)
    (evenPullback d (Diffeomorph.refl (𝓡 n) M ∞) hC hdom L (r + 1)) F] with t ht
  simpa only [nativePullbackForcing, evenPullback_refl, add_sub_cancel_right] using ht

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]


theorem exists_locally_continuous_nativePullbackForcing
    {U : Set P} (hU : IsOpen U) (hzero : (0 : P) ∈ U)
    (Phi : P → Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (hidentity : Phi 0 = Diffeomorph.refl (𝓡 n) M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 n) ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ))
    (hInv : ContMDiffOn (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 n) ∞
      (fun q : P × M => (Phi q.1).symm q.2) (U ×ˢ univ))
    {T : ℝ} (hT : 0 ≤ T) (F : ForcingSpace d.SymmetricIndex T) :
    ∃ C : ENNReal, ∃ hC : C ≠ ⊤, ∃ V : Set P,
      IsOpen V ∧ (0 : P) ∈ V ∧ V ⊆ U ∧
      ∃ hdom : ∀ p ∈ V, d.charts.measure.map (Phi p) ≤ C • d.charts.measure,
        Continuous (fun p : V => nativePullbackForcing d L (Phi p) hC
          (hdom p p.property) r hT F) := by
  obtain ⟨C, hC, Vh, hVh, h0h, hVhU, hdomh, _, Bh, hBh, hboundh⟩ :=
    exists_locally_uniform_evenPullback d L hU hzero Phi hidentity hPhi hInv (r + 1)
  obtain ⟨B, hB, hbefore⟩ :=
    exists_locally_uniform_coefficient_bound d hU hzero Phi hPhi hInv (2 * r)
  have hevent : {p | p ∈ Vh ∧
      ∀ (ab : d.ProbeIndex) (w : WordIndex (Fin d.fieldCount) (2 * r)),
        ‖pullbackWordBefore d (Phi p) (2 * r) ab (List.ofFn w.2)
          (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt)‖ ≤ B} ∈ 𝓝 0 :=
    Filter.inter_mem (hVh.mem_nhds h0h) hbefore
  obtain ⟨V, hVsub, hV, h0V⟩ := mem_nhds_iff.mp hevent
  have hVU : V ⊆ U := fun p hp => hVhU (hVsub hp).1
  have hdom : ∀ p ∈ V, d.charts.measure.map (Phi p) ≤ C • d.charts.measure :=
    fun p hp => hdomh p (hVsub hp).1
  let Bb : ℝ := ‖evenOutput d r‖ * ((C.toReal ^ (1 / (2 : ENNReal)).toReal * B) *
    ‖nativeProbeTupleL2 d L (2 * r) (2 * r) le_rfl‖)
  have hBb : 0 ≤ Bb := mul_nonneg (norm_nonneg _)
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) hB) (norm_nonneg _))
  have hboundb : ∀ p : V, ‖evenPullback d (Phi p) hC (hdom p p.property) L r‖ ≤ Bb :=
    fun p => norm_evenPullback_le d L (Phi p) hC (hdom p p.property) r hB (hVsub p.property).2
  have hboundh' : ∀ p : V,
      ‖evenPullback d (Phi p) hC (hdom p p.property) L (r + 1)‖ ≤ Bh :=
    fun p => hboundh ⟨p, (hVsub p.property).1⟩
  have hcBase := continuous_evenPullback_timeL2 d L Phi hC hdom r
    (continuous_evenPullback d hU hVU Phi hPhi hInv hC hdom L r)
    hBb hboundb (timeMeasure T)
  have hcHigh := continuous_evenPullback_timeL2 d L Phi hC hdom (r + 1)
    (continuous_evenPullback d hU hVU Phi hPhi hInv hC hdom L (r + 1))
    hBh hboundh' (timeMeasure T)
  let H := shiftedHighOperator hT d.symmetricParameters F
  let A2 := (highGenerator d.symmetricParameters).compLpL 2 (timeMeasure T)
  have hc1 := hcBase.comp (continuous_id.prodMk (continuous_const (y := F)))
  have hc2 := A2.continuous.comp
    (hcHigh.comp (continuous_id.prodMk (continuous_const (y := H))))
  have hc3 := hcBase.comp (continuous_id.prodMk (continuous_const (y := A2 H)))
  refine ⟨C, hC, V, hV, h0V, hVU, hdom, ?_⟩
  apply ((hc1.add hc2).sub hc3).congr
  intro p
  exact (nativePullbackForcing_eq d L (Phi p) hC (hdom p p.property) hT F).symm

end ParameterContinuity

section SmoothOrbit

open DeTurckParameterBackgroundNative

variable (L : FiniteChartLocalizationData d.charts)
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem seedCoordinates_eq_pullbackSeedCoordinates
    (Phi : P → Diffeomorph (𝓡 n) (𝓡 n) M M ∞) (p : P) :
    seedCoordinates Phi d (r + 1) p = pullbackSeedCoordinates d (Phi p) r := by
  rw [seedCoordinates_eq]
  simp only [Nat.mul_add, Nat.mul_one]
  rfl

theorem exists_smooth_orbit_of_fixedPoint
    (s : ℕ) (hsr : 2 * s ≤ r) (hs : (n : ℝ) < 2 * (2 * (s : ℝ)))
    (hpositive : K.radius ≤ positivityRadius d L r s hsr hs)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (F : ForcingSpace d.SymmetricIndex T)
    (hfix : K.spatialResidual.forcingResidual hT.le F = F)
    (hsmall : ‖F‖ ≤ K.spatialResidual.forcingRadius / 3)
    (u : (NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) (2 * r + 2) × StateD) →
      ForcingSpace d.SymmetricIndex T)
    (hu0 : u 0 = F) (hu : ContDiffAt ℝ ∞ u 0)
    (hunique : ∀ᶠ q in 𝓝 (0, F), K.forcing hT.le q = q.2 ↔ u q.1 = q.2)
    {U : Set P} (hU : IsOpen U) (hzero : (0 : P) ∈ U)
    (Phi : P → Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (hidentity : Phi 0 = Diffeomorph.refl (𝓡 n) M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 n) ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ))
    (hInv : ContMDiffOn (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 n) ∞
      (fun q : P × M => (Phi q.1).symm q.2) (U ×ˢ univ)) :
    ∃ orbit : P → ResponsePath d.SymmetricIndex T,
      ContDiffAt ℝ ∞ orbit 0 ∧ orbit 0 = responsePath hT.le d.symmetricParameters F ∧
      ∃ C : ENNReal, ∃ hC : C ≠ ⊤, ∃ V : Set P,
        IsOpen V ∧ (0 : P) ∈ V ∧ V ⊆ U ∧
        ∃ hdom : ∀ p ∈ V, d.charts.measure.map (Phi p) ≤ C • d.charts.measure,
          ∀ p (hp : p ∈ V) (t : Icc (0 : ℝ) T),
            orbit p t = evenPullback d (Phi p) hC (hdom p hp) L r
              (responseState d.symmetricParameters F t) := by
  let QB := backgroundTuples Phi d (2 * r + 2)
  let kappa := seedCoordinates Phi d (r + 1)
  let q (p : P) := (QB p, kappa p)
  have hq : ContDiffAt ℝ ∞ q 0 :=
    ((backgroundTuples_contDiffOn Phi d hU hPhi (2 * r + 2)).contDiffAt
      (hU.mem_nhds hzero)).prodMk
      ((seedCoordinates_contDiffOn Phi d hU hPhi (r + 1)).contDiffAt (hU.mem_nhds hzero))
  have hq0 : q 0 = 0 :=
    Prod.ext (backgroundTuples_zero Phi d hidentity (2 * r + 2))
      (seedCoordinates_zero Phi d hidentity (r + 1))
  have huq : ContDiffAt ℝ ∞ (fun p => u (q p)) 0 := by
    have hu' : ContDiffAt ℝ ∞ u (q 0) := by rw [hq0]; exact hu
    exact hu'.comp 0 hq
  let orbit (p : P) : ResponsePath d.SymmetricIndex T :=
    responseOperator hT.le d.symmetricParameters (u (q p))
  have horbit : ContDiffAt ℝ ∞ orbit 0 :=
    (responseOperator hT.le d.symmetricParameters).contDiff.contDiffAt.comp 0 huq
  have horbit0 : orbit 0 = responsePath hT.le d.symmetricParameters F := by
    dsimp only [orbit]
    rw [hq0, hu0]
    rfl
  obtain ⟨C, hC, V0, hV0, h0V0, hV0U, hdom0, hcont⟩ :=
    exists_locally_continuous_nativePullbackForcing d L (r := r) hU hzero
      Phi hidentity hPhi hInv hT.le F
  let p0 : V0 := ⟨0, h0V0⟩
  let Fp (p : V0) := nativePullbackForcing d L (Phi p) hC (hdom0 p p.property) r hT.le F
  have hFp0 : Fp p0 = F := by
    dsimp only [Fp, p0]
    simp only [hidentity, nativePullbackForcing_refl]
  have hqsub : Tendsto (fun p : V0 => q p) (𝓝 p0) (𝓝 0) := by
    simpa only [Function.comp_def, p0, hq0] using hq.continuousAt.tendsto.comp
      (continuous_subtype_val.tendsto p0)
  have hfpsub : Tendsto Fp (𝓝 p0) (𝓝 F) := by
    have h : Tendsto Fp (𝓝 p0) (𝓝 (Fp p0)) := hcont.tendsto p0
    simpa only [hFp0] using h
  have hpair : Tendsto (fun p : V0 => (q p, Fp p)) (𝓝 p0) (𝓝 (0, F)) :=
    hqsub.prodMk_nhds hfpsub
  have hqb : Tendsto (fun p : V0 => QB p) (𝓝 p0) (𝓝 0) :=
    (continuous_fst.tendsto (0 :
      NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) (2 * r + 2) × StateD)).comp hqsub
  have hseed : Tendsto (fun p : V0 =>
      shiftedBaseMultiplier d.symmetricParameters (pullbackSeedCoordinates d (Phi p) r))
      (𝓝 p0) (𝓝 0) := by
    have hk := (continuous_snd.tendsto (0 :
      NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) (2 * r + 2) × StateD)).comp hqsub
    have hj := ((shiftedBaseMultiplier d.symmetricParameters).continuous.tendsto 0).comp hk
    simpa only [Function.comp_def, map_zero, q, kappa, seedCoordinates_eq_pullbackSeedCoordinates] using hj
  have hRpos := K.spatialResidual.forcingRadius_pos
  have hFhalf : ‖F‖ < K.spatialResidual.forcingRadius / 2 := by linarith
  have hQBsmall : ∀ᶠ p : V0 in 𝓝 p0, ‖QB p‖ < K.backgroundRadius := by
    have hn : Tendsto (fun p : V0 => ‖QB p‖) (𝓝 p0) (𝓝 (0 : ℝ)) := by
      simpa only [norm_zero] using hqb.norm
    exact hn (Iio_mem_nhds K.backgroundRadius_pos)
  have hSeedSmall : ∀ᶠ p : V0 in 𝓝 p0,
      ‖shiftedBaseMultiplier d.symmetricParameters (pullbackSeedCoordinates d (Phi p) r)‖ <
        K.spatialResidual.forcingRadius / 2 := by
    have hn : Tendsto (fun p : V0 =>
        ‖shiftedBaseMultiplier d.symmetricParameters (pullbackSeedCoordinates d (Phi p) r)‖)
        (𝓝 p0) (𝓝 (0 : ℝ)) := by
      simpa only [norm_zero] using hseed.norm
    exact hn (Iio_mem_nhds (half_pos hRpos))
  have hFpSmall : ∀ᶠ p : V0 in 𝓝 p0, ‖Fp p‖ < K.spatialResidual.forcingRadius / 2 :=
    hfpsub.norm (Iio_mem_nhds hFhalf)
  have hevent : ∀ᶠ p : V0 in 𝓝 p0,
      ‖QB p‖ < K.backgroundRadius ∧
      ‖shiftedBaseMultiplier d.symmetricParameters (pullbackSeedCoordinates d (Phi p) r)‖ <
        K.spatialResidual.forcingRadius / 2 ∧
      ‖Fp p‖ < K.spatialResidual.forcingRadius / 2 ∧
      (K.forcing hT.le (q p, Fp p) = Fp p ↔ u (q p) = Fp p) :=
    hQBsmall.and (hSeedSmall.and (hFpSmall.and (hpair hunique)))
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hevent
  let V := V0 ∩ Metric.ball (0 : P) eps
  have hV : IsOpen V := hV0.inter Metric.isOpen_ball
  have h0V : (0 : P) ∈ V := ⟨h0V0, Metric.mem_ball_self heps⟩
  have hVU : V ⊆ U := fun p hp => hV0U hp.1
  have hdom : ∀ p ∈ V, d.charts.measure.map (Phi p) ≤ C • d.charts.measure :=
    fun p hp => hdom0 p hp.1
  refine ⟨orbit, horbit, horbit0, C, hC, V, hV, h0V, hVU, hdom, ?_⟩
  intro p hp t
  let a : V0 := ⟨p, hp.1⟩
  have haball : a ∈ Metric.ball p0 eps := by
    simpa only [Metric.mem_ball, Subtype.dist_eq, a, p0] using hp.2
  obtain ⟨haQB, haSeed, haFp, haUnique⟩ := hball haball
  have hactual := nativePullbackForcing_fixedPoint d K L (Phi p) hC (hdom0 p hp.1)
    s hsr hs hpositive (QB p) haQB
    (backgroundTuples_apply Phi d (2 * r + 2) p) hT.le hT1 F hfix hsmall haSeed haFp
  have huf : u (q p) = Fp a := haUnique.mp (by
    simpa only [q, kappa, seedCoordinates_eq_pullbackSeedCoordinates] using hactual)
  change responseState d.symmetricParameters (u (q p)) t = _
  rw [huf]
  exact responseState_nativePullbackForcing d L (Phi p) hC (hdom0 p hp.1) r hT.le F t.property


theorem exists_fixedPoint_with_smooth_orbits
    (s : ℕ) (hsr : 2 * s ≤ r) (hs : (n : ℝ) < 2 * (2 * (s : ℝ)))
    (hpositive : K.radius ≤ positivityRadius d L r s hsr hs) :
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧ ∃ F : ForcingSpace d.SymmetricIndex T,
      K.spatialResidual.forcingResidual hT.le F = F ∧
      ‖F‖ ≤ K.spatialResidual.forcingRadius / 3 ∧
      ∀ (U : Set P), IsOpen U → (0 : P) ∈ U →
      ∀ (Phi : P → Diffeomorph (𝓡 n) (𝓡 n) M M ∞),
        Phi 0 = Diffeomorph.refl (𝓡 n) M ∞ →
        ContMDiffOn (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 n) ∞
          (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ) →
        ContMDiffOn (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 n) ∞
          (fun q : P × M => (Phi q.1).symm q.2) (U ×ˢ univ) →
        ∃ orbit : P → ResponsePath d.SymmetricIndex T,
          ContDiffAt ℝ ∞ orbit 0 ∧ orbit 0 = responsePath hT.le d.symmetricParameters F ∧
          ∃ C : ENNReal, ∃ hC : C ≠ ⊤, ∃ V : Set P,
            IsOpen V ∧ (0 : P) ∈ V ∧ V ⊆ U ∧
            ∃ hdom : ∀ p ∈ V, d.charts.measure.map (Phi p) ≤ C • d.charts.measure,
              ∀ p (hp : p ∈ V) (t : Icc (0 : ℝ) T),
                orbit p t = evenPullback d (Phi p) hC (hdom p hp) L r
                  (responseState d.symmetricParameters F t) := by
  obtain ⟨T, hT, hT1, F, hfix, hsmall, _, u, hu0, hu, _, hunique, _⟩ :=
    K.exists_smooth_fixedPoint
  refine ⟨T, hT, hT1, F, hfix, hsmall, ?_⟩
  intro U hU hzero Phi hidentity hPhi hInv
  exact exists_smooth_orbit_of_fixedPoint d K L s hsr hs hpositive hT hT1 F hfix hsmall
    u hu0 hu hunique hU hzero Phi hidentity hPhi hInv

end SmoothOrbit

end PoincareConjecture.DeTurckPullbackForcingNative

end
