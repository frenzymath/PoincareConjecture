import PoincareConjecture.Proofs.M03.Existence.DeTurckTensorForcingNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckGeneratorCorrectionNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckMetricDomainNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckCompletedOutputNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckTraceCutoffNative

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix.Norms.Elementwise

namespace PoincareConjecture.DeTurckResidualNative

open TensorProbeNative TensorHilbertNative NativeChartScalarLocalization ChartMeasureNative
  DeTurckNative DeTurckCompatibleJetNative DeTurckJetCoordinatesNative
  DeTurckJetAffineNative DeTurckMetricDomainNative DeTurckTensorForcingNative
  DeTurckCompletedOutputNative DeTurckGeneratorCorrectionNative
  DeTurckPrincipalForcingNative DeTurckSourceJetNative DeTurckRationalJetNative
  SpectralHeatNative QuasilinearDeTurckNative

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {g0 : RiemannianMetric n M} (d : Data g0)
  (L : FiniteChartLocalizationData d.charts)
  (A : CompatibleChartCover (n := n) (M := M))

local notation "StateD" => SpectralHeatNative.State d.SymmetricIndex
local notation "LowD" r:max => NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) (r + 1)
local notation "InverseD" => A.centers → C(M, Matrix (Fin n) (Fin n) ℝ)

def lowInput (r p : ℕ) (hpr : 2 * p ≤ r) (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) :
    StateD →L[ℝ] LowD r :=
  nativeProbeTupleContinuous d L (2 * r + 1) (r + 1) p (by omega) hp

def traceInput (r : ℕ) :
    StateD →L[ℝ] NativeProbeL2 (iota := Fin d.fieldCount) d.charts.measure (2 * r + 1) :=
  nativeProbeTupleL2 d L (2 * r + 1) (2 * r + 1) le_rfl

def highInput (r : ℕ) :
    StateD →L[ℝ] NativeProbeL2 (iota := Fin d.fieldCount) d.charts.measure (2 * r + 2) :=
  nativeProbeTupleL2 d L (2 * r + 2) (2 * r + 2) le_rfl

theorem shiftedBase_eq_scaleDecode_one :
    shiftedBaseMultiplier d.symmetricParameters = scaleDecode d.symmetricParameters 1 := by
  ext x i
  change (1 / Real.sqrt (1 + (d.symmetricParameters i : ℝ))) * x i =
    (scaleWeight d.symmetricParameters 1 i)⁻¹ * x i
  simp only [scaleWeight, pow_one, one_div]

theorem shiftedBase_smoothTensorCoordinates (k : ℕ)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    shiftedBaseMultiplier d.symmetricParameters (d.smoothTensorCoordinates (k + 1) h hsymm) =
      d.smoothTensorCoordinates k h hsymm := by
  rw [shiftedBase_eq_scaleDecode_one d]
  apply scaleDecode_injective d.symmetricParameters k
  calc
    _ = scaleDecode d.symmetricParameters (k + 1)
        (d.smoothTensorCoordinates (k + 1) h hsymm) := by
      rw [scaleDecode_add]
      rfl
    _ = d.symmetricBasis.repr (d.intoSymmetricValue h hsymm) :=
      scaleDecode_scaleEncode d.symmetricParameters (k + 1) _ _
    _ = _ := (scaleDecode_scaleEncode d.symmetricParameters k _ _).symm

theorem lowInput_smoothTensorCoordinates (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (ab : d.ProbeIndex) (w : List (Fin d.fieldCount)) (hw : w.length ≤ r + 1) (x : M) :
    lowInput d L r p hpr hp (d.smoothTensorCoordinates (2 * r + 1) h hsymm) ab
      (wordIndex w hw) x = directionalWord d.fields w (scalarProbe d.fields h ab) x :=
  nativeProbeTupleContinuous_smoothTensorCoordinates d L (2 * r + 1) (r + 1) p
    (by omega) hp h hsymm ab w hw x

theorem traceInput_smoothTensorCoordinates (r : ℕ)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (ab : d.ProbeIndex) (w : List (Fin d.fieldCount)) (hw : w.length ≤ 2 * r + 1) :
    traceInput d L r (d.smoothTensorCoordinates (2 * r + 1) h hsymm) ab
      (wordIndex w hw) =ᵐ[d.charts.measure]
      directionalWord d.fields w (scalarProbe d.fields h ab) :=
  nativeProbeTupleL2_smoothTensorCoordinates d L (2 * r + 1) (2 * r + 1) le_rfl
    h hsymm ab w hw

theorem highInput_smoothTensorCoordinates (r : ℕ)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (ab : d.ProbeIndex) (w : List (Fin d.fieldCount)) (hw : w.length ≤ 2 * r + 2) :
    highInput d L r (d.smoothTensorCoordinates (2 * r + 2) h hsymm) ab
      (wordIndex w hw) =ᵐ[d.charts.measure]
      directionalWord d.fields w (scalarProbe d.fields h ab) :=
  nativeProbeTupleL2_smoothTensorCoordinates d L (2 * r + 2) (2 * r + 2) le_rfl
    h hsymm ab w hw

theorem probeDifference_eq_scalarProbe (g : RiemannianMetric n M)
    (h : SmoothTensor (n := n) (M := M))
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = g0.inner x v w + h x v w) (ab : d.ProbeIndex) :
    probeDifference d.fields g g0 ab = scalarProbe d.fields h ab := by
  funext x
  change g.inner x (d.fields ab.1 x) (d.fields ab.2 x) -
    g0.inner x (d.fields ab.1 x) (d.fields ab.2 x) = h x (d.fields ab.1 x) (d.fields ab.2 x)
  rw [hmetric]
  ring

def chartCorrection (r : ℕ) :
    NativeProbeL2 (iota := Fin d.fieldCount) d.charts.measure (2 * r + 1) →L[ℝ]
      ChartSourceTuples (iota := Fin d.fieldCount) A d.charts.measure (2 * r) :=
  ContinuousLinearMap.pi (fun a =>
    correctionL2 d.fields d.charts g0 (A.cutoffs a) d.charts.measure (2 * r))

theorem chartCorrection_ae_eq (r : ℕ)
    (Q : NativeProbeL2 (iota := Fin d.fieldCount) d.charts.measure (2 * r + 1))
    (h : SmoothTensor (n := n) (M := M))
    (hQ : ∀ ab w (hw : w.length ≤ 2 * r + 1),
      Q ab (wordIndex w hw) =ᵐ[d.charts.measure]
        directionalWord d.fields w (scalarProbe d.fields h ab))
    (a : A.centers) (ij : Fin n × Fin n) (word : List (Fin d.fieldCount))
    (hw : word.length ≤ 2 * r) :
    chartCorrection d A r Q a ij (wordIndex word hw) =ᵐ[d.charts.measure]
      directionalWord d.fields word
        (generatorCorrection d.fields d.charts g0 (A.cutoffs a) h ij.1 ij.2) :=
  correctionL2_ae_eq d.fields d.charts g0 (A.cutoffs a) d.charts.measure Q h hQ
    ij.1 ij.2 word hw

def principalOperator (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (B : LowD r → InverseD) (z : StateD) : StateD →L[ℝ] StateD :=
  (evenOutput d r).comp
    ((principalOutputL2 d.fields A g0 d.charts.measure (2 * r)
      (B (lowInput d L r p hpr hp z))).comp (highInput d L r))

theorem principalOperator_contDiff (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (B : LowD r → InverseD) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (principalOperator d L A r p hpr hp B) := by
  have hc : ContDiff ℝ ∞ (fun z : StateD =>
      principalOutputL2 d.fields A g0 d.charts.measure (2 * r)
        (B (lowInput d L r p hpr hp z))) :=
    (principalOutputL2 d.fields A g0 d.charts.measure (2 * r)).contDiff.comp
      (hB.comp (lowInput d L r p hpr hp).contDiff)
  exact contDiff_const.clm_comp (hc.clm_comp contDiff_const)

theorem principalOperator_zero (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (B : LowD r → InverseD) (hB0 : B 0 = 0) :
    principalOperator d L A r p hpr hp B 0 = 0 := by
  simp only [principalOperator, map_zero, hB0, ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.comp_zero]

def lowerSource (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (Phi : (LowD r × NativeProbeL2 (iota := Fin d.fieldCount) d.charts.measure (2 * r + 1)) →
      ChartSourceTuples (iota := Fin d.fieldCount) A d.charts.measure (2 * r))
    (z : StateD) : StateD :=
  evenOutput d r (sourceOutputL2 d.fields A g0 d.charts.measure (2 * r)
    (Phi (lowInput d L r p hpr hp z, traceInput d L r z) +
      chartCorrection d A r (traceInput d L r z)))

theorem lowerSource_contDiff (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (Phi : (LowD r × NativeProbeL2 (iota := Fin d.fieldCount) d.charts.measure (2 * r + 1)) →
      ChartSourceTuples (iota := Fin d.fieldCount) A d.charts.measure (2 * r))
    (hPhi : ContDiff ℝ ∞ Phi) :
    ContDiff ℝ ∞ (lowerSource d L A r p hpr hp Phi) :=
  (evenOutput d r).contDiff.comp
    ((sourceOutputL2 d.fields A g0 d.charts.measure (2 * r)).contDiff.comp
      ((hPhi.comp ((lowInput d L r p hpr hp).contDiff.prodMk
        (traceInput d L r).contDiff)).add
        ((chartCorrection d A r).contDiff.comp (traceInput d L r).contDiff)))

def rawSource (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (B : LowD r → InverseD)
    (Phi : (LowD r × NativeProbeL2 (iota := Fin d.fieldCount) d.charts.measure (2 * r + 1)) →
      ChartSourceTuples (iota := Fin d.fieldCount) A d.charts.measure (2 * r))
    (x : StateD) : StateD :=
  principalOperator d L A r p hpr hp B (shiftedBaseMultiplier d.symmetricParameters x) x +
    lowerSource d L A r p hpr hp Phi (shiftedBaseMultiplier d.symmetricParameters x)

theorem rawSource_eq_chartOutput (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (B : LowD r → InverseD)
    (Phi : (LowD r × NativeProbeL2 (iota := Fin d.fieldCount) d.charts.measure (2 * r + 1)) →
      ChartSourceTuples (iota := Fin d.fieldCount) A d.charts.measure (2 * r))
    (x : StateD) :
    rawSource d L A r p hpr hp B Phi x =
      evenOutput d r (sourceOutputL2 d.fields A g0 d.charts.measure (2 * r)
        (principalChartTopL2 d.fields A g0 d.charts.measure (2 * r)
            (B (lowInput d L r p hpr hp (shiftedBaseMultiplier d.symmetricParameters x)))
            (highInput d L r x) +
          Phi (lowInput d L r p hpr hp (shiftedBaseMultiplier d.symmetricParameters x),
            traceInput d L r (shiftedBaseMultiplier d.symmetricParameters x)) +
          chartCorrection d A r (traceInput d L r (shiftedBaseMultiplier d.symmetricParameters x)))) := by
  simp only [rawSource, principalOperator, lowerSource, ContinuousLinearMap.comp_apply,
    principalOutputL2_apply, map_add]
  abel

theorem exists_rawSource_localMixedBound (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (B : LowD r → InverseD) (hB : ContDiff ℝ ∞ B) (hB0 : B 0 = 0)
    (Phi : (LowD r × NativeProbeL2 (iota := Fin d.fieldCount) d.charts.measure (2 * r + 1)) →
      ChartSourceTuples (iota := Fin d.fieldCount) A d.charts.measure (2 * r))
    (hPhi : ContDiff ℝ ∞ Phi) :
    ∃ rho : ℝ, 0 < rho ∧ ∃ C C0 : NNReal,
      LocalMixedBound d.symmetricParameters rho C C0 (rawSource d L A r p hpr hp B Phi) :=
  exists_localMixedBound_of_contDiffAt d.symmetricParameters
    (principalOperator d L A r p hpr hp B) (lowerSource d L A r p hpr hp Phi)
    ((principalOperator_contDiff d L A r p hpr hp B hB).of_le (by simp)).contDiffAt
    ((lowerSource_contDiff d L A r p hpr hp Phi hPhi).of_le (by simp)).contDiffAt
    (principalOperator_zero d L A r p hpr hp B hB0)

def correctedEntry (g : RiemannianMetric n M)
    (h : SmoothTensor (n := n) (M := M)) (a : A.centers) (ij : Fin n × Fin n) (x : M) : ℝ :=
  (A.cutoffs a).residual g0 g x ij.1 ij.2 +
    generatorCorrection d.fields d.charts g0 (A.cutoffs a) h ij.1 ij.2 x

include d in
theorem chartResidual_contMDiff (g : RiemannianMetric n M)
    (a : A.centers) (ij : Fin n × Fin n) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => (A.cutoffs a).residual g0 g x ij.1 ij.2) := by
  simpa only [eval_residualExpr_compatible] using
    (residualExpr (Sum.inl : Fin n → Fin n ⊕ Fin d.fieldCount) ij.1 ij.2).native_contMDiff
      (combinedFields d.fields (A.cutoffs a)) (compatibleMatrix (A.cutoffs a) g0 g)
      (compatibleMatrix_contMDiff (A.cutoffs a) g0 g)
      (compatibleMatrix_det_ne_zero (A.cutoffs a) g0 g)

theorem correctedEntry_contMDiff (g : RiemannianMetric n M)
    (h : SmoothTensor (n := n) (M := M)) (a : A.centers) (ij : Fin n × Fin n) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (correctedEntry d A g h a ij) :=
  (chartResidual_contMDiff d A g a ij).add
    (generatorCorrection_contMDiff d.fields d.charts g0 (A.cutoffs a) h ij.1 ij.2)

theorem correctedEntry_word (g : RiemannianMetric n M)
    (h : SmoothTensor (n := n) (M := M)) (a : A.centers) (ij : Fin n × Fin n)
    (w : List (Fin d.fieldCount)) (x : M) :
    directionalWord d.fields w (correctedEntry d A g h a ij) x =
      directionalWord d.fields w (fun y => (A.cutoffs a).residual g0 g y ij.1 ij.2) x +
        directionalWord d.fields w
          (generatorCorrection d.fields d.charts g0 (A.cutoffs a) h ij.1 ij.2) x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    have heq : directionalWord d.fields w (correctedEntry d A g h a ij) = fun y =>
        directionalWord d.fields w (fun z => (A.cutoffs a).residual g0 g z ij.1 ij.2) y +
          directionalWord d.fields w
            (generatorCorrection d.fields d.charts g0 (A.cutoffs a) h ij.1 ij.2) y := funext ih
    rw [directionalWord_cons, heq]
    exact congrArg (fun Q : TangentSpace (𝓡 n) x →L[ℝ] ℝ => Q (d.fields i x))
      (mfderiv_add
        ((directionalWord_contMDiff d.fields w
          (chartResidual_contMDiff d A g a ij)).mdifferentiable (by simp) x)
        ((directionalWord_contMDiff d.fields w
          (generatorCorrection_contMDiff d.fields d.charts g0 (A.cutoffs a) h ij.1 ij.2)).mdifferentiable
          (by simp) x))

theorem correctedEntry_reconstruction {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData g0)
    (h : SmoothTensor (n := n) (M := M))
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = g0.inner x v w + h x v w) (ab : d.ProbeIndex) :
    entryReconstruction d.fields A g0 (correctedEntry d A g h) ab =
      scalarProbe d.fields (smoothResidualTensor d.fields d.charts D B h) ab := by
  funext x
  let R := smoothResidualTensor d.fields d.charts D B h
  change (∑ a : A.centers, ∑ ij : Fin n × Fin n,
    outputCoefficient (A.cutoffs a) g0 (A.partition a)
      (d.fields ab.1) (d.fields ab.2) ij.1 ij.2 x * correctedEntry d A g h a ij x) =
        R x (d.fields ab.1 x) (d.fields ab.2 x)
  calc
    _ = ∑ a : A.centers, A.partition a x * R x (d.fields ab.1 x) (d.fields ab.2 x) := by
      apply Finset.sum_congr rfl
      intro a _
      have heq := weighted_source_eq (A.cutoffs a) g0 (A.partition a)
        (subset_tsupport (A.partition a)) (d.fields ab.1) (d.fields ab.2) R
        (fun y i j => correctedEntry d A g h a (i, j) y)
        (fun y hy i j => (smoothResidualTensor_component d.fields d.charts g0
          (A.cutoffs a) d.parseval D B h hmetric hy i j).symm) x
      simpa only [Fintype.sum_prod_type] using heq.symm
    _ = _ := by rw [← Finset.sum_mul, A.weight_sum, one_mul]

theorem correctedOutput_eq (r : ℕ)
    (Q : ChartSourceTuples (iota := Fin d.fieldCount) A d.charts.measure (2 * r))
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (B : LeviCivitaData g0)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = g0.inner x v w + h x v w)
    (hQ : ∀ a ij w (hw : w.length ≤ 2 * r),
      Q a ij (wordIndex w hw) =ᵐ[d.charts.measure]
        directionalWord d.fields w (correctedEntry d A g h a ij)) :
    evenOutput d r (sourceOutputL2 d.fields A g0 d.charts.measure (2 * r) Q) =
      d.residualCoordinates (2 * r) D B h hsymm := by
  apply evenOutput_eq d r _ (smoothResidualTensor d.fields d.charts D B h)
    (smoothResidualTensor_symm d.fields d.charts D B h hsymm)
  intro ab w hw
  rw [sourceOutputL2_apply]
  have heq := sourceOutputWordL2_ae_reconstruction d.fields A g0 d.charts.measure ab w hw
    Q (correctedEntry d A g h) (correctedEntry_contMDiff d A g h) hQ
  rw [correctedEntry_reconstruction d A D B h hmetric ab] at heq
  exact heq

include L A in

theorem exists_rawResidual (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) :
    ∃ (Aop : StateD → StateD →L[ℝ] StateD) (b : StateD → StateD),
      ContDiff ℝ ∞ Aop ∧ ContDiff ℝ ∞ b ∧ Aop 0 = 0 ∧
      ∃ rho : ℝ, 0 < rho ∧ ∃ C C0 : NNReal,
      LocalMixedBound d.symmetricParameters rho C C0
        (fun x => Aop (shiftedBaseMultiplier d.symmetricParameters x) x +
          b (shiftedBaseMultiplier d.symmetricParameters x)) ∧
      ∀ (g : RiemannianMetric n M) (D : LeviCivitaData g) (B : LeviCivitaData g0)
        (h : SmoothTensor (n := n) (M := M))
        (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v),
        (∀ (x : M) (v w : TangentSpace (𝓡 n) x),
          g.inner x v w = g0.inner x v w + h x v w) →
        ‖d.smoothTensorCoordinates (2 * r + 1) h hsymm‖ ≤ rho →
        Aop (shiftedBaseMultiplier d.symmetricParameters
            (d.smoothTensorCoordinates (2 * r + 2) h hsymm))
            (d.smoothTensorCoordinates (2 * r + 2) h hsymm) +
          b (shiftedBaseMultiplier d.symmetricParameters
            (d.smoothTensorCoordinates (2 * r + 2) h hsymm)) =
          d.residualCoordinates (2 * r) D B h hsymm := by
  obtain ⟨deltaB, hdeltaB, Binv, hBinv, hBinv0, hBinvEq⟩ :=
    exists_smooth_cover_inverse_difference d.fields A g0 d.parseval (r + 1)
  obtain ⟨deltaPhi, hdeltaPhi, Phi, hPhi, hPhiEq⟩ :=
    exists_smooth_chart_trace_action d.fields A g0 d.charts.measure d.parseval
      (2 * r) (r + 1) (by omega)
  obtain ⟨rho0, hrho0, C, C0, hmix⟩ :=
    exists_rawSource_localMixedBound d L A r p hpr hp Binv hBinv hBinv0 Phi hPhi
  let delta := min deltaB deltaPhi
  have hdelta : 0 < delta := lt_min hdeltaB hdeltaPhi
  have hden : 0 < ‖lowInput d L r p hpr hp‖ + 1 := by positivity
  have hbound : 0 < delta / (‖lowInput d L r p hpr hp‖ + 1) := div_pos hdelta hden
  let rho := min rho0 (delta / (‖lowInput d L r p hpr hp‖ + 1)) / 2
  have hrho : 0 < rho := half_pos (lt_min hrho0 hbound)
  have hrho0le : rho ≤ rho0 :=
    (half_le_self (le_of_lt (lt_min hrho0 hbound))).trans (min_le_left _ _)
  have hrhoBound : rho < delta / (‖lowInput d L r p hpr hp‖ + 1) :=
    (half_lt_self (lt_min hrho0 hbound)).trans_le (min_le_right _ _)
  have hlowSmall (z : StateD) (hz : ‖z‖ ≤ rho) : ‖lowInput d L r p hpr hp z‖ < delta := by
    have hproduct := (lt_div_iff₀ hden).mp (hz.trans_lt hrhoBound)
    have hop := (lowInput d L r p hpr hp).le_opNorm z
    nlinarith [norm_nonneg z]
  have hmixrho : LocalMixedBound d.symmetricParameters rho C C0
      (rawSource d L A r p hpr hp Binv Phi) := by
    intro x y hx hy
    exact hmix x y (hx.trans hrho0le) (hy.trans hrho0le)
  refine ⟨principalOperator d L A r p hpr hp Binv, lowerSource d L A r p hpr hp Phi,
    principalOperator_contDiff d L A r p hpr hp Binv hBinv,
    lowerSource_contDiff d L A r p hpr hp Phi hPhi,
    principalOperator_zero d L A r p hpr hp Binv hBinv0,
    rho, hrho, C, C0, hmixrho, ?_⟩
  intro g D B h hsymm hmetric hsmall
  have hJ : shiftedBaseMultiplier d.symmetricParameters
      (d.smoothTensorCoordinates (2 * r + 2) h hsymm) =
      d.smoothTensorCoordinates (2 * r + 1) h hsymm := by
    simpa only [Nat.add_assoc] using
      shiftedBase_smoothTensorCoordinates d (2 * r + 1) h hsymm
  change rawSource d L A r p hpr hp Binv Phi _ = _
  rw [rawSource_eq_chartOutput, hJ]
  apply correctedOutput_eq d A r _ D B h hsymm hmetric
  let q := lowInput d L r p hpr hp (d.smoothTensorCoordinates (2 * r + 1) h hsymm)
  let Htrace := traceInput d L r (d.smoothTensorCoordinates (2 * r + 1) h hsymm)
  let Hhigh := highInput d L r (d.smoothTensorCoordinates (2 * r + 2) h hsymm)
  have hq : ∀ ab w (hw : w.length ≤ r + 1) x,
      q ab (wordIndex w hw) x = directionalWord d.fields w (probeDifference d.fields g g0 ab) x := by
    intro ab w hw x
    rw [probeDifference_eq_scalarProbe d g h hmetric ab]
    exact lowInput_smoothTensorCoordinates d L r p hpr hp h hsymm ab w hw x
  have htrace : ∀ ab w (hw : w.length ≤ 2 * r + 1),
      Htrace ab (wordIndex w hw) =ᵐ[d.charts.measure]
        directionalWord d.fields w (probeDifference d.fields g g0 ab) := by
    intro ab w hw
    rw [probeDifference_eq_scalarProbe d g h hmetric ab]
    exact traceInput_smoothTensorCoordinates d L r h hsymm ab w hw
  have hhigh : ∀ ab w (hw : w.length ≤ 2 * r + 2),
      Hhigh ab (wordIndex w hw) =ᵐ[d.charts.measure]
        directionalWord d.fields w (probeDifference d.fields g g0 ab) := by
    intro ab w hw
    rw [probeDifference_eq_scalarProbe d g h hmetric ab]
    exact highInput_smoothTensorCoordinates d L r h hsymm ab w hw
  have hqsmall : ‖q‖ < delta := hlowSmall _ hsmall
  have hactualB := hBinvEq q (hqsmall.trans_le (min_le_left deltaB deltaPhi)) g hq
  have hactualPhi := hPhiEq q (hqsmall.trans_le (min_le_right deltaB deltaPhi)) Htrace g hq htrace
  let U := principalChartTopL2 d.fields A g0 d.charts.measure (2 * r) (Binv q) Hhigh +
    Phi (q, Htrace)
  intro a ij word hw
  have hU := principalChartTopL2_add_trace_ae_eq d.fields A g0 d.charts.measure d.parseval
    (Binv q) Hhigh (Phi (q, Htrace)) g hactualB hhigh hactualPhi a ij word hw
  have hCorr := chartCorrection_ae_eq d A r Htrace h
    (traceInput_smoothTensorCoordinates d L r h hsymm) a ij word hw
  change (U a ij (wordIndex word hw) +
    chartCorrection d A r Htrace a ij (wordIndex word hw)) =ᵐ[d.charts.measure] _
  filter_upwards [hU, hCorr, Lp.coeFn_add (U a ij (wordIndex word hw))
    (chartCorrection d A r Htrace a ij (wordIndex word hw))] with x hx hcx hadd
  rw [hadd, Pi.add_apply, hx, hcx]
  exact (correctedEntry_word d A g h a ij word x).symm

include L A in

theorem exists_spatialResidual (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) :
    ∃ rho : ℝ, 0 < rho ∧ ∃ N : SpatialResidual d.symmetricParameters,
      2 * N.forcingRadius < rho ∧
      ∀ (g : RiemannianMetric n M) (D : LeviCivitaData g) (B : LeviCivitaData g0)
        (h : SmoothTensor (n := n) (M := M))
        (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v),
        (∀ (x : M) (v w : TangentSpace (𝓡 n) x),
          g.inner x v w = g0.inner x v w + h x v w) →
        ‖d.smoothTensorCoordinates (2 * r + 1) h hsymm‖ ≤ rho →
        N.toFun (d.smoothTensorCoordinates (2 * r + 2) h hsymm) =
          d.residualCoordinates (2 * r) D B h hsymm := by
  obtain ⟨Aop, b, _, _, _, rho, hrho, C, C0, hmix, hEq⟩ :=
    exists_rawResidual d L A r p hpr hp
  let raw := fun x => Aop (shiftedBaseMultiplier d.symmetricParameters x) x +
    b (shiftedBaseMultiplier d.symmetricParameters x)
  let N := cutoffSpatialResidual d.symmetricParameters hrho raw C C0 hmix
  refine ⟨rho, hrho, N,
    cutoffSpatialResidual_forcingRadius d.symmetricParameters hrho raw C C0 hmix, ?_⟩
  intro g D B h hsymm hmetric hsmall
  have hJ : shiftedBaseMultiplier d.symmetricParameters
      (d.smoothTensorCoordinates (2 * r + 2) h hsymm) =
      d.smoothTensorCoordinates (2 * r + 1) h hsymm := by
    simpa only [Nat.add_assoc] using
      shiftedBase_smoothTensorCoordinates d (2 * r + 1) h hsymm
  change (cutoffSpatialResidual d.symmetricParameters hrho raw C C0 hmix).toFun _ = _
  rw [cutoffSpatialResidual_apply_of_small d.symmetricParameters hrho raw C C0 hmix
    (by rw [hJ]; exact hsmall)]
  exact hEq g D B h hsymm hmetric hsmall

include L A in

theorem exists_spatialResidual_of_geometry :
    ∃ r : ℕ, ∃ rho : ℝ, 0 < rho ∧ ∃ N : SpatialResidual d.symmetricParameters,
      2 * N.forcingRadius < rho ∧
      ∀ (g : RiemannianMetric n M) (D : LeviCivitaData g) (B : LeviCivitaData g0)
        (h : SmoothTensor (n := n) (M := M))
        (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v),
        (∀ (x : M) (v w : TangentSpace (𝓡 n) x),
          g.inner x v w = g0.inner x v w + h x v w) →
        ‖d.smoothTensorCoordinates (2 * r + 1) h hsymm‖ ≤ rho →
        N.toFun (d.smoothTensorCoordinates (2 * r + 2) h hsymm) =
          d.residualCoordinates (2 * r) D B h hsymm := by
  refine ⟨2 * (n + 1), ?_⟩
  apply exists_spatialResidual d L A (2 * (n + 1)) (n + 1) le_rfl
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  push_cast
  nlinarith

end PoincareConjecture.DeTurckResidualNative

end
