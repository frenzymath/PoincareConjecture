import PoincareConjecture.Proofs.M03.Existence.DeTurckSmoothForcingNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckBackgroundVariationNative

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.DeTurckParameterForcingNative

open SpectralHeatNative QuasilinearDeTurckNative TimeL2BilinearNative
  DeTurckMetricProducerNative ContinuousPathCompositionNative DeTurckSmoothForcingNative

universe u v

section ParameterForcing

variable {iota : Type v} {B : Type u} [Countable iota]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  {T : ℝ} (lambda : iota → NNReal)

def highGenerator : State iota →L[ℝ] State iota :=
  ContinuousLinearMap.id ℝ (State iota) - scaleDecode lambda 2

theorem highGenerator_apply (x : State iota) (i : iota) :
    highGenerator lambda x i = (lambda i : ℝ) / (1 + (lambda i : ℝ)) * x i := by
  change x i - (scaleWeight lambda 2 i)⁻¹ * x i = _
  rw [scaleWeight_two]
  have hden : 1 + (lambda i : ℝ) ≠ 0 := by positivity
  field_simp
  ring

def traceShift (hT : 0 ≤ T) (q : State iota × ForcingSpace iota T) :
    ResponsePath iota T :=
  ContinuousMap.const (Icc (0 : ℝ) T) (shiftedBaseMultiplier lambda q.1) +
    shiftedTraceOperator hT lambda q.2

def highShift (hT : 0 ≤ T) (q : State iota × ForcingSpace iota T) :
    ForcingSpace iota T :=
  tracePathL2 hT (ContinuousMap.const (Icc (0 : ℝ) T) q.1) +
    shiftedHighOperator hT lambda q.2

theorem traceShift_contDiff (hT : 0 ≤ T) :
    ContDiff ℝ ∞ (traceShift lambda hT) := by
  exact ((ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T) :
    State iota →L[ℝ] ResponsePath iota T).contDiff.comp
      ((shiftedBaseMultiplier lambda).contDiff.comp contDiff_fst)).add
    ((shiftedTraceOperator hT lambda).contDiff.comp contDiff_snd)

theorem highShift_contDiff (hT : 0 ≤ T) :
    ContDiff ℝ ∞ (highShift lambda hT) := by
  exact ((tracePathL2 hT).contDiff.comp
    ((ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T) :
      State iota →L[ℝ] ResponsePath iota T).contDiff.comp contDiff_fst)).add
    ((shiftedHighOperator hT lambda).contDiff.comp contDiff_snd)

@[simp] theorem traceShift_zero (hT : 0 ≤ T) (F : ForcingSpace iota T) :
    traceShift lambda hT (0, F) = shiftedTraceOperator hT lambda F := by
  simp [traceShift]

@[simp] theorem highShift_zero (hT : 0 ≤ T) (F : ForcingSpace iota T) :
    highShift lambda hT (0, F) = shiftedHighOperator hT lambda F := by
  simp [highShift]

def backgroundTrace (hT : 0 ≤ T)
    (q : (B × State iota) × ForcingSpace iota T) :
    C(Icc (0 : ℝ) T, B × State iota) :=
  (ContinuousLinearMap.inl ℝ B (State iota)).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (ContinuousMap.const (Icc (0 : ℝ) T) q.1.1) +
    (ContinuousLinearMap.inr ℝ B (State iota)).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (traceShift lambda hT (q.1.2, q.2))

@[simp] theorem backgroundTrace_apply (hT : 0 ≤ T)
    (q : (B × State iota) × ForcingSpace iota T) (t : Icc (0 : ℝ) T) :
    backgroundTrace lambda hT q t = (q.1.1, traceShift lambda hT (q.1.2, q.2) t) := by
  simp [backgroundTrace]

theorem backgroundTrace_contDiff (hT : 0 ≤ T) :
    ContDiff ℝ ∞ (backgroundTrace (B := B) lambda hT) := by
  exact (((ContinuousLinearMap.inl ℝ B (State iota)).compLeftContinuous ℝ
    (Icc (0 : ℝ) T)).contDiff.comp
      ((ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T) :
        B →L[ℝ] C(Icc (0 : ℝ) T, B)).contDiff.comp
          (contDiff_fst.comp contDiff_fst))).add
    (((ContinuousLinearMap.inr ℝ B (State iota)).compLeftContinuous ℝ
      (Icc (0 : ℝ) T)).contDiff.comp
        ((traceShift_contDiff lambda hT).comp
          ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)))

variable (A : C(State iota, State iota →L[ℝ] State iota))
  (b : C(State iota, State iota)) (Delta : C(B × State iota, State iota))

def parameterForcing (hT : 0 ≤ T)
    (q : (B × State iota) × ForcingSpace iota T) : ForcingSpace iota T :=
  productOperator hT (ContinuousLinearMap.id ℝ (State iota →L[ℝ] State iota))
      (A.comp (traceShift lambda hT (q.1.2, q.2))) (highShift lambda hT (q.1.2, q.2)) +
    tracePathL2 hT (b.comp (traceShift lambda hT (q.1.2, q.2))) +
    tracePathL2 hT (Delta.comp (backgroundTrace lambda hT q)) -
    tracePathL2 hT (ContinuousMap.const (Icc (0 : ℝ) T) (highGenerator lambda q.1.2))

theorem parameterForcing_contDiff (hT : 0 ≤ T)
    (hA : ContDiff ℝ ∞ (A : State iota → State iota →L[ℝ] State iota))
    (hb : ContDiff ℝ ∞ (b : State iota → State iota))
    (hDelta : ContDiff ℝ ∞ (Delta : B × State iota → State iota)) :
    ContDiff ℝ ∞ (parameterForcing lambda A b Delta hT) := by
  have harg : ContDiff ℝ ∞ (fun q : (B × State iota) × ForcingSpace iota T =>
      (q.1.2, q.2)) := (contDiff_snd.comp contDiff_fst).prodMk contDiff_snd
  have htrace : ContDiff ℝ ∞ (fun q : (B × State iota) × ForcingSpace iota T =>
      traceShift lambda hT (q.1.2, q.2)) := by
    simpa only [Function.comp_def] using (traceShift_contDiff lambda hT).comp harg
  have hhigh : ContDiff ℝ ∞ (fun q : (B × State iota) × ForcingSpace iota T =>
      highShift lambda hT (q.1.2, q.2)) := by
    simpa only [Function.comp_def] using (highShift_contDiff lambda hT).comp harg
  have hAc : ContDiff ℝ ∞ (fun q : (B × State iota) × ForcingSpace iota T =>
      A.comp (traceShift lambda hT (q.1.2, q.2))) := by
    simpa only [Function.comp_def] using
      (contDiff_postcomp (Icc (0 : ℝ) T) A hA).comp htrace
  have hbc : ContDiff ℝ ∞ (fun q : (B × State iota) × ForcingSpace iota T =>
      b.comp (traceShift lambda hT (q.1.2, q.2))) := by
    simpa only [Function.comp_def] using
      (contDiff_postcomp (Icc (0 : ℝ) T) b hb).comp htrace
  let e : ULift.{max u v} (State iota) ≃L[ℝ] State iota := ContinuousLinearEquiv.ulift
  let Dlift : C(B × State iota, ULift.{max u v} (State iota)) :=
    ⟨fun z => e.symm (Delta z), e.symm.continuous.comp Delta.continuous⟩
  let down : C(Icc (0 : ℝ) T, ULift.{max u v} (State iota)) →L[ℝ] ResponsePath iota T :=
    e.toContinuousLinearMap.compLeftContinuous ℝ (Icc (0 : ℝ) T)
  have hdLift : ContDiff ℝ ∞ (Dlift : B × State iota → ULift.{max u v} (State iota)) :=
    e.symm.contDiff.comp hDelta
  have hDcomp : ContDiff ℝ ∞ (fun q : (B × State iota) × ForcingSpace iota T =>
      Dlift.comp (backgroundTrace lambda hT q)) := by
    simpa only [Function.comp_def] using
      (contDiff_postcomp (Icc (0 : ℝ) T) Dlift hdLift).comp
        (backgroundTrace_contDiff (B := B) lambda hT)
  have hdc : ContDiff ℝ ∞ (fun q : (B × State iota) × ForcingSpace iota T =>
      Delta.comp (backgroundTrace lambda hT q)) := by
    have heq : (fun q : (B × State iota) × ForcingSpace iota T =>
        down (Dlift.comp (backgroundTrace lambda hT q))) =
        (fun q => Delta.comp (backgroundTrace lambda hT q)) := by
      funext q
      apply ContinuousMap.ext
      intro t
      change e (e.symm (Delta (backgroundTrace lambda hT q t))) =
        Delta (backgroundTrace lambda hT q t)
      exact e.apply_symm_apply _
    simpa only [Function.comp_def, heq] using down.contDiff.comp hDcomp
  have hseed : ContDiff ℝ ∞ (fun q : (B × State iota) × ForcingSpace iota T =>
      ContinuousMap.const (Icc (0 : ℝ) T) (highGenerator lambda q.1.2)) := by
    change ContDiff ℝ ∞ (fun q : (B × State iota) × ForcingSpace iota T =>
      (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T) :
        State iota →L[ℝ] ResponsePath iota T) (highGenerator lambda q.1.2))
    simpa only [Function.comp_def] using
      (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T) :
        State iota →L[ℝ] ResponsePath iota T).contDiff.comp
          ((highGenerator lambda).contDiff.comp (contDiff_snd.comp contDiff_fst))
  have htop : ContDiff ℝ ∞ (fun q : (B × State iota) × ForcingSpace iota T =>
      productOperator hT (ContinuousLinearMap.id ℝ (State iota →L[ℝ] State iota))
        (A.comp (traceShift lambda hT (q.1.2, q.2)))
        (highShift lambda hT (q.1.2, q.2))) := by
    simpa only [Function.comp_def] using
      (((productOperator hT
        (ContinuousLinearMap.id ℝ (State iota →L[ℝ] State iota))).contDiff.comp hAc).clm_apply
          hhigh)
  have hlower : ContDiff ℝ ∞ (fun q : (B × State iota) × ForcingSpace iota T =>
      tracePathL2 (E := State iota) hT (b.comp (traceShift lambda hT (q.1.2, q.2)))) := by
    simpa only [Function.comp_def] using
      (tracePathL2 (E := State iota) hT).contDiff.comp hbc
  have hcorrection : ContDiff ℝ ∞ (fun q : (B × State iota) × ForcingSpace iota T =>
      tracePathL2 (E := State iota) hT (Delta.comp (backgroundTrace lambda hT q))) := by
    simpa only [Function.comp_def] using
      (tracePathL2 (E := State iota) hT).contDiff.comp hdc
  have hfixed : ContDiff ℝ ∞ (fun q : (B × State iota) × ForcingSpace iota T =>
      tracePathL2 (E := State iota) hT
        (ContinuousMap.const (Icc (0 : ℝ) T) (highGenerator lambda q.1.2))) := by
    simpa only [Function.comp_def] using
      (tracePathL2 (E := State iota) hT).contDiff.comp hseed
  change ContDiff ℝ ∞ (fun q : (B × State iota) × ForcingSpace iota T =>
    productOperator hT (ContinuousLinearMap.id ℝ (State iota →L[ℝ] State iota))
      (A.comp (traceShift lambda hT (q.1.2, q.2))) (highShift lambda hT (q.1.2, q.2)) +
    tracePathL2 (E := State iota) hT (b.comp (traceShift lambda hT (q.1.2, q.2))) +
    tracePathL2 (E := State iota) hT (Delta.comp (backgroundTrace lambda hT q)) -
    tracePathL2 (E := State iota) hT
      (ContinuousMap.const (Icc (0 : ℝ) T) (highGenerator lambda q.1.2)))
  exact ((htop.add hlower).add hcorrection).sub hfixed

theorem parameterForcing_zero (hT : 0 ≤ T) (hDelta : ∀ z, Delta (0, z) = 0)
    (F : ForcingSpace iota T) :
    parameterForcing lambda A b Delta hT ((0, 0), F) = uncutForcing lambda A b hT F := by
  have hcomp : Delta.comp (backgroundTrace lambda hT ((0, 0), F)) = 0 := by
    apply ContinuousMap.ext
    intro t
    change Delta (backgroundTrace lambda hT ((0, 0), F) t) = 0
    rw [backgroundTrace_apply, traceShift_zero]
    exact hDelta _
  simp only [parameterForcing, traceShift_zero, highShift_zero, hcomp,
    map_zero, ContinuousMap.const_zero, add_zero, sub_zero, uncutForcing]

theorem exists_parameter_fixedPoint [CompleteSpace B]
    (hA : ContDiff ℝ ∞ (A : State iota → State iota →L[ℝ] State iota))
    (hb : ContDiff ℝ ∞ (b : State iota → State iota))
    (hDelta : ContDiff ℝ ∞ (Delta : B × State iota → State iota))
    (hDelta0 : ∀ z, Delta (0, z) = 0)
    {rho : ℝ} (hrho : 0 < rho) (C C0 : NNReal)
    (hmix : LocalMixedBound lambda rho C C0
      (fun x => A (shiftedBaseMultiplier lambda x) x + b (shiftedBaseMultiplier lambda x))) :
    let N := cutoffSpatialResidual lambda hrho
      (fun x => A (shiftedBaseMultiplier lambda x) x + b (shiftedBaseMultiplier lambda x))
      C C0 hmix
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧ ∃ F : ForcingSpace iota T,
      N.forcingResidual hT.le F = F ∧ ‖F‖ ≤ N.forcingRadius / 3 ∧
      ‖F‖ < N.forcingRadius ∧
      ∃ u : B × State iota → ForcingSpace iota T,
        u 0 = F ∧ ContDiffAt ℝ ∞ u 0 ∧
        (∀ᶠ q in 𝓝 0, parameterForcing lambda A b Delta hT.le (q, u q) = u q) ∧
        (∀ᶠ q in 𝓝 (0, F),
          parameterForcing lambda A b Delta hT.le q = q.2 ↔ u q.1 = q.2) ∧
        (∀ᶠ q in 𝓝 0, ‖u q‖ < N.forcingRadius) := by
  let N := cutoffSpatialResidual lambda hrho
    (fun x => A (shiftedBaseMultiplier lambda x) x + b (shiftedBaseMultiplier lambda x))
    C C0 hmix
  obtain ⟨T, hT, hT1, F, hfix, hthird, hstrict, hLip⟩ := N.exists_strict_forcing_fixedPoint
  have hzero (G : ForcingSpace iota T) (hG : ‖G‖ ≤ N.forcingRadius) :
      parameterForcing lambda A b Delta hT.le (0, G) = N.forcingResidual hT.le G :=
    (parameterForcing_zero lambda A b Delta hT.le hDelta0 G).trans
      (uncutForcing_eq_cutoff_forcing lambda A b hT.le hT1 hrho C C0 hmix G hG)
  obtain ⟨u, hu, hsmooth, hufix, hunique⟩ :=
    exists_contDiffAt_fixedPoint_of_contraction (parameterForcing lambda A b Delta hT.le)
      (by simp : (∞ : ℕ∞ω) ≠ 0)
      (parameterForcing_contDiff lambda A b Delta hT.le hA hb hDelta).contDiffAt
      ((hzero F hstrict.le).trans hfix) hstrict
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
      (by
        intro G H hG hH
        rw [hzero G hG, hzero H hH]
        exact hLip G H hG hH)
  refine ⟨T, hT, hT1, F, hfix, hthird, hstrict, u, hu, hsmooth, hufix, hunique, ?_⟩
  have hmem : Metric.ball (0 : ForcingSpace iota T) N.forcingRadius ∈ 𝓝 (u 0) :=
    Metric.isOpen_ball.mem_nhds (by simpa only [hu, Metric.mem_ball, dist_zero_right] using hstrict)
  simpa only [Metric.mem_ball, dist_zero_right] using hsmooth.continuousAt.eventually hmem

end ParameterForcing

section NativeBackground

open TensorProbeNative TensorHilbertNative HilbertResolventNative NativeChartScalarLocalization
  DeTurckNative DeTurckJetCoordinatesNative DeTurckJetAffineNative DeTurckResidualNative
  DeTurckBackgroundVariationNative DeTurckTensorForcingNative DeTurckCompletedOutputNative
  ChartMeasureNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {g0 : RiemannianMetric n M} (d : Data g0)
  (L : FiniteChartLocalizationData d.charts)
  (A : CompatibleChartCover (n := n) (M := M))

local notation "StateD" => State d.SymmetricIndex
local notation "BackgroundD" r:max =>
  NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) (2 * r + 2)

theorem highGenerator_smoothTensorCoordinates (k : ℕ)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    highGenerator d.symmetricParameters (d.smoothTensorCoordinates (k + 2) h hsymm) =
      d.smoothTensorCoordinates k (smoothTensorLaplacian d.fields d.charts g0 h)
        (smoothTensorLaplacian_symm d.fields d.charts g0 h hsymm) := by
  have hgraph := d.symmetricGeneratorGraph_smoothTensorLaplacian h hsymm
  dsimp only [TensorHilbertNative.Data.SymmetricGeneratorGraph] at hgraph
  have hlap : InGeneratorGraph (V := ↥d.symmetricForm) (H := ↥d.symmetricValue)
      d.symmetricInclusion (d.intoSymmetricValue h hsymm)
      (d.intoSymmetricValue (smoothTensorLaplacian d.fields d.charts g0 h)
        (smoothTensorLaplacian_symm d.fields d.charts g0 h hsymm)) ↔
      ∀ j : d.SymmetricIndex,
        d.symmetricBasis.repr
            (d.intoSymmetricValue (smoothTensorLaplacian d.fields d.charts g0 h)
              (smoothTensorLaplacian_symm d.fields d.charts g0 h hsymm)) j =
          (d.symmetricParameters j : ℝ) *
            d.symmetricBasis.repr (d.intoSymmetricValue h hsymm) j := by
    dsimp only [TensorHilbertNative.Data.symmetricBasis, TensorHilbertNative.Data.symmetricParameters]
    apply inGeneratorGraph_iff_coeff (V := ↥d.symmetricForm) (H := ↥d.symmetricValue)
      d.symmetricInclusion
    all_goals first
      | exact d.symmetricInclusion_compact
      | exact d.symmetricInclusion_denseRange
      | exact d.norm_symmetricInclusion_le_one
  apply lp.ext
  funext i
  have hcoeff := hlap.mp hgraph i
  change d.symmetricBasis.repr
      (d.intoSymmetricValue (smoothTensorLaplacian d.fields d.charts g0 h)
        (smoothTensorLaplacian_symm d.fields d.charts g0 h hsymm)) i =
    (d.symmetricParameters i : ℝ) * d.symmetricBasis.repr (d.intoSymmetricValue h hsymm) i
    at hcoeff
  rw [highGenerator_apply]
  change (d.symmetricParameters i : ℝ) / (1 + (d.symmetricParameters i : ℝ)) *
      (scaleWeight d.symmetricParameters (k + 2) i *
        d.symmetricBasis.repr (d.intoSymmetricValue h hsymm) i) =
    scaleWeight d.symmetricParameters k i * d.symmetricBasis.repr
      (d.intoSymmetricValue (smoothTensorLaplacian d.fields d.charts g0 h)
        (smoothTensorLaplacian_symm d.fields d.charts g0 h hsymm)) i
  rw [hcoeff, scaleWeight_add, scaleWeight_two]
  have hden : 1 + (d.symmetricParameters i : ℝ) ≠ 0 := by positivity
  field_simp

theorem backgroundDifferenceTensor_symm {background g : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background) (B0 : LeviCivitaData g0)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    (smoothRicciDeTurckTensor D B - smoothRicciDeTurckTensor D B0) x v w =
      (smoothRicciDeTurckTensor D B - smoothRicciDeTurckTensor D B0) x w v := by
  change smoothRicciDeTurckTensor D B x v w - smoothRicciDeTurckTensor D B0 x v w =
    smoothRicciDeTurckTensor D B x w v - smoothRicciDeTurckTensor D B0 x w v
  rw [smoothRicciDeTurckTensor_symm D B x v w, smoothRicciDeTurckTensor_symm D B0 x v w]

def backgroundCorrection (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (Psi : BackgroundD r ×
      (NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) (r + 1) ×
        NativeProbeL2 (iota := Fin d.fieldCount) d.charts.measure (2 * r + 1)) →
      ChartSourceTuples (iota := Fin d.fieldCount) A d.charts.measure (2 * r))
    (q : BackgroundD r × StateD) : StateD :=
  evenOutput d r (sourceOutputL2 d.fields A g0 d.charts.measure (2 * r)
    (Psi (q.1, lowInput d L r p hpr hp q.2, traceInput d L r q.2)))

theorem backgroundCorrection_contDiff (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (Psi : BackgroundD r ×
      (NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) (r + 1) ×
        NativeProbeL2 (iota := Fin d.fieldCount) d.charts.measure (2 * r + 1)) →
      ChartSourceTuples (iota := Fin d.fieldCount) A d.charts.measure (2 * r))
    (hPsi : ContDiff ℝ ∞ Psi) :
    ContDiff ℝ ∞ (backgroundCorrection d L A r p hpr hp Psi) := by
  exact (evenOutput d r).contDiff.comp
    ((sourceOutputL2 d.fields A g0 d.charts.measure (2 * r)).contDiff.comp
      (hPsi.comp (contDiff_fst.prodMk
        (((lowInput d L r p hpr hp).contDiff.comp contDiff_snd).prodMk
          ((traceInput d L r).contDiff.comp contDiff_snd)))))

include L A in

theorem exists_native_backgroundCorrection (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ rho : ℝ, 0 < rho ∧
      ∃ Delta : BackgroundD r × StateD → StateD,
        ContDiff ℝ ∞ Delta ∧ (∀ z, Delta (0, z) = 0) ∧
        ∀ QB : BackgroundD r, ‖QB‖ < delta →
          ∀ (background g : RiemannianMetric n M) (D : LeviCivitaData g)
            (B : LeviCivitaData background) (B0 : LeviCivitaData g0)
            (h : SmoothTensor (n := n) (M := M))
            (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v),
          (∀ ab w (hw : w.length ≤ 2 * r + 2) x,
            QB ab (wordIndex w hw) x = directionalWord d.fields w
              (probeDifference d.fields background g0 ab) x) →
          (∀ (x : M) (v w : TangentSpace (𝓡 n) x),
            g.inner x v w = g0.inner x v w + h x v w) →
          ‖d.smoothTensorCoordinates (2 * r + 1) h hsymm‖ ≤ rho →
          Delta (QB, d.smoothTensorCoordinates (2 * r + 1) h hsymm) =
            d.smoothTensorCoordinates (2 * r)
              (smoothRicciDeTurckTensor D B - smoothRicciDeTurckTensor D B0)
              (backgroundDifferenceTensor_symm D B B0) := by
  obtain ⟨delta, hdelta, Psi, hPsi, hPsi0, hPsiEq⟩ :=
    exists_smooth_background_chart_action d.fields g0 d.charts.measure A d.parseval
      (2 * r) (r + 1) (by omega)
  let rho : ℝ := (delta / (‖lowInput d L r p hpr hp‖ + 1)) / 2
  have hden : 0 < ‖lowInput d L r p hpr hp‖ + 1 := by positivity
  have hrho : 0 < rho := half_pos (div_pos hdelta hden)
  have hsmall (z : StateD) (hz : ‖z‖ ≤ rho) : ‖lowInput d L r p hpr hp z‖ < delta := by
    have hzlt : ‖z‖ < delta / (‖lowInput d L r p hpr hp‖ + 1) :=
      hz.trans_lt (half_lt_self (div_pos hdelta hden))
    have hproduct := (lt_div_iff₀ hden).mp hzlt
    have hop := (lowInput d L r p hpr hp).le_opNorm z
    nlinarith [norm_nonneg z]
  refine ⟨delta, hdelta, rho, hrho, backgroundCorrection d L A r p hpr hp Psi,
    backgroundCorrection_contDiff d L A r p hpr hp Psi hPsi, ?_, ?_⟩
  · intro z
    simp only [backgroundCorrection, hPsi0, map_zero]
  · intro QB hQBsmall background g D B B0 h hsymm hQB hmetric hnorm
    let QC := lowInput d L r p hpr hp (d.smoothTensorCoordinates (2 * r + 1) h hsymm)
    let HC := traceInput d L r (d.smoothTensorCoordinates (2 * r + 1) h hsymm)
    have hQC : ∀ ab w (hw : w.length ≤ r + 1) x,
        QC ab (wordIndex w hw) x = directionalWord d.fields w
          (probeDifference d.fields g g0 ab) x := by
      intro ab w hw x
      rw [probeDifference_eq_scalarProbe d g h hmetric ab]
      exact lowInput_smoothTensorCoordinates d L r p hpr hp h hsymm ab w hw x
    have hHC : ∀ ab w (hw : w.length ≤ 2 * r + 1),
        HC ab (wordIndex w hw) =ᵐ[d.charts.measure] directionalWord d.fields w
          (probeDifference d.fields g g0 ab) := by
      intro ab w hw
      rw [probeDifference_eq_scalarProbe d g h hmetric ab]
      exact traceInput_smoothTensorCoordinates d L r h hsymm ab w hw
    have hQ := hPsiEq QB hQBsmall QC (hsmall _ hnorm) HC background g hQB hQC hHC
    apply evenOutput_eq d r _
      (smoothRicciDeTurckTensor D B - smoothRicciDeTurckTensor D B0)
      (backgroundDifferenceTensor_symm D B B0)
    intro ab word hw
    exact backgroundOutput_ae_eq d.fields g0 d.charts.measure A
      (Psi (QB, QC, HC)) background g D B B0 hQ ab word hw

structure NativeParameterData (r : ℕ) where
  coefficient : StateD → StateD →L[ℝ] StateD
  lower : StateD → StateD
  correction : BackgroundD r × StateD → StateD
  coefficient_smooth : ContDiff ℝ ∞ coefficient
  lower_smooth : ContDiff ℝ ∞ lower
  correction_smooth : ContDiff ℝ ∞ correction
  coefficient_zero : coefficient 0 = 0
  correction_zero : ∀ z, correction (0, z) = 0
  radius : ℝ
  radius_pos : 0 < radius
  backgroundRadius : ℝ
  backgroundRadius_pos : 0 < backgroundRadius
  principalConstant : NNReal
  lowerConstant : NNReal
  mixed : LocalMixedBound d.symmetricParameters radius principalConstant lowerConstant
    (fun x => coefficient (shiftedBaseMultiplier d.symmetricParameters x) x +
      lower (shiftedBaseMultiplier d.symmetricParameters x))
  raw_agreement :
    ∀ (g : RiemannianMetric n M) (D : LeviCivitaData g) (B0 : LeviCivitaData g0)
      (h : SmoothTensor (n := n) (M := M))
      (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v),
    (∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = g0.inner x v w + h x v w) →
    ‖d.smoothTensorCoordinates (2 * r + 1) h hsymm‖ ≤ radius →
    coefficient (shiftedBaseMultiplier d.symmetricParameters
        (d.smoothTensorCoordinates (2 * r + 2) h hsymm))
        (d.smoothTensorCoordinates (2 * r + 2) h hsymm) +
      lower (shiftedBaseMultiplier d.symmetricParameters
        (d.smoothTensorCoordinates (2 * r + 2) h hsymm)) =
      d.residualCoordinates (2 * r) D B0 h hsymm
  correction_agreement :
    ∀ QB : BackgroundD r, ‖QB‖ < backgroundRadius →
      ∀ (background g : RiemannianMetric n M) (D : LeviCivitaData g)
        (B : LeviCivitaData background) (B0 : LeviCivitaData g0)
        (h : SmoothTensor (n := n) (M := M))
        (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v),
      (∀ ab w (hw : w.length ≤ 2 * r + 2) x,
        QB ab (wordIndex w hw) x = directionalWord d.fields w
          (probeDifference d.fields background g0 ab) x) →
      (∀ (x : M) (v w : TangentSpace (𝓡 n) x),
        g.inner x v w = g0.inner x v w + h x v w) →
      ‖d.smoothTensorCoordinates (2 * r + 1) h hsymm‖ ≤ radius →
      correction (QB, d.smoothTensorCoordinates (2 * r + 1) h hsymm) =
        d.smoothTensorCoordinates (2 * r)
          (smoothRicciDeTurckTensor D B - smoothRicciDeTurckTensor D B0)
          (backgroundDifferenceTensor_symm D B B0)

include L A in

theorem exists_nativeParameterData (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) {upperRadius : ℝ} (hupper : 0 < upperRadius) :
    ∃ K : NativeParameterData d r, K.radius ≤ upperRadius := by
  obtain ⟨Aop, b, hA, hb, hA0, rho0, hrho0, C, C0, hmix, hEq⟩ :=
    exists_rawResidual d L A r p hpr hp
  obtain ⟨delta, hdelta, rhoD, hrhoD, Delta, hDelta, hDelta0, hDeltaEq⟩ :=
    exists_native_backgroundCorrection d L A r p hpr hp
  let rho : ℝ := min rho0 (min rhoD upperRadius)
  have hrho : 0 < rho := lt_min hrho0 (lt_min hrhoD hupper)
  have hbase : rho ≤ rho0 := min_le_left _ _
  have hcorr : rho ≤ rhoD := (min_le_right _ _).trans (min_le_left _ _)
  have hupp : rho ≤ upperRadius := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨{
    coefficient := Aop
    lower := b
    correction := Delta
    coefficient_smooth := hA
    lower_smooth := hb
    correction_smooth := hDelta
    coefficient_zero := hA0
    correction_zero := hDelta0
    radius := rho
    radius_pos := hrho
    backgroundRadius := delta
    backgroundRadius_pos := hdelta
    principalConstant := C
    lowerConstant := C0
    mixed := fun x y hx hy => hmix x y (hx.trans hbase) (hy.trans hbase)
    raw_agreement := fun g D B0 h hsymm hmetric hsmall =>
      hEq g D B0 h hsymm hmetric (hsmall.trans hbase)
    correction_agreement := fun QB hQB background g D B B0 h hsymm hQ hmetric hsmall =>
      hDeltaEq QB hQB background g D B B0 h hsymm hQ hmetric (hsmall.trans hcorr)
  }, hupp⟩

namespace NativeParameterData

variable {d} {r : ℕ} (K : NativeParameterData d r)

def coefficientMap : C(StateD, StateD →L[ℝ] StateD) :=
  ⟨K.coefficient, K.coefficient_smooth.continuous⟩

def lowerMap : C(StateD, StateD) := ⟨K.lower, K.lower_smooth.continuous⟩

def correctionMap : C(BackgroundD r × StateD, StateD) :=
  ⟨K.correction, K.correction_smooth.continuous⟩

def spatialResidual : SpatialResidual d.symmetricParameters :=
  cutoffSpatialResidual d.symmetricParameters K.radius_pos
    (fun x => K.coefficient (shiftedBaseMultiplier d.symmetricParameters x) x +
      K.lower (shiftedBaseMultiplier d.symmetricParameters x))
    K.principalConstant K.lowerConstant K.mixed

def forcing {T : ℝ} (hT : 0 ≤ T) :
    (BackgroundD r × StateD) × ForcingSpace d.SymmetricIndex T → ForcingSpace d.SymmetricIndex T :=
  parameterForcing d.symmetricParameters K.coefficientMap K.lowerMap K.correctionMap hT

theorem forcingRadius_lt : 2 * K.spatialResidual.forcingRadius < K.radius :=
  cutoffSpatialResidual_forcingRadius d.symmetricParameters K.radius_pos
    (fun x => K.coefficient (shiftedBaseMultiplier d.symmetricParameters x) x +
      K.lower (shiftedBaseMultiplier d.symmetricParameters x))
    K.principalConstant K.lowerConstant K.mixed

theorem spatialResidual_agreement
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (B0 : LeviCivitaData g0)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = g0.inner x v w + h x v w)
    (hsmall : ‖d.smoothTensorCoordinates (2 * r + 1) h hsymm‖ ≤ K.radius) :
    K.spatialResidual.toFun (d.smoothTensorCoordinates (2 * r + 2) h hsymm) =
      d.residualCoordinates (2 * r) D B0 h hsymm := by
  have hJ : shiftedBaseMultiplier d.symmetricParameters
      (d.smoothTensorCoordinates (2 * r + 2) h hsymm) =
      d.smoothTensorCoordinates (2 * r + 1) h hsymm := by
    simpa only [Nat.add_assoc] using
      shiftedBase_smoothTensorCoordinates d (2 * r + 1) h hsymm
  rw [spatialResidual, cutoffSpatialResidual_apply_of_small d.symmetricParameters K.radius_pos
    (fun x => K.coefficient (shiftedBaseMultiplier d.symmetricParameters x) x +
      K.lower (shiftedBaseMultiplier d.symmetricParameters x))
    K.principalConstant K.lowerConstant K.mixed (by rw [hJ]; exact hsmall)]
  exact K.raw_agreement g D B0 h hsymm hmetric hsmall

theorem exists_smooth_fixedPoint :
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧ ∃ F : ForcingSpace d.SymmetricIndex T,
      K.spatialResidual.forcingResidual hT.le F = F ∧
      ‖F‖ ≤ K.spatialResidual.forcingRadius / 3 ∧ ‖F‖ < K.spatialResidual.forcingRadius ∧
      ∃ u : BackgroundD r × StateD → ForcingSpace d.SymmetricIndex T,
        u 0 = F ∧ ContDiffAt ℝ ∞ u 0 ∧
        (∀ᶠ q in 𝓝 0, K.forcing hT.le (q, u q) = u q) ∧
        (∀ᶠ q in 𝓝 (0, F), K.forcing hT.le q = q.2 ↔ u q.1 = q.2) ∧
        (∀ᶠ q in 𝓝 0, ‖u q‖ < K.spatialResidual.forcingRadius) :=
  exists_parameter_fixedPoint d.symmetricParameters K.coefficientMap K.lowerMap K.correctionMap
    K.coefficient_smooth K.lower_smooth K.correction_smooth K.correction_zero
    K.radius_pos K.principalConstant K.lowerConstant K.mixed

end NativeParameterData

end NativeBackground

section Representatives

variable {iota B : Type*} [Countable iota] [NormedAddCommGroup B] [NormedSpace ℝ B]
  {T : ℝ} (lambda : iota → NNReal)

theorem highShift_coe (hT : 0 ≤ T) (kappa : State iota) (F : ForcingSpace iota T) :
    highShift lambda hT (kappa, F) =ᵐ[timeMeasure T]
      fun t => kappa + shiftedHighOperator hT lambda F t := by
  let K : ResponsePath iota T := ContinuousMap.const (Icc (0 : ℝ) T) kappa
  filter_upwards [tracePathL2_ae_eq hT K,
    Lp.coeFn_add (tracePathL2 hT K) (shiftedHighOperator hT lambda F),
    ae_restrict_mem measurableSet_Ioc] with t hK hadd ht
  change (tracePathL2 hT K + shiftedHighOperator hT lambda F) t = _
  rw [hadd, Pi.add_apply, hK ⟨ht.1.le, ht.2⟩]
  rfl

theorem parameterForcing_coe
    (A : C(State iota, State iota →L[ℝ] State iota))
    (b : C(State iota, State iota)) (Delta : C(B × State iota, State iota))
    (hT : 0 ≤ T) (QB : B) (kappa : State iota) (F : ForcingSpace iota T) :
    parameterForcing lambda A b Delta hT ((QB, kappa), F) =ᵐ[timeMeasure T] fun t =>
      A (shiftedBaseMultiplier lambda (kappa + shiftedHighOperator hT lambda F t))
          (kappa + shiftedHighOperator hT lambda F t) +
        b (shiftedBaseMultiplier lambda (kappa + shiftedHighOperator hT lambda F t)) +
        Delta (QB, shiftedBaseMultiplier lambda (kappa + shiftedHighOperator hT lambda F t)) -
        highGenerator lambda kappa := by
  let ev := ContinuousLinearMap.id ℝ (State iota →L[ℝ] State iota)
  let Z := traceShift lambda hT (kappa, F)
  let H := highShift lambda hT (kappa, F)
  let AP := A.comp Z
  let BP := b.comp Z
  let DP := Delta.comp (backgroundTrace lambda hT ((QB, kappa), F))
  let KP : ResponsePath iota T :=
    ContinuousMap.const (Icc (0 : ℝ) T) (highGenerator lambda kappa)
  let top := product hT ev AP H
  let lower := tracePathL2 hT BP
  let correction := tracePathL2 hT DP
  let seed := tracePathL2 hT KP
  filter_upwards [product_ae_eq_on_interval hT ev AP H,
    tracePathL2_ae_eq hT BP, tracePathL2_ae_eq hT DP, tracePathL2_ae_eq hT KP,
    Lp.coeFn_add top lower, Lp.coeFn_add (top + lower) correction,
    Lp.coeFn_sub (top + lower + correction) seed,
    highShift_coe lambda hT kappa F, intermediate_high_eq_trace hT lambda F,
    ae_restrict_mem measurableSet_Ioc]
      with t htop hlower hcorrection hseed hadd hadd' hsub hhigh htrace ht
  have hmem : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hZ : Z ⟨t, hmem⟩ =
      shiftedBaseMultiplier lambda (kappa + shiftedHighOperator hT lambda F t) := by
    change shiftedBaseMultiplier lambda kappa + shiftedTracePath hT lambda F ⟨t, hmem⟩ = _
    rw [map_add, htrace hmem]
  change (top + lower + correction - seed) t = _
  rw [hsub, Pi.sub_apply, hadd', Pi.add_apply, hadd, Pi.add_apply,
    htop hmem, hlower hmem, hcorrection hmem, hseed hmem]
  simp only [AP, BP, DP, KP, ContinuousMap.comp_apply, ContinuousMap.const_apply,
    backgroundTrace_apply]
  change A (Z ⟨t, hmem⟩) (H t) + b (Z ⟨t, hmem⟩) +
    Delta (QB, Z ⟨t, hmem⟩) - highGenerator lambda kappa = _
  rw [hZ, hhigh]

end Representatives

section NativeCombinedSource

open TensorProbeNative TensorHilbertNative NativeChartScalarLocalization DeTurckNative
  DeTurckJetCoordinatesNative DeTurckJetAffineNative DeTurckResidualNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {g0 : RiemannianMetric n M} (d : Data g0)

theorem smoothTensorCoordinates_add_sub (k : ℕ)
    (h1 h2 h3 : SmoothTensor (n := n) (M := M))
    (hsymm1 : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h1 x v w = h1 x w v)
    (hsymm2 : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h2 x v w = h2 x w v)
    (hsymm3 : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h3 x v w = h3 x w v)
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      (h1 + h2 - h3) x v w = (h1 + h2 - h3) x w v) :
    d.smoothTensorCoordinates k (h1 + h2 - h3) hsymm =
      d.smoothTensorCoordinates k h1 hsymm1 + d.smoothTensorCoordinates k h2 hsymm2 -
        d.smoothTensorCoordinates k h3 hsymm3 := by
  have hinto : d.intoSymmetricValue (h1 + h2 - h3) hsymm =
      d.intoSymmetricValue h1 hsymm1 + d.intoSymmetricValue h2 hsymm2 -
        d.intoSymmetricValue h3 hsymm3 := by
    apply Subtype.ext
    change intoTensorL2 d.fields d.charts.measure (h1 + h2 - h3) =
      intoTensorL2 d.fields d.charts.measure h1 + intoTensorL2 d.fields d.charts.measure h2 -
        intoTensorL2 d.fields d.charts.measure h3
    rw [map_sub (intoTensorL2 d.fields d.charts.measure) (h1 + h2) h3,
      map_add (intoTensorL2 d.fields d.charts.measure) h1 h2]
  apply lp.ext
  funext i
  change scaleWeight d.symmetricParameters k i *
      d.symmetricBasis.repr (d.intoSymmetricValue (h1 + h2 - h3) hsymm) i =
    scaleWeight d.symmetricParameters k i * d.symmetricBasis.repr (d.intoSymmetricValue h1 hsymm1) i +
      scaleWeight d.symmetricParameters k i * d.symmetricBasis.repr (d.intoSymmetricValue h2 hsymm2) i -
        scaleWeight d.symmetricParameters k i * d.symmetricBasis.repr (d.intoSymmetricValue h3 hsymm3) i
  rw [hinto, map_sub, map_add]
  simp only [lp.coeFn_sub, lp.coeFn_add, Pi.sub_apply, Pi.add_apply]
  ring

theorem NativeParameterData.rawCorrection_agreement {r : ℕ} (K : NativeParameterData d r)
    (QB : NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) (2 * r + 2))
    (hQBsmall : ‖QB‖ < K.backgroundRadius)
    (background g : RiemannianMetric n M) (D : LeviCivitaData g)
    (B : LeviCivitaData background) (B0 : LeviCivitaData g0)
    (h seed : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (hseed : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), seed x v w = seed x w v)
    (hQB : ∀ ab w (hw : w.length ≤ 2 * r + 2) x,
      QB ab (wordIndex w hw) x = directionalWord d.fields w
        (probeDifference d.fields background g0 ab) x)
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = g0.inner x v w + h x v w)
    (hsmall : ‖d.smoothTensorCoordinates (2 * r + 1) h hsymm‖ ≤ K.radius) :
    K.coefficient (shiftedBaseMultiplier d.symmetricParameters
        (d.smoothTensorCoordinates (2 * r + 2) h hsymm))
        (d.smoothTensorCoordinates (2 * r + 2) h hsymm) +
      K.lower (shiftedBaseMultiplier d.symmetricParameters
        (d.smoothTensorCoordinates (2 * r + 2) h hsymm)) +
      K.correction (QB, shiftedBaseMultiplier d.symmetricParameters
        (d.smoothTensorCoordinates (2 * r + 2) h hsymm)) -
      highGenerator d.symmetricParameters (d.smoothTensorCoordinates (2 * r + 2) seed hseed) =
    d.smoothTensorCoordinates (2 * r)
      (smoothTensorLaplacian d.fields d.charts g0 h + smoothRicciDeTurckTensor D B -
        smoothTensorLaplacian d.fields d.charts g0 seed)
      (fun x v w => by
        change smoothTensorLaplacian d.fields d.charts g0 h x v w +
          smoothRicciDeTurckTensor D B x v w - smoothTensorLaplacian d.fields d.charts g0 seed x v w =
          smoothTensorLaplacian d.fields d.charts g0 h x w v +
          smoothRicciDeTurckTensor D B x w v - smoothTensorLaplacian d.fields d.charts g0 seed x w v
        rw [smoothTensorLaplacian_symm d.fields d.charts g0 h hsymm x v w,
          smoothRicciDeTurckTensor_symm D B x v w,
          smoothTensorLaplacian_symm d.fields d.charts g0 seed hseed x v w]) := by
  have hJ : shiftedBaseMultiplier d.symmetricParameters
      (d.smoothTensorCoordinates (2 * r + 2) h hsymm) =
      d.smoothTensorCoordinates (2 * r + 1) h hsymm := by
    simpa only [Nat.add_assoc] using shiftedBase_smoothTensorCoordinates d (2 * r + 1) h hsymm
  rw [K.raw_agreement g D B0 h hsymm hmetric hsmall, hJ,
    K.correction_agreement QB hQBsmall background g D B B0 h hsymm hQB hmetric hsmall,
    highGenerator_smoothTensorCoordinates d (2 * r) seed hseed]
  let R0 := smoothResidualTensor d.fields d.charts D B0 h
  let SD := smoothRicciDeTurckTensor D B - smoothRicciDeTurckTensor D B0
  let LS := smoothTensorLaplacian d.fields d.charts g0 seed
  have hR0 := smoothResidualTensor_symm d.fields d.charts D B0 h hsymm
  have hSD := backgroundDifferenceTensor_symm D B B0
  have hLS := smoothTensorLaplacian_symm d.fields d.charts g0 seed hseed
  have hsum : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      (R0 + SD - LS) x v w = (R0 + SD - LS) x w v := by
    intro x v w
    change R0 x v w + SD x v w - LS x v w = R0 x w v + SD x w v - LS x w v
    rw [hR0 x v w, hSD x v w, hLS x v w]
  have hcoords := smoothTensorCoordinates_add_sub d (2 * r) R0 SD LS hR0 hSD hLS hsum
  have htensor : R0 + SD - LS = smoothTensorLaplacian d.fields d.charts g0 h +
      smoothRicciDeTurckTensor D B - smoothTensorLaplacian d.fields d.charts g0 seed := by
    apply ContMDiffSection.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    change smoothTensorLaplacian d.fields d.charts g0 h x v w +
      smoothRicciDeTurckTensor D B0 x v w +
      (smoothRicciDeTurckTensor D B x v w - smoothRicciDeTurckTensor D B0 x v w) -
      smoothTensorLaplacian d.fields d.charts g0 seed x v w =
      smoothTensorLaplacian d.fields d.charts g0 h x v w +
      smoothRicciDeTurckTensor D B x v w - smoothTensorLaplacian d.fields d.charts g0 seed x v w
    ring
  simp only [htensor] at hcoords
  simpa only [TensorHilbertNative.Data.residualCoordinates, R0, SD, LS] using hcoords.symm

end NativeCombinedSource

end PoincareConjecture.DeTurckParameterForcingNative

end
