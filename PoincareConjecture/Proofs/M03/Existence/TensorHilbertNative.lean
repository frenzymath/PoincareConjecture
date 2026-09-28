import PoincareConjecture.Proofs.M03.Existence.GlobalParsevalFrameNative
import PoincareConjecture.Proofs.M03.Existence.TensorFirstOrderClosedNative
import PoincareConjecture.Proofs.M03.Existence.NativeTensorRellichNative
import PoincareConjecture.Proofs.M03.Existence.HilbertScaleNative
import PoincareConjecture.Proofs.M03.Existence.NativeTensorLaplacianNative
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.MeasureTheory.Measure.SeparableMeasure

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology Bundle SchwartzMap LineDeriv

universe u

namespace PoincareConjecture.TensorHilbertNative

open TensorProbeNative ChartMeasureNative HilbertResolventNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]

structure Data (g : RiemannianMetric n M) where
  fieldCount : ℕ
  fields : Fin fieldCount → SmoothField (n := n) (M := M)
  parseval : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
    (∑ i, g.inner x (fields i x) v • fields i x) = v
  charts : FiniteChartData (n := n) (M := M)

theorem exists_data (g : RiemannianMetric n M) : Nonempty (Data g) := by
  obtain ⟨k, F, hF⟩ := ParsevalFrameNative.exists_finite_smooth_parseval_fields g
  obtain ⟨d⟩ := exists_finiteChartData (n := n) (M := M)
  exact ⟨⟨k, F, hF, d⟩⟩

def geometry (g : RiemannianMetric n M) : Data g := Classical.choice (exists_data g)

namespace Data

variable {g : RiemannianMetric n M} (d : Data g)
  [MeasurableSpace M] [BorelSpace M]

abbrev Value := tensorL2 d.fields d.charts.measure

abbrev Form := firstOrderGraph d.fields d.charts.measure

def inclusion : d.Form →L[ℝ] d.Value := graphValue d.fields d.charts.measure

theorem inclusion_injective : Function.Injective d.inclusion :=
  graphValue_injective d.fields (fun i : d.charts.centers => i.val) d.charts.weight
    d.charts.measure rfl

theorem inclusion_compact : IsCompactOperator d.inclusion :=
  isCompactOperator_graphValue d.fields g d.parseval d.charts

theorem inclusion_denseRange : DenseRange d.inclusion :=
  graphValue_denseRange d.fields d.charts.measure

theorem norm_inclusion_le_one : ‖d.inclusion‖ ≤ 1 := by
  change ‖graphValue d.fields d.charts.measure‖ ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound
    (E := firstOrderGraph d.fields d.charts.measure)
    (F := tensorL2 d.fields d.charts.measure)
    (graphValue d.fields d.charts.measure) zero_le_one
  intro v
  simpa only [one_mul] using norm_graphValue_le d.fields d.charts.measure v

private theorem projection_denseRange : DenseRange
    (fun x : firstOrderGraph d.fields d.charts.measure =>
      (WithLp.ofLp (x : FirstOrderAmbient d.fields d.charts.measure)).1) := by
  have h := graphValue_denseRange d.fields d.charts.measure
  change DenseRange (fun x : firstOrderGraph d.fields d.charts.measure =>
    (WithLp.ofLp (x : FirstOrderAmbient d.fields d.charts.measure)).1) at h
  exact h

private theorem projection_compact : IsCompactOperator
    (fun x : firstOrderGraph d.fields d.charts.measure =>
      (WithLp.ofLp (x : FirstOrderAmbient d.fields d.charts.measure)).1) := by
  have h := isCompactOperator_graphValue d.fields g d.parseval d.charts
  change IsCompactOperator (fun x : firstOrderGraph d.fields d.charts.measure =>
    (WithLp.ofLp (x : FirstOrderAmbient d.fields d.charts.measure)).1) at h
  exact h

def resolvent : d.Value →L[ℝ] d.Value :=
  operator (V := firstOrderGraph d.fields d.charts.measure)
    (H := tensorL2 d.fields d.charts.measure) (graphValue d.fields d.charts.measure)

theorem resolvent_injective : Function.Injective d.resolvent := by
  dsimp only [resolvent]
  apply operator_injective (V := firstOrderGraph d.fields d.charts.measure)
    (H := tensorL2 d.fields d.charts.measure) (graphValue d.fields d.charts.measure)
  change DenseRange (fun x : firstOrderGraph d.fields d.charts.measure =>
    (WithLp.ofLp (x : FirstOrderAmbient d.fields d.charts.measure)).1)
  exact d.projection_denseRange

abbrev Index := EigenIndex (V := firstOrderGraph d.fields d.charts.measure)
  (H := tensorL2 d.fields d.charts.measure) (graphValue d.fields d.charts.measure)

def basis : HilbertBasis d.Index ℝ d.Value := by
  apply eigenbasis (V := firstOrderGraph d.fields d.charts.measure)
    (H := tensorL2 d.fields d.charts.measure) (graphValue d.fields d.charts.measure)
  · change IsCompactOperator (fun x : firstOrderGraph d.fields d.charts.measure =>
      (WithLp.ofLp (x : FirstOrderAmbient d.fields d.charts.measure)).1)
    exact d.projection_compact
  · change DenseRange (fun x : firstOrderGraph d.fields d.charts.measure =>
      (WithLp.ofLp (x : FirstOrderAmbient d.fields d.charts.measure)).1)
    exact d.projection_denseRange

def parameters : d.Index → NNReal := by
  apply generatorParameters (V := firstOrderGraph d.fields d.charts.measure)
    (H := tensorL2 d.fields d.charts.measure) (graphValue d.fields d.charts.measure)
  · change IsCompactOperator (fun x : firstOrderGraph d.fields d.charts.measure =>
      (WithLp.ofLp (x : FirstOrderAmbient d.fields d.charts.measure)).1)
    exact d.projection_compact
  · change DenseRange (fun x : firstOrderGraph d.fields d.charts.measure =>
      (WithLp.ofLp (x : FirstOrderAmbient d.fields d.charts.measure)).1)
    exact d.projection_denseRange
  · simpa only [inclusion] using d.norm_inclusion_le_one

def GeneratorGraph (v a : d.Value) : Prop :=
  InGeneratorGraph (V := firstOrderGraph d.fields d.charts.measure)
    (H := tensorL2 d.fields d.charts.measure) (graphValue d.fields d.charts.measure) v a

theorem generatorGraph_iff_variational (v a : d.Value) :
    d.GeneratorGraph v a ↔
      ∃ w : d.Form, d.inclusion w = v ∧
        ∀ z : d.Form, inner ℝ z w = inner ℝ (d.inclusion z) (v + a) := by
  simpa only [GeneratorGraph, inclusion] using
    inGeneratorGraph_iff_variational (V := firstOrderGraph d.fields d.charts.measure)
      (H := tensorL2 d.fields d.charts.measure) (graphValue d.fields d.charts.measure) v a

theorem generatorGraph_unique {v a b : d.Value}
    (ha : d.GeneratorGraph v a) (hb : d.GeneratorGraph v b) : a = b := by
  dsimp only [GeneratorGraph] at ha hb
  refine inGeneratorGraph_unique (V := firstOrderGraph d.fields d.charts.measure)
    (H := tensorL2 d.fields d.charts.measure) (graphValue d.fields d.charts.measure) ?_ ha hb
  change DenseRange (fun x : firstOrderGraph d.fields d.charts.measure =>
    (WithLp.ofLp (x : FirstOrderAmbient d.fields d.charts.measure)).1)
  exact d.projection_denseRange

theorem generatorGraph_nonneg {v a : d.Value} (ha : d.GeneratorGraph v a) :
    0 ≤ inner ℝ v a := by
  dsimp only [GeneratorGraph] at ha
  exact inGeneratorGraph_nonneg (V := firstOrderGraph d.fields d.charts.measure)
    (H := tensorL2 d.fields d.charts.measure) (graphValue d.fields d.charts.measure)
    (by simpa only [inclusion] using d.norm_inclusion_le_one) ha

variable [SecondCountableTopology M]

instance value_separable : TopologicalSpace.SeparableSpace d.Value := by
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology
      (Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure) := inferInstance
  infer_instance

instance index_countable : Countable d.Index := by
  apply eigenIndex_countable (V := firstOrderGraph d.fields d.charts.measure)
    (H := tensorL2 d.fields d.charts.measure) (graphValue d.fields d.charts.measure)
  change IsCompactOperator (fun x : firstOrderGraph d.fields d.charts.measure =>
    (WithLp.ofLp (x : FirstOrderAmbient d.fields d.charts.measure)).1)
  exact d.projection_compact

theorem exists_response {T : ℝ} (hT : 0 ≤ T) {F : ℝ → d.Value}
    (hF : MemLp F 2 (SpectralHeatNative.timeMeasure T)) :
    ∃ U D G : ℝ → d.Value,
      U 0 = 0 ∧ ContinuousOn U (Icc (0 : ℝ) T) ∧
      MemLp D 2 (SpectralHeatNative.timeMeasure T) ∧
      MemLp G 2 (SpectralHeatNative.timeMeasure T) ∧
      (∀ᵐ t ∂SpectralHeatNative.timeMeasure T, HasDerivAt U (D t) t) ∧
      (∀ᵐ t ∂SpectralHeatNative.timeMeasure T, D t + G t = F t) ∧
      (∀ᵐ t ∂SpectralHeatNative.timeMeasure T, d.GeneratorGraph (U t) (G t)) ∧
      (∫ t, ‖D t‖ ^ 2 ∂SpectralHeatNative.timeMeasure T) +
          (∫ t, ‖G t‖ ^ 2 ∂SpectralHeatNative.timeMeasure T) ≤
        ∫ t, ‖F t‖ ^ 2 ∂SpectralHeatNative.timeMeasure T := by
  dsimp only [GeneratorGraph]
  apply HilbertResolventNative.exists_response (V := firstOrderGraph d.fields d.charts.measure)
    (H := tensorL2 d.fields d.charts.measure) (graphValue d.fields d.charts.measure)
  · change IsCompactOperator (fun x : firstOrderGraph d.fields d.charts.measure =>
      (WithLp.ofLp (x : FirstOrderAmbient d.fields d.charts.measure)).1)
    exact d.projection_compact
  · change DenseRange (fun x : firstOrderGraph d.fields d.charts.measure =>
      (WithLp.ofLp (x : FirstOrderAmbient d.fields d.charts.measure)).1)
    exact d.projection_denseRange
  · simpa only [inclusion] using d.norm_inclusion_le_one
  · exact hT
  · exact hF

end Data

section CoefficientAction

variable [MeasurableSpace M] [BorelSpace M]
  {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (μ : Measure M) (A : C(M, E →L[ℝ] V))

theorem coefficientAction_memLp {f : M → E} (hf : MemLp f 2 μ) :
    MemLp (fun x => A x (f x)) 2 μ := by
  have hcont : Continuous (fun p : (E →L[ℝ] V) × E => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hA : AEStronglyMeasurable A μ :=
    (A.continuous.stronglyMeasurable_of_hasCompactSupport
      (isClosed_tsupport _).isCompact).aestronglyMeasurable
  apply hf.of_le_mul
    (hcont.comp_aestronglyMeasurable (hA.prodMk hf.aestronglyMeasurable))
  exact Eventually.of_forall (fun x =>
    ((A x).le_opNorm (f x)).trans
      (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm x) (norm_nonneg (f x))))

def coefficientActionFun (f : Lp E 2 μ) : Lp V 2 μ :=
  (coefficientAction_memLp μ A (Lp.memLp f)).toLp (fun x => A x (f x))

theorem coefficientActionFun_coe (f : Lp E 2 μ) :
    coefficientActionFun μ A f =ᵐ[μ] (fun x => A x (f x)) :=
  (coefficientAction_memLp μ A (Lp.memLp f)).coeFn_toLp

theorem norm_coefficientActionFun_le (f : Lp E 2 μ) :
    ‖coefficientActionFun μ A f‖ ≤ ‖A‖ * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coefficientActionFun_coe μ A f] with x hx
  rw [hx]
  exact ((A x).le_opNorm (f x)).trans
    (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm x) (norm_nonneg (f x)))

def coefficientActionLinear : Lp E 2 μ →ₗ[ℝ] Lp V 2 μ where
  toFun := coefficientActionFun μ A
  map_add' f h := by
    apply Lp.ext
    filter_upwards [coefficientActionFun_coe μ A (f + h),
      coefficientActionFun_coe μ A f, coefficientActionFun_coe μ A h,
      Lp.coeFn_add f h,
      Lp.coeFn_add (coefficientActionFun μ A f) (coefficientActionFun μ A h)]
      with x hsum hf hh hin hout
    simp only [hsum, hout, Pi.add_apply, hf, hh, hin, map_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [coefficientActionFun_coe μ A (c • f),
      coefficientActionFun_coe μ A f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (coefficientActionFun μ A f)] with x hcf hf hin hout
    simp only [RingHom.id_apply, hcf, hout, Pi.smul_apply, hf, hin, map_smul]

def coefficientAction : Lp E 2 μ →L[ℝ] Lp V 2 μ :=
  (coefficientActionLinear μ A).mkContinuous ‖A‖ (norm_coefficientActionFun_le μ A)

theorem coefficientAction_coe (f : Lp E 2 μ) :
    coefficientAction μ A f =ᵐ[μ] (fun x => A x (f x)) :=
  coefficientActionFun_coe μ A f

theorem norm_coefficientAction_le : ‖coefficientAction μ A‖ ≤ ‖A‖ :=
  (coefficientActionLinear μ A).mkContinuous_norm_le (norm_nonneg A)
    (norm_coefficientActionFun_le μ A)

end CoefficientAction

namespace Data

open ParsevalTensorNative

variable {g : RiemannianMetric n M} (d : Data g)
  [MeasurableSpace M] [BorelSpace M]

abbrev ProbeIndex := Fin d.fieldCount × Fin d.fieldCount

def derivative : d.Form →L[ℝ] Lp (DerivativeCoefficients (Fin d.fieldCount)) 2 d.charts.measure :=
  (WithLp.sndL 2 ℝ d.Value
    (Lp (DerivativeCoefficients (Fin d.fieldCount)) 2 d.charts.measure)).comp
      (firstOrderGraph d.fields d.charts.measure).subtypeL

@[simp] theorem derivative_into (h : SmoothTensor (n := n) (M := M)) :
    d.derivative (intoFirstOrderGraph d.fields d.charts.measure h) =
      derivativeToLp d.fields d.charts.measure h := rfl

def valueCoefficient (ab : d.ProbeIndex) : d.Value →L[ℝ] Lp ℝ 2 d.charts.measure :=
  (coefficientL2 d.charts.measure ab).comp (tensorL2 d.fields d.charts.measure).subtypeL

def derivativeCoefficient (i : Fin d.fieldCount) (ab : d.ProbeIndex) :
    d.Form →L[ℝ] Lp ℝ 2 d.charts.measure :=
  (coefficientL2 d.charts.measure (i, ab)).comp d.derivative

def projectionValueCoefficient (ab : d.ProbeIndex) :
    C(M, Coefficients (Fin d.fieldCount) →L[ℝ] ℝ) where
  toFun x := ∑ cd : d.ProbeIndex,
    scalarLaplacian d.fields d.charts (fun y => projectionKernel g d.fields y ab cd) x •
      EuclideanSpace.proj cd
  continuous_toFun := by
    apply continuous_finset_sum
    intro cd _
    exact ((scalarLaplacian_contMDiff d.fields d.charts
      (projectionKernel_contMDiff d.fields g ab cd)).continuous).smul continuous_const

def projectionDerivativeCoefficient (ab : d.ProbeIndex) :
    C(M, DerivativeCoefficients (Fin d.fieldCount) →L[ℝ] ℝ) where
  toFun x := (-2 : ℝ) • ∑ cd : d.ProbeIndex, ∑ i : Fin d.fieldCount,
    scalarDirectional (d.fields i) (fun y => projectionKernel g d.fields y ab cd) x •
      EuclideanSpace.proj (i, cd)
  continuous_toFun := by
    have hsum : Continuous (fun x : M => ∑ cd : d.ProbeIndex, ∑ i : Fin d.fieldCount,
        scalarDirectional (d.fields i) (fun y => projectionKernel g d.fields y ab cd) x •
          (EuclideanSpace.proj (i, cd) : DerivativeCoefficients (Fin d.fieldCount) →L[ℝ] ℝ)) := by
      apply continuous_finset_sum
      intro cd _
      apply continuous_finset_sum
      intro i _
      exact ((contMDiff_directional (projectionKernel_contMDiff d.fields g ab cd)
        (d.fields i)).continuous).smul continuous_const
    exact hsum.const_smul (-2 : ℝ)

theorem projectionCoefficients_apply (ab : d.ProbeIndex) (x : M)
    (q : Coefficients (Fin d.fieldCount)) (dq : DerivativeCoefficients (Fin d.fieldCount)) :
    d.projectionValueCoefficient ab x q + d.projectionDerivativeCoefficient ab x dq =
      projectionLowerSource d.fields d.charts g x q dq ab := by
  simp only [projectionValueCoefficient, projectionDerivativeCoefficient,
    ContinuousMap.coe_mk, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, EuclideanSpace.coe_proj, smul_eq_mul,
    projectionLowerSource]
  have hval :
      (∑ cd : d.ProbeIndex, scalarLaplacian d.fields d.charts
        (fun y => projectionKernel g d.fields y ab cd) x * q cd) =
      ∑ cd : d.ProbeIndex, q cd * scalarLaplacian d.fields d.charts
        (fun y => projectionKernel g d.fields y ab cd) x :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [hval]
  ring

def lowerSource (ab : d.ProbeIndex) : d.Form →L[ℝ] Lp ℝ 2 d.charts.measure :=
  (coefficientAction d.charts.measure (d.projectionValueCoefficient ab)).comp
      ((tensorL2 d.fields d.charts.measure).subtypeL.comp d.inclusion) +
    (coefficientAction d.charts.measure (d.projectionDerivativeCoefficient ab)).comp d.derivative

theorem lowerSource_coe (ab : d.ProbeIndex) (z : d.Form) :
    d.lowerSource ab z =ᵐ[d.charts.measure] (fun x =>
      projectionLowerSource d.fields d.charts g x
        ((d.inclusion z : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure) x)
        (d.derivative z x) ab) := by
  filter_upwards [coefficientAction_coe d.charts.measure (d.projectionValueCoefficient ab)
      (d.inclusion z : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure),
    coefficientAction_coe d.charts.measure (d.projectionDerivativeCoefficient ab) (d.derivative z),
    Lp.coeFn_add
      (coefficientAction d.charts.measure (d.projectionValueCoefficient ab)
        (d.inclusion z : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure))
      (coefficientAction d.charts.measure (d.projectionDerivativeCoefficient ab) (d.derivative z))]
    with x hval hderiv hadd
  change (coefficientAction d.charts.measure (d.projectionValueCoefficient ab)
      (d.inclusion z : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure) +
    coefficientAction d.charts.measure (d.projectionDerivativeCoefficient ab) (d.derivative z)) x = _
  rw [hadd, Pi.add_apply, hval, hderiv]
  exact d.projectionCoefficients_apply ab x _ _

theorem lowerSource_into_coe (ab : d.ProbeIndex) (h : SmoothTensor (n := n) (M := M)) :
    d.lowerSource ab (intoFirstOrderGraph d.fields d.charts.measure h) =ᵐ[d.charts.measure]
      (fun x => projectionLowerSource d.fields d.charts g x
        (probes d.fields h x) (derivativeProbes d.fields h x) ab) := by
  filter_upwards [d.lowerSource_coe ab (intoFirstOrderGraph d.fields d.charts.measure h),
    tensorToLp_coe d.fields d.charts.measure h,
    derivativeToLp_coe d.fields d.charts.measure h] with x hx hval hderiv
  rw [hx]
  change projectionLowerSource d.fields d.charts g x
    (tensorToLp d.fields d.charts.measure h x) (derivativeToLp d.fields d.charts.measure h x) ab = _
  rw [hval, hderiv]

def scalarLp (f : M → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    Lp ℝ 2 d.charts.measure :=
  ContinuousMap.toLp 2 d.charts.measure ℝ ⟨f, hf.continuous⟩

theorem scalarLp_coe (f : M → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    d.scalarLp f hf =ᵐ[d.charts.measure] f :=
  ContinuousMap.coeFn_toLp (p := (2 : ENNReal)) (𝕜 := ℝ) d.charts.measure ⟨f, hf.continuous⟩

theorem valueCoefficient_coe (ab : d.ProbeIndex) (v : d.Value) :
    d.valueCoefficient ab v =ᵐ[d.charts.measure] fun x =>
      (v : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure) x ab :=
  coefficientL2_coe d.charts.measure ab _

theorem valueCoefficient_into_coe (ab : d.ProbeIndex)
    (h : SmoothTensor (n := n) (M := M)) :
    d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure h) =ᵐ[d.charts.measure]
      scalarProbe d.fields h ab := by
  filter_upwards [d.valueCoefficient_coe ab (intoTensorL2 d.fields d.charts.measure h),
    tensorToLp_coe d.fields d.charts.measure h] with x hx hh
  rw [hx]
  change tensorToLp d.fields d.charts.measure h x ab = _
  rw [hh]
  rfl

def scalarTest (ab : d.ProbeIndex) (η : M → ℝ)
    (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η) : SmoothTensor (n := n) (M := M) :=
  smoothDecode g d.fields (fun x => η x • EuclideanSpace.basisFun d.ProbeIndex ℝ ab)
    (fun cd => by
      change ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun x => η x * EuclideanSpace.basisFun d.ProbeIndex ℝ ab cd)
      exact hη.mul contMDiff_const)

theorem probes_scalarTest (ab : d.ProbeIndex) (η : M → ℝ)
    (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η) (x : M) :
    probes d.fields (d.scalarTest ab η hη) x =
      nativeProjection g d.fields x (η x • EuclideanSpace.basisFun d.ProbeIndex ℝ ab) :=
  probes_smoothDecode g d.fields _ _ x

theorem scalarTest_pairing (ab : d.ProbeIndex) (η : M → ℝ)
    (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η) (v : d.Value) :
    inner ℝ (intoTensorL2 d.fields d.charts.measure (d.scalarTest ab η hη)) v =
      inner ℝ (d.scalarLp η hη) (d.valueCoefficient ab v) := by
  have hproj := projectionL2_coe g d.fields d.parseval d.charts.measure
    (v : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure)
  rw [projectionL2_eq_self_of_mem_tensorL2 g d.fields d.parseval d.charts.measure v.property]
    at hproj
  change inner ℝ (tensorToLp d.fields d.charts.measure (d.scalarTest ab η hη))
    (v : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure) = _
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [tensorToLp_coe d.fields d.charts.measure (d.scalarTest ab η hη),
    d.scalarLp_coe η hη, d.valueCoefficient_coe ab v, hproj] with x htest heta hval hp
  rw [htest, d.probes_scalarTest ab η hη x, nativeProjection_selfadjoint, ← hp,
    heta, hval, real_inner_smul_left, EuclideanSpace.basisFun_inner, Real.inner_apply]

theorem scalarLaplacian_pairing_symmetric {f η : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η) :
    (∫ x, scalarLaplacian d.fields d.charts η x * f x ∂d.charts.measure) =
      ∫ x, η x * scalarLaplacian d.fields d.charts f x ∂d.charts.measure := by
  calc
    _ = ∫ x, f x * scalarLaplacian d.fields d.charts η x ∂d.charts.measure := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => mul_comm _ _)
    _ = ∫ x, ∑ i, scalarDirectional (d.fields i) f x *
        scalarDirectional (d.fields i) η x ∂d.charts.measure :=
      (integral_scalarLaplacian_pairing d.fields d.charts hf hη).symm
    _ = ∫ x, ∑ i, scalarDirectional (d.fields i) η x *
        scalarDirectional (d.fields i) f x ∂d.charts.measure := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => Finset.sum_congr rfl (fun _ _ => mul_comm _ _))
    _ = _ := integral_scalarLaplacian_pairing d.fields d.charts hη hf

theorem scalarLaplacian_smooth_pairing (ab : d.ProbeIndex) (η : M → ℝ)
    (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η) (h : SmoothTensor (n := n) (M := M)) :
    inner ℝ
      (d.scalarLp (scalarLaplacian d.fields d.charts η)
        (scalarLaplacian_contMDiff d.fields d.charts hη))
      (d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure h)) =
    inner ℝ (d.scalarLp η hη)
      (d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure
        (smoothTensorLaplacian d.fields d.charts g h)) +
          d.lowerSource ab (intoFirstOrderGraph d.fields d.charts.measure h)) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x, scalarLaplacian d.fields d.charts η x * scalarProbe d.fields h ab x
        ∂d.charts.measure := by
      apply integral_congr_ae
      filter_upwards [d.scalarLp_coe (scalarLaplacian d.fields d.charts η)
        (scalarLaplacian_contMDiff d.fields d.charts hη),
        d.valueCoefficient_into_coe ab h] with x heta hh
      rw [heta, hh, Real.inner_apply]
    _ = ∫ x, η x * scalarLaplacian d.fields d.charts (scalarProbe d.fields h ab) x
        ∂d.charts.measure :=
      d.scalarLaplacian_pairing_symmetric (scalarProbe_contMDiff d.fields h ab) hη
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [d.scalarLp_coe η hη,
        d.valueCoefficient_into_coe ab (smoothTensorLaplacian d.fields d.charts g h),
        d.lowerSource_into_coe ab h,
        Lp.coeFn_add
          (d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure
            (smoothTensorLaplacian d.fields d.charts g h)))
          (d.lowerSource ab (intoFirstOrderGraph d.fields d.charts.measure h))]
        with x heta hvalue hsource hadd
      rw [hadd, Pi.add_apply, heta, hvalue, hsource, Real.inner_apply,
        scalarLaplacian_probe_eq d.fields d.charts g d.parseval h ab x]
      rfl

theorem scalarLaplacian_form_pairing (ab : d.ProbeIndex) (η : M → ℝ)
    (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η) (z : d.Form) :
    inner ℝ
      (d.scalarLp (scalarLaplacian d.fields d.charts η)
        (scalarLaplacian_contMDiff d.fields d.charts hη))
      (d.valueCoefficient ab (d.inclusion z)) =
    inner ℝ (intoFirstOrderGraph d.fields d.charts.measure (d.scalarTest ab η hη)) z -
      inner ℝ (intoTensorL2 d.fields d.charts.measure (d.scalarTest ab η hη)) (d.inclusion z) +
        inner ℝ (d.scalarLp η hη) (d.lowerSource ab z) := by
  have heq :
      (fun z : d.Form => inner ℝ
        (d.scalarLp (scalarLaplacian d.fields d.charts η)
          (scalarLaplacian_contMDiff d.fields d.charts hη))
        (d.valueCoefficient ab (d.inclusion z))) =
      (fun z : d.Form =>
        inner ℝ (intoFirstOrderGraph d.fields d.charts.measure (d.scalarTest ab η hη)) z -
          inner ℝ (intoTensorL2 d.fields d.charts.measure (d.scalarTest ab η hη)) (d.inclusion z) +
            inner ℝ (d.scalarLp η hη) (d.lowerSource ab z)) := by
    apply (intoFirstOrderGraph_denseRange d.fields d.charts.measure).equalizer
      (continuous_const.inner ((d.valueCoefficient ab).continuous.comp d.inclusion.continuous))
      (((continuous_const.inner continuous_id).sub
        (continuous_const.inner d.inclusion.continuous)).add
          (continuous_const.inner (d.lowerSource ab).continuous))
    funext h
    simp only [Function.comp_apply]
    change inner ℝ
      (d.scalarLp (scalarLaplacian d.fields d.charts η)
        (scalarLaplacian_contMDiff d.fields d.charts hη))
      (d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure h)) = _
    rw [d.scalarLaplacian_smooth_pairing ab η hη h, inner_add_right]
    have hform := form_pairing_laplacian d.fields d.charts g d.parseval h
      (intoFirstOrderGraph d.fields d.charts.measure (d.scalarTest ab η hη))
    rw [graphValue_into, inner_add_right, d.scalarTest_pairing] at hform
    rw [d.scalarTest_pairing] at hform
    change _ = inner ℝ
      (intoFirstOrderGraph d.fields d.charts.measure (d.scalarTest ab η hη))
      (intoFirstOrderGraph d.fields d.charts.measure h) -
        inner ℝ (intoTensorL2 d.fields d.charts.measure (d.scalarTest ab η hη))
          (intoTensorL2 d.fields d.charts.measure h) + _
    rw [d.scalarTest_pairing]
    linarith only [hform]
  exact congrFun heq z

theorem generatorGraph_scalar_weak {u a : d.Value} (ha : d.GeneratorGraph u a) :
    ∃ z : d.Form, d.inclusion z = u ∧
      ∀ (ab : d.ProbeIndex) (η : M → ℝ) (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η),
        inner ℝ
          (d.scalarLp (scalarLaplacian d.fields d.charts η)
            (scalarLaplacian_contMDiff d.fields d.charts hη))
          (d.valueCoefficient ab u) =
        inner ℝ (d.scalarLp η hη) (d.valueCoefficient ab a + d.lowerSource ab z) := by
  obtain ⟨z, hz, hform⟩ := (d.generatorGraph_iff_variational u a).mp ha
  refine ⟨z, hz, ?_⟩
  intro ab η hη
  have hweak := d.scalarLaplacian_form_pairing ab η hη z
  have htest := hform (intoFirstOrderGraph d.fields d.charts.measure (d.scalarTest ab η hη))
  change inner ℝ (intoFirstOrderGraph d.fields d.charts.measure (d.scalarTest ab η hη)) z =
    inner ℝ (intoTensorL2 d.fields d.charts.measure (d.scalarTest ab η hη)) (u + a) at htest
  rw [inner_add_right] at htest
  rw [hz, htest] at hweak
  rw [add_sub_cancel_left, d.scalarTest_pairing, ← inner_add_right] at hweak
  exact hweak

theorem derivativeCoefficient_coe (i : Fin d.fieldCount) (ab : d.ProbeIndex) (z : d.Form) :
    d.derivativeCoefficient i ab z =ᵐ[d.charts.measure] fun x => d.derivative z x (i, ab) :=
  coefficientL2_coe d.charts.measure (i, ab) _

theorem derivativeCoefficient_into_coe (i : Fin d.fieldCount) (ab : d.ProbeIndex)
    (h : SmoothTensor (n := n) (M := M)) :
    d.derivativeCoefficient i ab (intoFirstOrderGraph d.fields d.charts.measure h)
      =ᵐ[d.charts.measure] scalarDirectional (d.fields i) (scalarProbe d.fields h ab) := by
  filter_upwards [d.derivativeCoefficient_coe i ab (intoFirstOrderGraph d.fields d.charts.measure h),
    derivativeToLp_coe d.fields d.charts.measure h] with x hx hh
  rw [hx]
  change derivativeToLp d.fields d.charts.measure h x (i, ab) = _
  rw [hh]
  rfl

theorem directional_form_pairing (i : Fin d.fieldCount) (ab : d.ProbeIndex)
    (η : M → ℝ) (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η) (z : d.Form) :
    inner ℝ
      (d.scalarLp (d.charts.fieldAdjoint (d.fields i) η)
        (d.charts.fieldAdjoint_contMDiff (d.fields i) hη))
      (d.valueCoefficient ab (d.inclusion z)) =
    inner ℝ (d.scalarLp η hη) (d.derivativeCoefficient i ab z) := by
  have heq :
      (fun z : d.Form => inner ℝ
        (d.scalarLp (d.charts.fieldAdjoint (d.fields i) η)
          (d.charts.fieldAdjoint_contMDiff (d.fields i) hη))
        (d.valueCoefficient ab (d.inclusion z))) =
      (fun z : d.Form => inner ℝ (d.scalarLp η hη) (d.derivativeCoefficient i ab z)) := by
    apply (intoFirstOrderGraph_denseRange d.fields d.charts.measure).equalizer
      (continuous_const.inner ((d.valueCoefficient ab).continuous.comp d.inclusion.continuous))
      (continuous_const.inner (d.derivativeCoefficient i ab).continuous)
    funext h
    simp only [Function.comp_apply]
    change inner ℝ
      (d.scalarLp (d.charts.fieldAdjoint (d.fields i) η)
        (d.charts.fieldAdjoint_contMDiff (d.fields i) hη))
      (d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure h)) = _
    rw [L2.inner_def, L2.inner_def]
    calc
      _ = ∫ x, scalarProbe d.fields h ab x * d.charts.fieldAdjoint (d.fields i) η x
          ∂d.charts.measure := by
        apply integral_congr_ae
        filter_upwards [d.scalarLp_coe (d.charts.fieldAdjoint (d.fields i) η)
          (d.charts.fieldAdjoint_contMDiff (d.fields i) hη),
          d.valueCoefficient_into_coe ab h] with x heta hh
        rw [heta, hh, Real.inner_apply, mul_comm]
      _ = ∫ x, scalarDirectional (d.fields i) (scalarProbe d.fields h ab) x * η x
          ∂d.charts.measure :=
        (d.charts.integral_directional_eq_adjoint (d.fields i)
          (scalarProbe_contMDiff d.fields h ab) hη).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [d.scalarLp_coe η hη, d.derivativeCoefficient_into_coe i ab h]
          with x heta hh
        rw [heta, hh, Real.inner_apply, mul_comm]
  exact congrFun heq z

theorem norm_form_le_of_variational {u a : d.Value} {z : d.Form}
    (hz : d.inclusion z = u)
    (hform : ∀ w : d.Form, inner ℝ w z = inner ℝ (d.inclusion w) (u + a)) :
    ‖z‖ ≤ ‖u‖ + ‖a‖ := by
  have hzsq := hform z
  rw [hz, real_inner_self_eq_norm_sq] at hzsq
  have hb : ‖z‖ ^ 2 ≤ (‖u‖ + ‖a‖) ^ 2 := by
    calc
      _ = inner ℝ u (u + a) := hzsq
      _ ≤ ‖u‖ * ‖u + a‖ := real_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖u‖ + ‖a‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le u a) (norm_nonneg u)
      _ ≤ (‖u‖ + ‖a‖) ^ 2 := by
        nlinarith [norm_nonneg u, norm_nonneg a]
  exact (sq_le_sq₀ (norm_nonneg z) (add_nonneg (norm_nonneg u) (norm_nonneg a))).mp hb

theorem generatorGraph_scalar_equations {u a : d.Value} (ha : d.GeneratorGraph u a) :
    ∃ z : d.Form, d.inclusion z = u ∧ ‖z‖ ≤ ‖u‖ + ‖a‖ ∧
      (∀ ab : d.ProbeIndex, ‖d.lowerSource ab z‖ ≤ ‖d.lowerSource ab‖ * (‖u‖ + ‖a‖)) ∧
      (∀ (i : Fin d.fieldCount) (ab : d.ProbeIndex) (η : M → ℝ)
          (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η),
        inner ℝ
          (d.scalarLp (d.charts.fieldAdjoint (d.fields i) η)
            (d.charts.fieldAdjoint_contMDiff (d.fields i) hη))
          (d.valueCoefficient ab u) =
        inner ℝ (d.scalarLp η hη) (d.derivativeCoefficient i ab z)) ∧
      (∀ (ab : d.ProbeIndex) (η : M → ℝ) (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η),
        inner ℝ
          (d.scalarLp (scalarLaplacian d.fields d.charts η)
            (scalarLaplacian_contMDiff d.fields d.charts hη))
          (d.valueCoefficient ab u) =
        inner ℝ (d.scalarLp η hη) (d.valueCoefficient ab a + d.lowerSource ab z)) := by
  obtain ⟨z, hz, hform⟩ := (d.generatorGraph_iff_variational u a).mp ha
  have hnorm := d.norm_form_le_of_variational hz hform
  refine ⟨z, hz, hnorm, ?_, ?_, ?_⟩
  · intro ab
    exact ((d.lowerSource ab).le_opNorm z).trans
      (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
  · intro i ab η hη
    simpa only [hz] using d.directional_form_pairing i ab η hη z
  · obtain ⟨w, hw, hweak⟩ := d.generatorGraph_scalar_weak ha
    have heq : w = z := d.inclusion_injective (hw.trans hz.symm)
    simpa only [heq] using hweak

section LocalFirstOrder

open NativeChartScalarLocalization NativeChartGradientEnergyNative
  EuclideanMollificationNative LpFiniteCoordinatesNative LineDeriv

local notation "ModelE" => EuclideanSpace ℝ (Fin n)

variable (L : FiniteChartLocalizationData d.charts) (a : L.patches) (ab : d.ProbeIndex)

def localizedSchwartz : SmoothTensor (n := n) (M := M) →ₗ[ℝ] 𝓢(ModelE, ℝ) where
  toFun h :=
    (chartScalar_compactSupport a.val.1.val (L.weight_compactSupport a)
      (L.weight_support_source a) (L.localizedProduct_zero a (scalarProbe d.fields h ab))).toSchwartzMap
        (contDiff_chartScalar a.val.1.val
          ((L.weight_smooth a).mul (scalarProbe_contMDiff d.fields h ab))
          (L.weight_compactSupport a) (L.weight_support_source a)
          (L.localizedProduct_zero a (scalarProbe d.fields h ab)))
  map_add' h k := by
    ext z
    change chartScalar a.val.1.val
        (fun x => L.weight a x * scalarProbe d.fields (h + k) ab x) z =
      chartScalar a.val.1.val (fun x => L.weight a x * scalarProbe d.fields h ab x) z +
        chartScalar a.val.1.val (fun x => L.weight a x * scalarProbe d.fields k ab x) z
    by_cases hz : z ∈ (chartAt ModelE a.val.1.val).target
    · simp only [chartScalar_of_mem _ _ hz]
      change L.weight a _ * (scalarProbe d.fields h ab _ + scalarProbe d.fields k ab _) = _
      exact mul_add _ _ _
    · simp only [chartScalar_of_notMem _ _ hz, zero_add]
  map_smul' c h := by
    ext z
    change chartScalar a.val.1.val
        (fun x => L.weight a x * scalarProbe d.fields (c • h) ab x) z =
      c * chartScalar a.val.1.val (fun x => L.weight a x * scalarProbe d.fields h ab x) z
    by_cases hz : z ∈ (chartAt ModelE a.val.1.val).target
    · simp only [chartScalar_of_mem _ _ hz]
      change L.weight a _ * (c * scalarProbe d.fields h ab _) = _
      ring
    · simp only [chartScalar_of_notMem _ _ hz, mul_zero]

@[simp] theorem localizedSchwartz_apply (h : SmoothTensor (n := n) (M := M)) (x : ModelE) :
    d.localizedSchwartz L a ab h x =
      chartScalar a.val.1.val (fun y => L.weight a y * scalarProbe d.fields h ab y) x := rfl

def localizedDerivativeCore (j : Fin n) :
    SmoothTensor (n := n) (M := M) →ₗ[ℝ] Lp ℝ 2 (volume : Measure ModelE) :=
  (SchwartzMap.toLpCLM ℝ ℝ 2 volume).toLinearMap.comp
    ((lineDerivOpCLM ℝ 𝓢(ModelE, ℝ) (EuclideanSpace.single j (1 : ℝ))).toLinearMap.comp
      (d.localizedSchwartz L a ab))

theorem localizedDerivativeCore_norm_sq (j : Fin n) (h : SmoothTensor (n := n) (M := M)) :
    ‖d.localizedDerivativeCore L a ab j h‖ ^ 2 =
      ∫ x, (fderiv ℝ (d.localizedSchwartz L a ab h) x (EuclideanSpace.single j (1 : ℝ))) ^ 2 := by
  rw [l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [(∂_{EuclideanSpace.single j (1 : ℝ)} (d.localizedSchwartz L a ab h)).coeFn_toLp
    2 volume] with x hx
  change ‖(∂_{EuclideanSpace.single j (1 : ℝ)} (d.localizedSchwartz L a ab h)).toLp 2 volume x‖ ^ 2 = _
  rw [hx, SchwartzMap.lineDerivOp_apply_eq_fderiv, Real.norm_eq_abs, sq_abs]

theorem exists_localizedDerivativeCore_bound (j : Fin n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : SmoothTensor (n := n) (M := M),
      ‖d.localizedDerivativeCore L a ab j h‖ ≤
        C * ‖intoFirstOrderGraph d.fields d.charts.measure h‖ := by
  obtain ⟨C, hC, hgradient⟩ := exists_cutoff_chart_gradientEnergy_bound g d.fields d.parseval
    a.val.1.val (L.weight_smooth a)
    (fun x => by rw [abs_of_nonneg (L.weight_nonneg a x)]; exact L.weight_le_one a x)
    (L.weight_compactSupport a) (L.weight_support_source a)
    (L.weight_zero_off_support a) (L.region_open a).measurableSet
    (L.region_subset_target a) (L.supportImage_subset_region a)
    (L.lowerConstant_pos a) (L.region_measure_lower a)
  refine ⟨C + 1, by linarith, ?_⟩
  intro h
  let hf := pairing_memLp d.fields d.charts.measure h ab.1 ab.2
  let hDf := fun i => directional_pairing_memLp d.fields d.charts.measure h i ab.1 ab.2
  have hcoord : ‖d.localizedDerivativeCore L a ab j h‖ ^ 2 ≤
      gradientEnergy (d.localizedSchwartz L a ab h) := by
    rw [d.localizedDerivativeCore_norm_sq]
    unfold gradientEnergy
    exact Finset.single_le_sum
      (f := fun i : Fin n => ∫ x : ModelE,
        (fderiv ℝ (d.localizedSchwartz L a ab h) x (EuclideanSpace.single i (1 : ℝ))) ^ 2)
      (a := j)
      (fun i _ => integral_nonneg (fun x => sq_nonneg
        (fderiv ℝ (d.localizedSchwartz L a ab h) x (EuclideanSpace.single i (1 : ℝ)))))
      (Finset.mem_univ j)
  have hgrad := hgradient (scalarProbe d.fields h ab)
    (scalarProbe_contMDiff d.fields h ab) hf hDf
  have henergy := pairing_firstOrderEnergy_le d.fields d.charts.measure h ab.1 ab.2 hf hDf
  have hbound : ‖d.localizedDerivativeCore L a ab j h‖ ^ 2 ≤
      C * ‖intoFirstOrderGraph d.fields d.charts.measure h‖ ^ 2 :=
    hcoord.trans (hgrad.trans (mul_le_mul_of_nonneg_left henergy hC))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))).mp
  have hCbound : C ≤ (C + 1) ^ 2 := by nlinarith [sq_nonneg C]
  have hsq := mul_le_mul_of_nonneg_right hCbound
    (sq_nonneg ‖intoFirstOrderGraph d.fields d.charts.measure h‖)
  simpa only [mul_pow] using hbound.trans hsq

def localizedDerivative (j : Fin n) : d.Form →L[ℝ] Lp ℝ 2 (volume : Measure ModelE) :=
  (d.localizedDerivativeCore L a ab j).extendOfNorm
    (intoFirstOrderGraph d.fields d.charts.measure)

theorem localizedDerivative_into (j : Fin n) (h : SmoothTensor (n := n) (M := M)) :
    d.localizedDerivative L a ab j (intoFirstOrderGraph d.fields d.charts.measure h) =
      (∂_{EuclideanSpace.single j (1 : ℝ)} (d.localizedSchwartz L a ab h)).toLp 2 volume := by
  obtain ⟨C, _, hC⟩ := d.exists_localizedDerivativeCore_bound L a ab j
  exact LinearMap.extendOfNorm_eq (intoFirstOrderGraph_denseRange d.fields d.charts.measure) ⟨C, hC⟩ h

def localizedValue : d.Form →L[ℝ] Lp ℝ 2 (volume : Measure ModelE) :=
  (L.localizationL2 a).comp ((d.valueCoefficient ab).comp d.inclusion)

theorem localizedValue_into (h : SmoothTensor (n := n) (M := M)) :
    d.localizedValue L a ab (intoFirstOrderGraph d.fields d.charts.measure h) =
      (d.localizedSchwartz L a ab h).toLp 2 volume := by
  let hf := pairing_memLp d.fields d.charts.measure h ab.1 ab.2
  have hcoeff : d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure h) =
      hf.toLp (scalarProbe d.fields h ab) := by
    apply Lp.ext
    exact (d.valueCoefficient_into_coe ab h).trans hf.coeFn_toLp.symm
  change L.localizationL2 a (d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure h)) = _
  rw [hcoeff, L.localizationL2_toLp_eq a (scalarProbe_contMDiff d.fields h ab) hf]
  apply Lp.ext
  exact (L.localizedProduct_memLp a (scalarProbe_contMDiff d.fields h ab)).coeFn_toLp.trans
    ((d.localizedSchwartz L a ab h).coeFn_toLp 2 volume).symm

end LocalFirstOrder

end Data

section Complexification

variable {n : ℕ}

local notation "ModelE" => EuclideanSpace ℝ (Fin n)

def coordinateComplexification : Lp ℝ 2 (volume : Measure ModelE) →L[ℝ]
    Lp ℂ 2 (volume : Measure ModelE) :=
  Complex.ofRealCLM.compLpL 2 volume

theorem coordinateComplexification_schwartz (f : 𝓢(ModelE, ℝ)) :
    coordinateComplexification (f.toLp 2 volume) =
      (f.postcompCLM Complex.ofRealCLM).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (f.toLp 2 volume), f.coeFn_toLp 2 volume,
    (f.postcompCLM Complex.ofRealCLM).coeFn_toLp 2 volume] with x hc hf hg
  change Complex.ofRealCLM.compLpL 2 volume (f.toLp 2 volume) x = _
  rw [hc, hf, hg, SchwartzMap.postcompCLM_apply]

theorem schwartz_lineDeriv_complexification (f : 𝓢(ModelE, ℝ)) (v : ModelE) :
    ∂_{v} (f.postcompCLM Complex.ofRealCLM) =
      (∂_{v} f).postcompCLM Complex.ofRealCLM := by
  ext x
  change fderiv ℝ (fun y => Complex.ofRealCLM (f y)) x v =
    Complex.ofRealCLM (fderiv ℝ f x v)
  exact congrArg (fun A : ModelE →L[ℝ] ℂ => A v)
    (Complex.ofRealCLM.hasFDerivAt.comp x (f.hasFDerivAt x)).fderiv

theorem coordinateComplexification_derivative (f : 𝓢(ModelE, ℝ)) (v : ModelE) :
    ∂_{v} (coordinateComplexification (f.toLp 2 volume) : 𝓢'(ModelE, ℂ)) =
      (coordinateComplexification ((∂_{v} f).toLp 2 volume) : 𝓢'(ModelE, ℂ)) := by
  rw [coordinateComplexification_schwartz, coordinateComplexification_schwartz,
    Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq,
    TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq,
    schwartz_lineDeriv_complexification]

end Complexification

namespace Data

variable {g : RiemannianMetric n M} (d : Data g)
  [MeasurableSpace M] [BorelSpace M]

local notation "ModelE" => EuclideanSpace ℝ (Fin n)

theorem localizedDerivative_distribution (L : FiniteChartLocalizationData d.charts)
    (a : L.patches) (ab : d.ProbeIndex) (j : Fin n) (z : d.Form) :
    ∂_{EuclideanSpace.single j (1 : ℝ)}
      (coordinateComplexification (d.localizedValue L a ab z) : 𝓢'(ModelE, ℂ)) =
      (coordinateComplexification (d.localizedDerivative L a ab j z) : 𝓢'(ModelE, ℂ)) := by
  have hval : Continuous (fun z : d.Form =>
      (coordinateComplexification (d.localizedValue L a ab z) : 𝓢'(ModelE, ℂ))) :=
    (Lp.toTemperedDistributionCLM ℂ volume 2).continuous.comp
      (coordinateComplexification.continuous.comp (d.localizedValue L a ab).continuous)
  have hderiv : Continuous (fun z : d.Form =>
      (coordinateComplexification (d.localizedDerivative L a ab j z) : 𝓢'(ModelE, ℂ))) :=
    (Lp.toTemperedDistributionCLM ℂ volume 2).continuous.comp
      (coordinateComplexification.continuous.comp (d.localizedDerivative L a ab j).continuous)
  have heq :
      (fun z : d.Form => ∂_{EuclideanSpace.single j (1 : ℝ)}
        (coordinateComplexification (d.localizedValue L a ab z) : 𝓢'(ModelE, ℂ))) =
      (fun z : d.Form =>
        (coordinateComplexification (d.localizedDerivative L a ab j z) : 𝓢'(ModelE, ℂ))) := by
    apply (intoFirstOrderGraph_denseRange d.fields d.charts.measure).equalizer
      ((LineDeriv.lineDerivOpCLM ℂ 𝓢'(ModelE, ℂ) (EuclideanSpace.single j (1 : ℝ))).continuous.comp hval)
      hderiv
    funext h
    simp only [Function.comp_apply]
    rw [d.localizedValue_into, d.localizedDerivative_into]
    exact coordinateComplexification_derivative (d.localizedSchwartz L a ab h)
      (EuclideanSpace.single j (1 : ℝ))
  exact congrFun heq z

theorem scalarLp_norm_sq (f : M → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ‖d.scalarLp f hf‖ ^ 2 = ∫ x, f x ^ 2 ∂d.charts.measure := by
  rw [LpFiniteCoordinatesNative.l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [d.scalarLp_coe f hf] with x hx
  rw [hx, Real.norm_eq_abs, sq_abs]

theorem scalarLp_scalarProbe (h : SmoothTensor (n := n) (M := M)) (ab : d.ProbeIndex) :
    d.scalarLp (scalarProbe d.fields h ab) (scalarProbe_contMDiff d.fields h ab) =
      d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure h) := by
  apply Lp.ext
  exact (d.scalarLp_coe _ _).trans (d.valueCoefficient_into_coe ab h).symm

theorem scalarLp_scalarLaplacian_probe (h : SmoothTensor (n := n) (M := M))
    (ab : d.ProbeIndex) :
    d.scalarLp (scalarLaplacian d.fields d.charts (scalarProbe d.fields h ab))
        (scalarLaplacian_contMDiff d.fields d.charts (scalarProbe_contMDiff d.fields h ab)) =
      d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure
        (smoothTensorLaplacian d.fields d.charts g h)) +
          d.lowerSource ab (intoFirstOrderGraph d.fields d.charts.measure h) := by
  apply Lp.ext
  filter_upwards [d.scalarLp_coe
      (scalarLaplacian d.fields d.charts (scalarProbe d.fields h ab))
      (scalarLaplacian_contMDiff d.fields d.charts (scalarProbe_contMDiff d.fields h ab)),
    d.valueCoefficient_into_coe ab (smoothTensorLaplacian d.fields d.charts g h),
    d.lowerSource_into_coe ab h,
    Lp.coeFn_add (d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure
      (smoothTensorLaplacian d.fields d.charts g h)))
      (d.lowerSource ab (intoFirstOrderGraph d.fields d.charts.measure h))]
    with x hL hvalue hlower hadd
  rw [hadd, Pi.add_apply, hL, hvalue, hlower]
  exact scalarLaplacian_probe_eq d.fields d.charts g d.parseval h ab x

theorem exists_smooth_secondDirectional_graph_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : SmoothTensor (n := n) (M := M),
      (∑ ab : d.ProbeIndex, ∑ i, ∑ j, ∫ x,
        scalarDirectional (d.fields i) (scalarDirectional (d.fields j)
          (scalarProbe d.fields h ab)) x ^ 2 ∂d.charts.measure) ≤
      C * (‖intoTensorL2 d.fields d.charts.measure h‖ +
        ‖intoTensorL2 d.fields d.charts.measure
          (smoothTensorLaplacian d.fields d.charts g h)‖) ^ 2 := by
  classical
  obtain ⟨C, hC, hscalar⟩ :=
    d.charts.exists_secondDirectional_graph_bound g d.fields d.parseval
  let K : d.ProbeIndex → ℝ := fun ab =>
    C * (‖d.valueCoefficient ab‖ ^ 2 + (‖d.valueCoefficient ab‖ + ‖d.lowerSource ab‖) ^ 2)
  refine ⟨∑ ab, K ab, Finset.sum_nonneg (fun ab _ => by dsimp [K]; positivity), ?_⟩
  intro h
  let u := intoTensorL2 d.fields d.charts.measure h
  let a := intoTensorL2 d.fields d.charts.measure
    (smoothTensorLaplacian d.fields d.charts g h)
  let z := intoFirstOrderGraph d.fields d.charts.measure h
  let R : ℝ := ‖u‖ + ‖a‖
  have hR : 0 ≤ R := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hu : ‖u‖ ≤ R := le_add_of_nonneg_right (norm_nonneg _)
  have ha : ‖a‖ ≤ R := le_add_of_nonneg_left (norm_nonneg _)
  have hz : ‖z‖ ≤ R := d.norm_form_le_of_variational (u := u) (a := a) rfl
    (form_pairing_laplacian d.fields d.charts g d.parseval h)
  have hbound (ab : d.ProbeIndex) :
      (∑ i, ∑ j, ∫ x, scalarDirectional (d.fields i) (scalarDirectional (d.fields j)
        (scalarProbe d.fields h ab)) x ^ 2 ∂d.charts.measure) ≤ K ab * R ^ 2 := by
    let f := scalarProbe d.fields h ab
    have hf := scalarProbe_contMDiff d.fields h ab
    have hL := scalarLaplacian_contMDiff d.fields d.charts hf
    have hfnorm : ‖d.scalarLp f hf‖ ≤ ‖d.valueCoefficient ab‖ * R := by
      rw [d.scalarLp_scalarProbe]
      exact ((d.valueCoefficient ab).le_opNorm u).trans
        (mul_le_mul_of_nonneg_left hu (norm_nonneg (d.valueCoefficient ab)))
    have hLnorm : ‖d.scalarLp (scalarLaplacian d.fields d.charts f) hL‖ ≤
        (‖d.valueCoefficient ab‖ + ‖d.lowerSource ab‖) * R := by
      rw [d.scalarLp_scalarLaplacian_probe]
      calc
        _ ≤ ‖d.valueCoefficient ab a‖ + ‖d.lowerSource ab z‖ := norm_add_le _ _
        _ ≤ ‖d.valueCoefficient ab‖ * ‖a‖ + ‖d.lowerSource ab‖ * ‖z‖ :=
          add_le_add ((d.valueCoefficient ab).le_opNorm a) ((d.lowerSource ab).le_opNorm z)
        _ ≤ ‖d.valueCoefficient ab‖ * R + ‖d.lowerSource ab‖ * R :=
          add_le_add (mul_le_mul_of_nonneg_left ha (norm_nonneg (d.valueCoefficient ab)))
            (mul_le_mul_of_nonneg_left hz (norm_nonneg (d.lowerSource ab)))
        _ = _ := by ring
    calc
      _ ≤ C * ((∫ x, f x ^ 2 ∂d.charts.measure) +
          ∫ x, scalarLaplacian d.fields d.charts f x ^ 2 ∂d.charts.measure) := hscalar f hf
      _ = C * (‖d.scalarLp f hf‖ ^ 2 +
          ‖d.scalarLp (scalarLaplacian d.fields d.charts f) hL‖ ^ 2) := by
        rw [d.scalarLp_norm_sq, d.scalarLp_norm_sq]
      _ ≤ C * ((‖d.valueCoefficient ab‖ * R) ^ 2 +
          ((‖d.valueCoefficient ab‖ + ‖d.lowerSource ab‖) * R) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (add_le_add ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hfnorm)
            ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hLnorm)) hC
      _ = K ab * R ^ 2 := by dsimp [K]; ring
  calc
    _ ≤ ∑ ab, K ab * R ^ 2 := Finset.sum_le_sum (fun ab _ => hbound ab)
    _ = _ := by rw [Finset.sum_mul]

end Data

end PoincareConjecture.TensorHilbertNative
