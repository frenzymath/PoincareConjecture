import PoincareConjecture.Proofs.M03.Existence.DeTurckSpatialRecoveryNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckPositiveStateNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckJetProlongationNative
import PoincareConjecture.Proofs.M03.Existence.CoordinateMetricRegularityNative
import PoincareConjecture.Proofs.M03.Existence.ParsevalTensorSmoothNative







set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix.Norms.Elementwise

namespace PoincareConjecture.DeTurckSmoothMetricFamilyNative

open TensorProbeNative TensorHilbertNative ParsevalTensorNative ChartMeasureNative
  DeTurckJetCoordinatesNative DeTurckJetAffineNative DeTurckSpatialRecoveryNative
  DeTurckPositiveStateNative DeTurckNative DeTurckMetricProducerNative
  DeTurckJetProlongationNative DeTurckEndpointCalculusNative
  ContinuousPathCompositionNative SpectralHeatNative

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {g0 : RiemannianMetric n M} (d : Data g0)
  (L : FiniteChartLocalizationData d.charts)

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓡 n
local notation "P" => Fin n → ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

section RecoveredMetric

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (r p : ℕ) (hpr : 2 * p ≤ r) (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
  (z : C(K, State d.SymmetricIndex))
  (hspatial : ∀ ab : d.ProbeIndex,
    ContMDiff (𝓡 n) 𝓘(ℝ, C(K, ℝ)) ∞ (probePath d L r p (by omega) hp z ab))

def recoveredMetric
    (hsmall : ∀ t : K,
      ‖d.smoothTensorCoordinates (2 * r + 1)
        (recoveredTensor d L r p (by omega) hp z hspatial t)
        (recoveredTensor_symmetric d L r p (by omega) hp z hspatial t)‖ ≤
          positivityRadius d L r p hpr hp) (t : K) : RiemannianMetric n M :=
  (smallMetricPerturbation d L r p hpr hp
    (recoveredTensor d L r p (by omega) hp z hspatial t)
    (recoveredTensor_symmetric d L r p (by omega) hp z hspatial t) (hsmall t)).metric

variable (hsmall : ∀ t : K,
  ‖d.smoothTensorCoordinates (2 * r + 1)
    (recoveredTensor d L r p (by omega) hp z hspatial t)
    (recoveredTensor_symmetric d L r p (by omega) hp z hspatial t)‖ ≤
      positivityRadius d L r p hpr hp)

theorem recoveredMetric_inner (t : K) (x : M) (v w : TangentSpace I x) :
    (recoveredMetric d L r p hpr hp z hspatial hsmall t).inner x v w =
      g0.inner x v w + stateTensor d L r p (by omega) hp (z t) x v w := rfl

theorem recoveredMetric_lower_bound (t : K) (x : M) (v : TangentSpace I x) :
    (3 / 4 : ℝ) * g0.inner x v v ≤
      (recoveredMetric d L r p hpr hp z hspatial hsmall t).inner x v v :=
  smallMetricPerturbation_lower_bound d L r p hpr hp _ _ (hsmall t) x v

theorem recoveredMetric_eq_initial {t : K} (hz : z t = 0) :
    recoveredMetric d L r p hpr hp z hspatial hsmall t = g0 := by
  have hinner : ∀ (x : M) (v w : TangentSpace I x),
      (recoveredMetric d L r p hpr hp z hspatial hsmall t).inner x v w = g0.inner x v w := by
    intro x v w
    rw [recoveredMetric_inner, hz, ← tensorEvaluation_apply]
    simp only [map_zero, add_zero]
  cases h1 : recoveredMetric d L r p hpr hp z hspatial hsmall t
  cases h2 : g0
  simp only [Bundle.ContMDiffRiemannianMetric.mk.injEq]
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simpa only [h1, h2] using hinner x v w

def metricEntryPath (base : M) (i j : Fin n) (x : M) : C(K, ℝ) :=
  ContinuousMap.const K (g0.inner x (chartFrame base i x) (chartFrame base j x)) +
    chartTensorPath d L r p (by omega) hp z base i j x

theorem metricEntryPath_apply (base : M) (i j : Fin n) (x : M) (t : K) :
    metricEntryPath d L r p hpr hp z base i j x t =
      (recoveredMetric d L r p hpr hp z hspatial hsmall t).inner x
        (chartFrame base i x) (chartFrame base j x) := by
  rw [metricEntryPath, ContinuousMap.add_apply, ContinuousMap.const_apply,
    chartTensorPath_apply, recoveredMetric_inner]

include hspatial in
theorem contMDiffOn_metricEntryPath (base : M) (i j : Fin n) :
    ContMDiffOn I 𝓘(ℝ, C(K, ℝ)) ∞ (metricEntryPath d L r p hpr hp z base i j)
      (chartAt E base).source := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g0.toRiemannianMetric⟩
  have hbase : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x => g0.inner x (chartFrame base i x) (chartFrame base j x))
      (chartAt E base).source :=
    (chartFrame_contMDiffOn base i).inner_bundle (chartFrame_contMDiffOn base j)
  exact ((ContinuousLinearMap.const ℝ K).contMDiff.comp_contMDiffOn hbase).add
    (contMDiffOn_chartTensorPath d L r p (by omega) hp z hspatial base i j)

end RecoveredMetric

section OrdinaryCoordinates

def coordinateModel (n : ℕ) : (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm

theorem coordinateModel_basis (i : Fin n) :
    coordinateModel n (Pi.single i 1) = (PiLp.basisFun 2 ℝ (Fin n)) i := by
  rw [PiLp.basisFun_apply]
  rfl

def chartPoint (base : M) (y : P) : M :=
  (extChartAt I base).symm (coordinateModel n y)

def chartDomain (base : M) : Set P :=
  coordinateModel n ⁻¹' (extChartAt I base).target

def coordinateOf (base x : M) : P :=
  (coordinateModel n).symm (extChartAt I base x)

theorem isOpen_chartDomain (base : M) : IsOpen (chartDomain (n := n) base) :=
  (isOpen_extChartAt_target base).preimage (coordinateModel n).continuous

theorem chartPoint_mem_source (base : M) {y : P} (hy : y ∈ chartDomain base) :
    chartPoint base y ∈ (chartAt E base).source := by
  simpa only [chartPoint, extChartAt_source] using (extChartAt I base).map_target hy

theorem coordinateOf_mem_domain (base : M) {x : M}
    (hx : x ∈ (chartAt E base).source) :
    coordinateOf (n := n) base x ∈ chartDomain (n := n) base := by
  change coordinateModel n ((coordinateModel n).symm (extChartAt I base x)) ∈
    (extChartAt I base).target
  rw [(coordinateModel n).apply_symm_apply]
  exact (extChartAt I base).map_source (by simpa only [extChartAt_source] using hx)

theorem chartPoint_coordinateOf (base : M) {x : M}
    (hx : x ∈ (chartAt E base).source) :
    chartPoint (n := n) base (coordinateOf (n := n) base x) = x := by
  simp only [chartPoint, coordinateOf, (coordinateModel n).apply_symm_apply]
  exact (extChartAt I base).left_inv (by simpa only [extChartAt_source] using hx)

theorem contMDiffOn_chartPoint (base : M) :
    ContMDiffOn 𝓘(ℝ, P) I ∞ (chartPoint (n := n) base) (chartDomain (n := n) base) :=
  (contMDiffOn_extChartAt_symm base).comp (coordinateModel n).contDiff.contMDiff.contMDiffOn
    (fun _ hy => hy)

theorem contMDiffOn_coordinateOf (base : M) :
    ContMDiffOn I 𝓘(ℝ, P) ∞ (coordinateOf (n := n) base) (chartAt E base).source :=
  (coordinateModel n).symm.contDiff.contMDiff.comp_contMDiffOn contMDiffOn_extChartAt

theorem exists_precompact_chartDomain (base : M) :
    ∃ Omega : Set P, IsOpen Omega ∧ coordinateOf base base ∈ Omega ∧
      closure Omega ⊆ chartDomain base ∧ IsCompact (closure Omega) := by
  obtain ⟨Omega, hO, hmem, hsub, hcompact⟩ :=
    exists_open_between_and_isCompact_closure (isCompact_singleton (x := coordinateOf base base))
      (isOpen_chartDomain base)
      (singleton_subset_iff.mpr (coordinateOf_mem_domain base (mem_chart_source E base)))
  exact ⟨Omega, hO, hmem (mem_singleton _), hsub, hcompact⟩

def coordinateMetricEntries (g : RiemannianMetric n M) (base : M) (y : P) : Mat :=
  chartMetricCoefficients g base (coordinateModel n y)

theorem contDiffOn_coordinateMetricEntries (g : RiemannianMetric n M) (base : M) :
    ContDiffOn ℝ ∞ (coordinateMetricEntries g base) (chartDomain base) := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact (chartMetricCoefficients_contDiffOn g base i j).comp
    (coordinateModel n).contDiff.contDiffOn (fun _ hy => hy)

theorem coordinateMetricEntries_posDef (g : RiemannianMetric n M) (base : M)
    {y : P} (hy : y ∈ chartDomain base) : (coordinateMetricEntries g base y).PosDef :=
  chartMetricCoefficients_posDef g base hy

theorem fderiv_comp_coordinateModel {f : E → ℝ} {y : P}
    (hf : DifferentiableAt ℝ f (coordinateModel n y)) (i : Fin n) :
    fderiv ℝ (fun q => f (coordinateModel n q)) y (Pi.single i 1) =
      fderiv ℝ f (coordinateModel n y) ((PiLp.basisFun 2 ℝ (Fin n)) i) := by
  have hderiv := (hf.hasFDerivAt.comp y (coordinateModel n).hasFDerivAt).fderiv
  simp only [Function.comp_def] at hderiv
  rw [hderiv]
  change fderiv ℝ f (coordinateModel n y) (coordinateModel n (Pi.single i 1)) = _
  rw [coordinateModel_basis]

theorem coordinateMetricEntries_first (g : RiemannianMetric n M) (base : M)
    {y : P} (hy : y ∈ chartDomain base) (a i j : Fin n) :
    wordDerivative [a] (fun q => coordinateMetricEntries g base q i j) y =
      (frameMetricJet g (chartFrame base) (chartPoint base y)).first a i j := by
  have hf := ((chartMetricCoefficients_contDiffOn g base i j).contDiffAt
    ((isOpen_extChartAt_target base).mem_nhds hy)).differentiableAt (by simp)
  change fderiv ℝ (fun q => chartMetricCoefficients g base (coordinateModel n q) i j)
    y (Pi.single a 1) = _
  rw [fderiv_comp_coordinateModel hf,
    frameMetricJet_first_eq_chartCoefficient_derivative g base (chartPoint_mem_source base hy)]
  simp only [chartPoint, (extChartAt I base).right_inv hy]

theorem coordinateMetricEntries_second (g : RiemannianMetric n M) (base : M)
    {y : P} (hy : y ∈ chartDomain base) (a b i j : Fin n) :
    wordDerivative [a, b] (fun q => coordinateMetricEntries g base q i j) y =
      (frameMetricJet g (chartFrame base) (chartPoint base y)).second a b i j := by
  let f : E → ℝ := fun e => chartMetricCoefficients g base e i j
  let df : E → ℝ := fun e => fderiv ℝ f e ((PiLp.basisFun 2 ℝ (Fin n)) b)
  have hf : ContDiffOn ℝ ∞ f (extChartAt I base).target :=
    chartMetricCoefficients_contDiffOn g base i j
  have hdf : ContDiffOn ℝ ∞ df (extChartAt I base).target :=
    (hf.fderiv_of_isOpen (isOpen_extChartAt_target base) (by simp)).clm_apply contDiffOn_const
  have heq : (fun q => fderiv ℝ (fun w => f (coordinateModel n w)) q (Pi.single b 1)) =ᶠ[𝓝 y]
      (fun q => df (coordinateModel n q)) := by
    filter_upwards [(isOpen_chartDomain base).mem_nhds hy] with q hq
    exact fderiv_comp_coordinateModel
      ((hf.contDiffAt ((isOpen_extChartAt_target base).mem_nhds hq)).differentiableAt (by simp)) b
  change fderiv ℝ (fun q => fderiv ℝ (fun w => f (coordinateModel n w)) q
    (Pi.single b 1)) y (Pi.single a 1) = _
  rw [heq.fderiv_eq, fderiv_comp_coordinateModel
    ((hdf.contDiffAt ((isOpen_extChartAt_target base).mem_nhds hy)).differentiableAt (by simp)) a,
    frameMetricJet_second_eq_chartCoefficient_derivative g base (chartPoint_mem_source base hy)]
  simp only [chartPoint, (extChartAt I base).right_inv hy, df, f]

end OrdinaryCoordinates

section MatrixPaths

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

def matrixCurry (n : ℕ) : ((Fin n × Fin n) → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j =>
    ContinuousLinearMap.proj (i, j)))

def matrixPath (f : (Fin n × Fin n) → C(K, ℝ)) : C(K, Mat) :=
  (matrixCurry n).compLeftContinuous ℝ K (packContinuous f)

@[simp] theorem matrixPath_apply (f : (Fin n × Fin n) → C(K, ℝ)) (t : K) (i j : Fin n) :
    matrixPath f t i j = f (i, j) t := by
  change packContinuous f t (i, j) = _
  classical
  simp [packContinuous, ContinuousLinearMap.single_apply]

theorem contDiffOn_matrixPath {Omega : Set P} (f : (Fin n × Fin n) → P → C(K, ℝ))
    (hf : ∀ ab, ContDiffOn ℝ ∞ (f ab) Omega) :
    ContDiffOn ℝ ∞ (fun y => matrixPath (fun ab => f ab y)) Omega := by
  have hpack : ContDiffOn ℝ ∞ (fun y => packContinuous (fun ab => f ab y)) Omega := by
    simpa only [Function.comp_def] using
      (packContinuous (M := K) (A := Fin n × Fin n)).contDiff.comp_contDiffOn
        (contDiffOn_pi.mpr hf)
  simpa only [matrixPath, Function.comp_def] using
    ((matrixCurry n).compLeftContinuous ℝ K).contDiff.comp_contDiffOn hpack

def pairMatrixPath (B G : C(K, Mat)) : C(K, Mat × Mat) :=
  (ContinuousLinearMap.inl ℝ Mat Mat).compLeftContinuous ℝ K B +
    (ContinuousLinearMap.inr ℝ Mat Mat).compLeftContinuous ℝ K G

@[simp] theorem pairMatrixPath_apply (B G : C(K, Mat)) (t : K) :
    pairMatrixPath B G t = (B t, G t) := by
  simp [pairMatrixPath]

theorem contDiffOn_pairMatrixPath {Omega : Set P} {B G : P → C(K, Mat)}
    (hB : ContDiffOn ℝ ∞ B Omega) (hG : ContDiffOn ℝ ∞ G Omega) :
    ContDiffOn ℝ ∞ (fun y => pairMatrixPath (B y) (G y)) Omega :=
  (((ContinuousLinearMap.inl ℝ Mat Mat).compLeftContinuous ℝ K).contDiff.comp_contDiffOn hB).add
    (((ContinuousLinearMap.inr ℝ Mat Mat).compLeftContinuous ℝ K).contDiff.comp_contDiffOn hG)

end MatrixPaths

section RecoveredCoordinates

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  (r p : ℕ) (hpr : 2 * p ≤ r) (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
  (z : C(K, State d.SymmetricIndex))
  (hspatial : ∀ ab : d.ProbeIndex,
    ContMDiff (𝓡 n) 𝓘(ℝ, C(K, ℝ)) ∞ (probePath d L r p (by omega) hp z ab))
  (hsmall : ∀ t : K,
    ‖d.smoothTensorCoordinates (2 * r + 1)
      (recoveredTensor d L r p (by omega) hp z hspatial t)
      (recoveredTensor_symmetric d L r p (by omega) hp z hspatial t)‖ ≤
        positivityRadius d L r p hpr hp)

def coordinateMetricPath (base : M) (y : P) : C(K, Mat) :=
  matrixPath (fun ab => metricEntryPath d L r p hpr hp z base ab.1 ab.2 (chartPoint base y))

theorem coordinateMetricPath_apply (base : M) (y : P) (t : K) :
    coordinateMetricPath d L r p hpr hp z base y t =
      coordinateMetricEntries (recoveredMetric d L r p hpr hp z hspatial hsmall t) base y := by
  ext i j
  rw [coordinateMetricPath, matrixPath_apply,
    metricEntryPath_apply d L r p hpr hp z hspatial hsmall]
  rfl

include hspatial in
theorem contDiffOn_coordinateMetricPath (base : M) :
    ContDiffOn ℝ ∞ (coordinateMetricPath d L r p hpr hp z base) (chartDomain base) := by
  apply contDiffOn_matrixPath
  intro ab
  exact ((contMDiffOn_metricEntryPath d L r p hpr hp z hspatial base ab.1 ab.2).comp
    (contMDiffOn_chartPoint base) (fun _ hy => chartPoint_mem_source base hy)).contDiffOn

def coordinatePairPath (base : M) (y : P) : C(K, Mat × Mat) :=
  pairMatrixPath (ContinuousMap.const K (coordinateMetricEntries g0 base y))
    (coordinateMetricPath d L r p hpr hp z base y)

theorem coordinatePairPath_apply (base : M) (y : P) (t : K) :
    coordinatePairPath d L r p hpr hp z base y t =
      (coordinateMetricEntries g0 base y,
        coordinateMetricEntries (recoveredMetric d L r p hpr hp z hspatial hsmall t) base y) := by
  rw [coordinatePairPath, pairMatrixPath_apply, ContinuousMap.const_apply,
    coordinateMetricPath_apply d L r p hpr hp z hspatial hsmall]

include hspatial in
theorem contDiffOn_coordinatePairPath (base : M) :
    ContDiffOn ℝ ∞ (coordinatePairPath d L r p hpr hp z base) (chartDomain base) := by
  let A : Mat →L[ℝ] C(K, Mat) := ContinuousLinearMap.const ℝ K
  have hA (v : Mat) : A v = ContinuousMap.const K v := rfl
  have hbase : ContDiffOn ℝ ∞
      (fun y => ContinuousMap.const K (coordinateMetricEntries g0 base y))
      (chartDomain base) := by
    simpa only [Function.comp_def, hA] using
      A.contDiff.comp_contDiffOn (contDiffOn_coordinateMetricEntries g0 base)
  exact contDiffOn_pairMatrixPath hbase
    (contDiffOn_coordinateMetricPath d L r p hpr hp z hspatial base)

end RecoveredCoordinates

section TwoJet

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def matrixSlot (b : Bool) : (Mat × Mat) →L[ℝ] Mat :=
  if b then ContinuousLinearMap.snd ℝ Mat Mat else ContinuousLinearMap.fst ℝ Mat Mat

def matrixEntry (b : Bool) (i j : Fin n) : (Mat × Mat) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.proj i).comp (matrixSlot b))

def packChartState (b : Bool) (Q : WordIndex (Fin n) 2 → Mat × Mat) : ChartState (n := n) :=
  (matrixSlot b (Q (wordIndex [] (by simp))),
    (fun a => matrixSlot b (Q (wordIndex [a] (by simp)))),
    fun a b' => matrixSlot b (Q (wordIndex [a, b'] (by simp))))

def packChartJet (Q : WordIndex (Fin n) 2 → Mat × Mat) :
    ChartState (n := n) × ChartState (n := n) :=
  (packChartState false Q, packChartState true Q)

theorem contDiff_packChartState (b : Bool) : ContDiff ℝ ∞ (packChartState (n := n) b) := by
  unfold packChartState
  fun_prop

theorem contDiff_packChartJet : ContDiff ℝ ∞ (packChartJet (n := n)) :=
  (contDiff_packChartState false).prodMk (contDiff_packChartState true)

def packWordPaths (k : ℕ) :
    (WordIndex (Fin n) k → C(K, Mat × Mat)) →L[ℝ] C(K, WordIndex (Fin n) k → Mat × Mat) := by
  classical
  exact ∑ w : WordIndex (Fin n) k,
    ((ContinuousLinearMap.single ℝ (fun _ : WordIndex (Fin n) k => Mat × Mat) w).compLeftContinuous
      ℝ K).comp (ContinuousLinearMap.proj w)

@[simp] theorem packWordPaths_apply (k : ℕ) (Q : WordIndex (Fin n) k → C(K, Mat × Mat))
    (t : K) (w : WordIndex (Fin n) k) : packWordPaths k Q t w = Q w t := by
  classical
  simp [packWordPaths, ContinuousLinearMap.single_apply]

def coordinateJetPath (U : P → C(K, Mat × Mat)) (y : P) :
    C(K, WordIndex (Fin n) 2 → Mat × Mat) :=
  packWordPaths 2 (fun w => wordDerivative (List.ofFn w.2) U y)

theorem coordinateJetPath_apply (U : P → C(K, Mat × Mat)) (y : P) (t : K) :
    coordinateJetPath U y t = finiteJet 2 (fun w => wordDerivative w U y t) := by
  funext w
  exact packWordPaths_apply 2 _ t w

theorem contDiffOn_coordinateJetPath {Omega : Set P} (hOmega : IsOpen Omega)
    {U : P → C(K, Mat × Mat)} (hU : ContDiffOn ℝ ∞ U Omega) :
    ContDiffOn ℝ ∞ (coordinateJetPath U) Omega := by
  exact (packWordPaths (n := n) (K := K) 2).contDiff.comp_contDiffOn
    (contDiffOn_pi.mpr (fun w : WordIndex (Fin n) 2 =>
      wordDerivative_contDiffOn hOmega hU (List.ofFn w.2)))


theorem packChartState_eq_frameMetricJet (base : M) (U : P → C(K, Mat × Mat))
    (hU : ContDiffOn ℝ ∞ U (chartDomain base)) (b : Bool) (g : K → RiemannianMetric n M)
    (hvalue : ∀ y t, matrixSlot b (U y t) = coordinateMetricEntries (g t) base y)
    {y : P} (hy : y ∈ chartDomain base) (t : K) :
    chartStateJet (packChartState b (coordinateJetPath U y t)) =
      frameMetricJet (g t) (chartFrame base) (chartPoint base y) := by
  have hword (w : List (Fin n)) (i j : Fin n) :
      matrixEntry b i j (wordDerivative w U y t) =
        wordDerivative w (fun q => coordinateMetricEntries (g t) base q i j) y := by
    let A : C(K, Mat × Mat) →L[ℝ] ℝ := (matrixEntry b i j).comp (ContinuousMap.evalCLM ℝ t)
    have heq : (fun q => A (U q)) = (fun q => coordinateMetricEntries (g t) base q i j) := by
      funext q
      exact congrFun (congrFun (hvalue q t) i) j
    rw [← heq]
    exact (wordDerivative_clm A (isOpen_chartDomain base) hU w hy).symm
  have hv : (chartStateJet (packChartState b (coordinateJetPath U y t))).value =
      (frameMetricJet (g t) (chartFrame base) (chartPoint base y)).value := by
    change matrixSlot b (coordinateJetPath U y t (wordIndex [] (by simp))) = _
    rw [coordinateJetPath_apply]
    simpa only [finiteJet, wordIndex_word, wordDerivative, coordinateMetricEntries,
      chartMetricCoefficients, chartPoint, frameMetricJet] using hvalue y t
  have hf : (chartStateJet (packChartState b (coordinateJetPath U y t))).first =
      (frameMetricJet (g t) (chartFrame base) (chartPoint base y)).first := by
    funext a i j
    change matrixEntry b i j (coordinateJetPath U y t (wordIndex [a] (by simp))) = _
    rw [coordinateJetPath_apply]
    simp only [finiteJet, wordIndex_word]
    exact (hword [a] i j).trans (coordinateMetricEntries_first (g t) base hy a i j)
  have hs : (chartStateJet (packChartState b (coordinateJetPath U y t))).second =
      (frameMetricJet (g t) (chartFrame base) (chartPoint base y)).second := by
    funext a b' i j
    change matrixEntry b i j (coordinateJetPath U y t (wordIndex [a, b'] (by simp))) = _
    rw [coordinateJetPath_apply]
    simp only [finiteJet, wordIndex_word]
    exact (hword [a, b'] i j).trans (coordinateMetricEntries_second (g t) base hy a b' i j)
  cases h1 : chartStateJet (packChartState b (coordinateJetPath U y t))
  cases h2 : frameMetricJet (g t) (chartFrame base) (chartPoint base y)
  simp_all only [MetricJet2.mk.injEq]

end TwoJet

section CompactSource

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def finiteSource (fExt : C(ChartState (n := n) × ChartState (n := n), Mat)) :
    (P × (WordIndex (Fin n) 2 → Mat × Mat)) → Mat × Mat :=
  fun q => (0, fExt (packChartJet q.2))

theorem contDiff_finiteSource (fExt : C(ChartState (n := n) × ChartState (n := n), Mat))
    (hfExt : ContDiff ℝ ∞ fExt) : ContDiff ℝ ∞ (finiteSource fExt) :=
  contDiff_const.prodMk (hfExt.comp (contDiff_packChartJet.comp contDiff_snd))

def sourceMap (fExt : C(ChartState (n := n) × ChartState (n := n), Mat)) :
    C(WordIndex (Fin n) 2 → Mat × Mat, Mat × Mat) :=
  ⟨fun Q => (0, fExt (packChartJet Q)),
    continuous_const.prodMk (fExt.continuous.comp contDiff_packChartJet.continuous)⟩

def coordinateSourcePath (fExt : C(ChartState (n := n) × ChartState (n := n), Mat))
    (U : P → C(K, Mat × Mat)) (y : P) : C(K, Mat × Mat) :=
  (sourceMap fExt).comp (coordinateJetPath U y)

theorem coordinateSourcePath_apply (fExt : C(ChartState (n := n) × ChartState (n := n), Mat))
    (U : P → C(K, Mat × Mat)) (y : P) (t : K) :
    coordinateSourcePath fExt U y t =
      finiteSource fExt (y, finiteJet 2 (fun w => wordDerivative w U y t)) := by
  change (0, fExt (packChartJet (coordinateJetPath U y t))) = _
  rw [coordinateJetPath_apply]
  rfl

theorem contDiffOn_coordinateSourcePath
    (fExt : C(ChartState (n := n) × ChartState (n := n), Mat))
    (hfExt : ContDiff ℝ ∞ fExt) {Omega : Set P} (hOmega : IsOpen Omega)
    {U : P → C(K, Mat × Mat)} (hU : ContDiffOn ℝ ∞ U Omega) :
    ContDiffOn ℝ ∞ (coordinateSourcePath fExt U) Omega :=
  (contDiff_postcomp K (sourceMap fExt)
    (contDiff_const.prodMk (hfExt.comp contDiff_packChartJet))).comp_contDiffOn
      (contDiffOn_coordinateJetPath hOmega hU)


theorem exists_coordinate_source_extension (base : M) (U : P → C(K, Mat × Mat))
    (hU : ContDiffOn ℝ ∞ U (chartDomain base)) (g : K → RiemannianMetric n M)
    (hvalue : ∀ y t, U y t =
      (coordinateMetricEntries g0 base y, coordinateMetricEntries (g t) base y))
    {Omega : Set P} (hclosure : closure Omega ⊆ chartDomain base)
    (hcompact : IsCompact (closure Omega)) :
    ∃ fExt : C(ChartState (n := n) × ChartState (n := n), Mat),
      ContDiff ℝ ∞ fExt ∧ ∀ y ∈ closure Omega, ∀ t : K,
        fExt (packChartJet (coordinateJetPath U y t)) =
          chartStateSource (chartStateJet (packChartJet (coordinateJetPath U y t)).1)
            (packChartJet (coordinateJetPath U y t)).2 := by
  let J : K × P → ChartState (n := n) × ChartState (n := n) :=
    fun q => packChartJet (coordinateJetPath U q.2 q.1)
  let S : Set (ChartState (n := n) × ChartState (n := n)) :=
    J '' (univ ×ˢ closure Omega)
  have hj : ContinuousOn J (univ ×ˢ closure Omega) :=
    contDiff_packChartJet.continuous.comp_continuousOn
      (continuous_eval.comp_continuousOn
        ((((contDiffOn_coordinateJetPath (isOpen_chartDomain base) hU).continuousOn).comp
          continuous_snd.continuousOn (fun q hq => hclosure hq.2)).prodMk
            continuous_fst.continuousOn))
  have hS : IsCompact S := (isCompact_univ.prod hcompact).image_of_continuousOn hj
  let V : Set (ChartState (n := n) × ChartState (n := n)) :=
    {q | q.1.1.det ≠ 0 ∧ q.2.1.det ≠ 0}
  have hV : IsOpen V :=
    (isOpen_ne_fun continuous_fst.fst.matrix_det continuous_const).inter
      (isOpen_ne_fun continuous_snd.fst.matrix_det continuous_const)
  have hSV : S ⊆ V := by
    rintro _ ⟨⟨t, y⟩, hy, rfl⟩
    have heq : J (t, y) = packChartJet (finiteJet 2 (fun w => wordDerivative w U y t)) := by
      dsimp only [J]
      rw [coordinateJetPath_apply]
    rw [heq]
    change (matrixSlot false (U y t)).det ≠ 0 ∧ (matrixSlot true (U y t)).det ≠ 0
    rw [hvalue]
    exact ⟨ne_of_gt (coordinateMetricEntries_posDef g0 base (hclosure hy.2)).det_pos,
      ne_of_gt (coordinateMetricEntries_posDef (g t) base (hclosure hy.2)).det_pos⟩
  obtain ⟨fExt, hfExt, O, hO, hSO, hEq⟩ :=
    exists_contDiff_extension_near_compact hS hV hSV
      (fun q => chartStateSource (chartStateJet q.1) q.2)
      (fun q hq => contDiffAt_jointChartStateSource_of_det_ne_zero q hq.1 hq.2)
  refine ⟨fExt, hfExt, ?_⟩
  intro y hy t
  exact hEq (hSO ⟨(t, y), ⟨mem_univ t, hy⟩, rfl⟩)

theorem coordinateSourcePath_eq_intrinsic (base : M) (U : P → C(K, Mat × Mat))
    (hU : ContDiffOn ℝ ∞ U (chartDomain base)) (g : K → RiemannianMetric n M)
    (hvalue : ∀ y t, U y t =
      (coordinateMetricEntries g0 base y, coordinateMetricEntries (g t) base y))
    (fExt : C(ChartState (n := n) × ChartState (n := n), Mat))
    {y : P} (hy : y ∈ chartDomain base) (t : K)
    (hext : fExt (packChartJet (coordinateJetPath U y t)) =
      chartStateSource (chartStateJet (packChartJet (coordinateJetPath U y t)).1)
        (packChartJet (coordinateJetPath U y t)).2) :
    coordinateSourcePath fExt U y t = (0, fun i j =>
      MetricFamilyProducerNative.deTurckRHS g0 (g t) (chartPoint base y)
        (chartFrame base i (chartPoint base y)) (chartFrame base j (chartPoint base y))) := by
  have hB := packChartState_eq_frameMetricJet base U hU false (fun _ => g0)
    (fun q s => by rw [hvalue]; rfl) hy t
  have hG := packChartState_eq_frameMetricJet base U hU true g
    (fun q s => by rw [hvalue]; rfl) hy t
  change (0, fExt (packChartJet (coordinateJetPath U y t))) = (0, _)
  refine Prod.ext rfl ?_
  funext i j
  change fExt (packChartJet (coordinateJetPath U y t)) i j = _
  rw [hext]
  change ricciDeTurckSource
    (chartStateJet (packChartState false (coordinateJetPath U y t)))
    (chartStateJet (packChartState true (coordinateJetPath U y t))) i j = _
  rw [hB, hG]
  exact ricciDeTurckSource_frameMetricJet_eq_intrinsic
    (MetricFamilyProducerNative.connection (g t)) (MetricFamilyProducerNative.connection g0)
    base (chartPoint_mem_source base hy) i j

end CompactSource

section ChartBootstrap

variable {T : ℝ} (hT : 0 < T)

private theorem path_integral_eq_of_derivative
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (U S : C(Icc (0 : ℝ) T, Z))
    (hd : ∀ t (ht : t ∈ Icc (0 : ℝ) T),
      HasDerivWithinAt (IccExtend hT.le U) (S ⟨t, ht⟩) (Icc (0 : ℝ) T) t) :
    U = ContinuousMap.const _ (U ⟨0, by simp [hT.le]⟩) + integralOperator hT.le S := by
  ext t
  have hu : Continuous (IccExtend hT.le U) := U.continuous.comp continuous_projIcc
  have hs : Continuous (IccExtend hT.le S) := S.continuous.comp continuous_projIcc
  have hd' : ∀ s ∈ Ioo (0 : ℝ) (t : ℝ),
      HasDerivAt (IccExtend hT.le U) (IccExtend hT.le S s) s := by
    intro s hs0
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs0.1.le, hs0.2.le.trans t.2.2⟩
    rw [IccExtend_of_mem hT.le S hsT]
    exact (hd s hsT).hasDerivAt (Icc_mem_nhds hs0.1 (hs0.2.trans_le t.2.2))
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.2.1 hu.continuousOn hd'
    (hs.intervalIntegrable 0 t)
  rw [IccExtend_of_mem hT.le U t.2, IccExtend_of_mem hT.le U (by simp [hT.le])] at hint
  change U t = U ⟨0, by simp [hT.le]⟩ + ∫ s in (0 : ℝ)..t, IccExtend hT.le S s
  rw [hint]
  abel


theorem coordinatePairPath_hasDerivWithinAt (base : M)
    (U : P → C(Icc (0 : ℝ) T, Mat × Mat))
    (hU : ContDiffOn ℝ ∞ U (chartDomain base)) (g : ℝ → RiemannianMetric n M)
    (hvalue : ∀ y (t : Icc (0 : ℝ) T), U y t =
      (coordinateMetricEntries g0 base y, coordinateMetricEntries (g t) base y))
    (heq : ∀ t, t ∈ Icc (0 : ℝ) T → ∀ x (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g s).inner x v w)
        (MetricFamilyProducerNative.deTurckRHS g0 (g t) x v w) (Icc (0 : ℝ) T) t)
    (fExt : C(ChartState (n := n) × ChartState (n := n), Mat))
    {y : P} (hy : y ∈ chartDomain base) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (hext : fExt (packChartJet (coordinateJetPath U y ⟨t, ht⟩)) =
      chartStateSource (chartStateJet (packChartJet (coordinateJetPath U y ⟨t, ht⟩)).1)
        (packChartJet (coordinateJetPath U y ⟨t, ht⟩)).2) :
    HasDerivWithinAt (IccExtend hT.le (U y))
      (coordinateSourcePath fExt U y ⟨t, ht⟩) (Icc (0 : ℝ) T) t := by
  rw [coordinateSourcePath_eq_intrinsic base U hU (fun a => g a) hvalue fExt hy ⟨t, ht⟩ hext]
  have hB : HasDerivWithinAt (fun s => (IccExtend hT.le (U y) s).1) (0 : Mat)
      (Icc (0 : ℝ) T) t := by
    have he : (fun s => (IccExtend hT.le (U y) s).1) =
        (fun _ : ℝ => coordinateMetricEntries g0 base y) := by
      funext s
      exact congrArg Prod.fst (hvalue y (projIcc 0 T hT.le s))
    rw [he]
    exact hasDerivWithinAt_const _ _ _
  have hG : HasDerivWithinAt (fun s => (IccExtend hT.le (U y) s).2)
      (fun i j => MetricFamilyProducerNative.deTurckRHS g0 (g t) (chartPoint base y)
        (chartFrame base i (chartPoint base y)) (chartFrame base j (chartPoint base y)))
      (Icc (0 : ℝ) T) t := by
    apply hasDerivWithinAt_pi.mpr
    intro i
    apply hasDerivWithinAt_pi.mpr
    intro j
    apply (heq t ht (chartPoint base y) (chartFrame base i (chartPoint base y))
      (chartFrame base j (chartPoint base y))).congr_of_mem _ ht
    intro s hs
    rw [IccExtend_of_mem hT.le (U y) hs, hvalue]
    rfl
  exact hB.prodMk hG

include hT in
theorem exists_joint_smooth_coordinateEntries (base : M)
    (U : P → C(Icc (0 : ℝ) T, Mat × Mat))
    (hU : ContDiffOn ℝ ∞ U (chartDomain base)) (g : ℝ → RiemannianMetric n M)
    (hvalue : ∀ y (t : Icc (0 : ℝ) T), U y t =
      (coordinateMetricEntries g0 base y, coordinateMetricEntries (g t) base y))
    (heq : ∀ t, t ∈ Icc (0 : ℝ) T → ∀ x (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g s).inner x v w)
        (MetricFamilyProducerNative.deTurckRHS g0 (g t) x v w) (Icc (0 : ℝ) T) t) :
    ∃ Omega : Set P, IsOpen Omega ∧ coordinateOf base base ∈ Omega ∧
      Omega ⊆ chartDomain base ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × P => coordinateMetricEntries (g q.1) base q.2)
        (Icc (0 : ℝ) T ×ˢ Omega) := by
  obtain ⟨Omega, hOmega, hmem, hclosure, hcompact⟩ := exists_precompact_chartDomain (n := n) base
  have hsub : Omega ⊆ chartDomain base := subset_closure.trans hclosure
  obtain ⟨fExt, hfExt, hext⟩ := exists_coordinate_source_extension base U hU (fun t => g t)
    hvalue hclosure hcompact
  let S := coordinateSourcePath fExt U
  let initial : P → Mat × Mat := fun y => U y ⟨0, by simp [hT.le]⟩
  have hS : ContDiffOn ℝ ∞ S Omega :=
    contDiffOn_coordinateSourcePath fExt hfExt hOmega (hU.mono hsub)
  have hinitial : ContDiffOn ℝ ∞ initial Omega :=
    (ContinuousMap.evalCLM ℝ (M := Mat × Mat)
      (⟨0, by simp [hT.le]⟩ : Icc (0 : ℝ) T)).contDiff.comp_contDiffOn (hU.mono hsub)
  have hint : ∀ y ∈ Omega, U y = ContinuousMap.const _ (initial y) + integralOperator hT.le (S y) := by
    intro y hy
    apply path_integral_eq_of_derivative hT
    intro t ht
    exact coordinatePairPath_hasDerivWithinAt hT base U hU g hvalue heq fExt (hsub hy) t ht
      (hext y (subset_closure hy) ⟨t, ht⟩)
  have hjoint := joint_smooth_of_integral_finite_jet hT.le (contDiff_finiteSource fExt hfExt)
    hT hOmega U S initial (hU.mono hsub) hS hinitial hint
      (fun y _ t => coordinateSourcePath_apply fExt U y t)
  refine ⟨Omega, hOmega, hmem, hsub, ?_⟩
  apply hjoint.snd.congr
  intro q hq
  rw [hvalue]
  rw [projIcc_of_mem hT.le hq.1]

end ChartBootstrap

section BundleRecovery

theorem sum_chartFieldOnSource_frame (base : M)
    (V : SmoothField (n := n) (M := M)) {x : M} (hx : x ∈ (chartAt E base).source) :
    (∑ i, chartFieldOnSource base V x i • chartFrame base i x) = V x := by
  let e := chartDifferentialEquiv base x hx
  have he : e (V x) = chartFieldOnSource base V x := by
    change (chartDifferentialEquiv base x hx : TangentSpace I x →L[ℝ] E) (V x) = _
    rw [chartDifferentialEquiv_coe]
    rfl
  have hb (i : Fin n) : e (chartFrame base i x) = (PiLp.basisFun 2 ℝ (Fin n)) i := by
    rw [chartFrame_eq_basis base x hx]
    change e (e.symm ((PiLp.basisFun 2 ℝ (Fin n)) i)) = _
    exact e.apply_symm_apply _
  apply e.injective
  simp only [map_sum, map_smul, hb]
  rw [← he]
  simpa only [PiLp.basisFun_repr] using (PiLp.basisFun 2 ℝ (Fin n)).sum_repr (e (V x))

theorem contMDiffOn_chartFieldCoefficient (base : M)
    (V : SmoothField (n := n) (M := M)) (i : Fin n) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => chartFieldOnSource base V x i)
      (chartAt E base).source := by
  let A : E →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (coordinateModel n).symm.toContinuousLinearMap
  exact A.contMDiff.comp_contMDiffOn (contMDiffOn_chartFieldOnSource base V)

theorem metricPair_chart_sum (g : RiemannianMetric n M) (base : M)
    (V W : SmoothField (n := n) (M := M)) {x : M} (hx : x ∈ (chartAt E base).source) :
    g.inner x (V x) (W x) = ∑ i : Fin n, ∑ j : Fin n,
      (chartFieldOnSource base V x i * chartFieldOnSource base W x j) *
        g.inner x (chartFrame base i x) (chartFrame base j x) := by
  have hV := sum_chartFieldOnSource_frame base V hx
  have hW := sum_chartFieldOnSource_frame base W hx
  conv_lhs => rw [← hV, ← hW]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem contMDiffOn_metricPair_of_local_coordinates {J : Set ℝ}
    (g : ℝ → RiemannianMetric n M)
    (hlocal : ∀ base : M, ∃ Omega : Set P, IsOpen Omega ∧ coordinateOf base base ∈ Omega ∧
      Omega ⊆ chartDomain base ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × P => coordinateMetricEntries (g q.1) base q.2)
        (J ×ˢ Omega))
    (V W : SmoothField (n := n) (M := M)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => (g q.1).inner q.2 (V q.2) (W q.2)) (J ×ˢ univ) := by
  intro q hq
  let base := q.2
  obtain ⟨Omega, hOmega, hbase, hsub, hregular⟩ := hlocal base
  let A : Set M := (chartAt E base).source ∩ coordinateOf base ⁻¹' Omega
  have hx : base ∈ (chartAt E base).source := mem_chart_source E base
  have hcoord := (contMDiffOn_coordinateOf base).contMDiffAt
    ((chartAt E base).open_source.mem_nhds hx)
  have hA : A ∈ 𝓝 base := inter_mem ((chartAt E base).open_source.mem_nhds hx)
    (hcoord.continuousAt.preimage_mem_nhds (hOmega.mem_nhds hbase))
  have hsmall : J ×ˢ A ∈ 𝓝[J ×ˢ univ] q := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (continuous_snd.continuousAt.preimage_mem_nhds hA)]
      with a ha haA
    exact ⟨ha.1, haA⟩
  have hmap : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × P) ∞
      (fun a : ℝ × M => (a.1, coordinateOf base a.2)) (J ×ˢ A) :=
    contMDiffOn_fst.prodMk_space
      ((contMDiffOn_coordinateOf base).comp contMDiffOn_snd (fun _ ha => ha.2.1))
  have hentries : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, Mat) ∞
      (fun a : ℝ × M => coordinateMetricEntries (g a.1) base (coordinateOf base a.2))
      (J ×ˢ A) :=
    hregular.contMDiffOn.comp hmap (fun _ ha => ⟨ha.1, ha.2.2⟩)
  have hsum : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun a : ℝ × M => ∑ i : Fin n, ∑ j : Fin n,
        (chartFieldOnSource base V a.2 i * chartFieldOnSource base W a.2 j) *
          coordinateMetricEntries (g a.1) base (coordinateOf base a.2) i j) (J ×ˢ A) :=
    contMDiffOn_finsetSum (fun i _ => contMDiffOn_finsetSum (fun j _ =>
      (((contMDiffOn_chartFieldCoefficient base V i).comp contMDiffOn_snd
        (fun _ ha => ha.2.1)).mul
        ((contMDiffOn_chartFieldCoefficient base W j).comp contMDiffOn_snd
          (fun _ ha => ha.2.1))).mul
            (contMDiffOn_pi_space.mp (contMDiffOn_pi_space.mp hentries i) j)))
  have heq : EqOn (fun a : ℝ × M => (g a.1).inner a.2 (V a.2) (W a.2))
      (fun a : ℝ × M => ∑ i : Fin n, ∑ j : Fin n,
        (chartFieldOnSource base V a.2 i * chartFieldOnSource base W a.2 j) *
          coordinateMetricEntries (g a.1) base (coordinateOf base a.2) i j) (J ×ˢ A) := by
    intro a ha
    have hpoint := chartPoint_coordinateOf base ha.2.1
    change (g a.1).inner a.2 (V a.2) (W a.2) =
      ∑ i : Fin n, ∑ j : Fin n,
        (chartFieldOnSource base V a.2 i * chartFieldOnSource base W a.2 j) *
          (g a.1).inner (chartPoint base (coordinateOf base a.2))
            (chartFrame base i (chartPoint base (coordinateOf base a.2)))
            (chartFrame base j (chartPoint base (coordinateOf base a.2)))
    rw [hpoint]
    exact metricPair_chart_sum (g a.1) base V W ha.2.1
  exact ((hsum.congr heq) q ⟨hq.1, hx, hbase⟩).mono_of_mem_nhdsWithin hsmall


theorem isSmoothFamilyOn_of_local_coordinates_fields {A : Type*} [Fintype A]
    (background : RiemannianMetric n M) (F : A → SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace I x),
      (∑ a, background.inner x (F a x) v • F a x) = v) {J : Set ℝ}
    (g : ℝ → RiemannianMetric n M)
    (hlocal : ∀ base : M, ∃ Omega : Set P, IsOpen Omega ∧ coordinateOf base base ∈ Omega ∧
      Omega ⊆ chartDomain base ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × P => coordinateMetricEntries (g q.1) base q.2)
        (J ×ˢ Omega)) : RiemannianMetric.IsSmoothFamilyOn g J := by
  let C : ℝ × M → Coefficients A := fun q => probes F (metricTensor (g q.1)) q.2
  have hC : ∀ ab : A × A,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q => C q ab) (J ×ˢ univ) :=
    fun ab => contMDiffOn_metricPair_of_local_coordinates g hlocal (F ab.1) (F ab.2)
  have hdecode := nativeDecode_contMDiffOn_spacetime background F C hC
  have heq (q : ℝ × M) : nativeDecode background F q.2 (C q) = (g q.1).inner q.2 :=
    nativeDecode_probes background F hF (metricTensor (g q.1)) q.2
  simpa only [RiemannianMetric.IsSmoothFamilyOn, heq] using hdecode

end BundleRecovery

include d in
theorem isSmoothFamilyOn_of_local_coordinates {J : Set ℝ}
    (g : ℝ → RiemannianMetric n M)
    (hlocal : ∀ base : M, ∃ Omega : Set P, IsOpen Omega ∧ coordinateOf base base ∈ Omega ∧
      Omega ⊆ chartDomain base ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × P => coordinateMetricEntries (g q.1) base q.2)
        (J ×ˢ Omega)) : RiemannianMetric.IsSmoothFamilyOn g J :=
  isSmoothFamilyOn_of_local_coordinates_fields g0 d.fields d.parseval g hlocal

section SmoothFamily

variable {T : ℝ} (hT : 0 < T)
  (r p : ℕ) (hpr : 2 * p ≤ r) (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
  (z : C(Icc (0 : ℝ) T, State d.SymmetricIndex))
  (hspatial : ∀ ab : d.ProbeIndex,
    ContMDiff (𝓡 n) 𝓘(ℝ, C(Icc (0 : ℝ) T, ℝ)) ∞ (probePath d L r p (by omega) hp z ab))
  (hsmall : ∀ t : Icc (0 : ℝ) T,
    ‖d.smoothTensorCoordinates (2 * r + 1)
      (recoveredTensor d L r p (by omega) hp z hspatial t)
      (recoveredTensor_symmetric d L r p (by omega) hp z hspatial t)‖ ≤
        positivityRadius d L r p hpr hp)

include hT in

theorem recoveredMetric_isSmoothFamilyOn (g : ℝ → RiemannianMetric n M)
    (hmetric : ∀ (t : Icc (0 : ℝ) T) (x : M) (v w : TangentSpace I x),
      (g t).inner x v w =
        (recoveredMetric d L r p hpr hp z hspatial hsmall t).inner x v w)
    (heq : ∀ t, t ∈ Icc (0 : ℝ) T → ∀ x (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g s).inner x v w)
        (MetricFamilyProducerNative.deTurckRHS g0 (g t) x v w) (Icc (0 : ℝ) T) t) :
    RiemannianMetric.IsSmoothFamilyOn g (Icc (0 : ℝ) T) := by
  apply isSmoothFamilyOn_of_local_coordinates d g
  intro base
  apply exists_joint_smooth_coordinateEntries hT base
    (coordinatePairPath d L r p hpr hp z base)
    (contDiffOn_coordinatePairPath d L r p hpr hp z hspatial base) g _ heq
  intro y t
  rw [coordinatePairPath_apply d L r p hpr hp z hspatial hsmall]
  refine Prod.ext rfl ?_
  ext i j
  exact (hmetric t (chartPoint base y) (chartFrame base i (chartPoint base y))
    (chartFrame base j (chartPoint base y))).symm

end SmoothFamily

end PoincareConjecture.DeTurckSmoothMetricFamilyNative

end
