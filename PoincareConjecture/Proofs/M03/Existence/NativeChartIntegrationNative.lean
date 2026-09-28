import PoincareConjecture.Proofs.M03.Existence.NativeChartDensityMeasureNative
import PoincareConjecture.Proofs.M03.Existence.NativeChartAdjointNative
import PoincareConjecture.Proofs.M03.Existence.NativeChartScalarLocalization
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology SchwartzMap ENNReal

noncomputable section

universe u

namespace PoincareConjecture.ChartMeasureNative.FiniteChartData

open TensorProbeNative EuclideanDerivativeNative NativeChartScalarLocalization
  ChartPushforwardLpNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

local notation "E" => EuclideanSpace ℝ (Fin n)

variable (d : FiniteChartData (n := n) (M := M))

theorem integral_eq_chartDensity (p : M) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ (chartAt E p).source)
    (hfzero : ∀ x ∉ K, f x = 0) :
    (∫ x, f x ∂d.measure) = ∫ z, d.chartDensity p z * chartScalar (n := n) p f z := by
  let e : OpenPartialHomeomorph M E := chartAt E p
  have hq : Continuous (chartScalar (n := n) p f) :=
    (contDiff_chartScalar p hf hK hKs hfzero).continuous
  have hρ : AEMeasurable (fun z => ENNReal.ofReal (d.chartDensity p z))
      (volume.restrict e.target) :=
    ((d.chartDensity_contDiffOn p).continuousOn.aemeasurable e.open_target.measurableSet).ennreal_ofReal
  calc
    _ = ∫ x in e.source, f x ∂d.measure :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hfzero x (fun hxK => hx (hKs hxK)))).symm
    _ = ∫ x in e.source, chartScalar p f (measurableChart e x) ∂d.measure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx
      rw [measurableChart_of_mem e hx, chartScalar_of_mem p f (e.map_source hx), e.left_inv hx]
    _ = ∫ z, chartScalar p f z ∂((d.measure.restrict e.source).map (measurableChart e)) :=
      (integral_map_of_stronglyMeasurable (measurable_measurableChart e) hq.stronglyMeasurable).symm
    _ = ∫ z in e.target, d.chartDensity p z * chartScalar p f z := by
      rw [d.map_measurableChart_eq_density p,
        integral_withDensity_eq_integral_toReal_smul₀ hρ
          (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      simp only [ENNReal.toReal_ofReal (d.chartDensity_nonneg p _), smul_eq_mul]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [chartScalar_of_notMem p f hz, mul_zero])

theorem coordinateAdjoint_eventuallyEq (p : M) (V : SmoothField (n := n) (M := M))
    {η θ : E → ℝ} {z : E} (h : η =ᶠ[𝓝 z] θ) :
    d.coordinateAdjoint p V η z = d.coordinateAdjoint p V θ z := by
  unfold coordinateAdjoint densityAdjointTest
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun L : E →L[ℝ] ℝ => L ((PiLp.basisFun 2 ℝ (Fin n)) i))
    ((h.mul (EventuallyEq.rfl (f := fun y => d.chartDensity p y * chartField p V y i))).fderiv_eq)

theorem coordinateAdjoint_eq_zero_off_support (p : M) (V : SmoothField (n := n) (M := M))
    {η : E → ℝ} {z : E} (hz : z ∉ tsupport η) : d.coordinateAdjoint p V η z = 0 := by
  unfold coordinateAdjoint densityAdjointTest
  have hsum : (∑ i : Fin n, fderiv ℝ
      (fun y => η y * (d.chartDensity p y * chartField p V y i)) z
        ((PiLp.basisFun 2 ℝ (Fin n)) i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hsub : tsupport (fun y => η y * (d.chartDensity p y * chartField p V y i)) ⊆
        tsupport η := tsupport_mul_subset_left
    rw [fderiv_of_notMem_tsupport ℝ (fun hs => hz (hsub hs)), ContinuousLinearMap.zero_apply]
  rw [hsum, mul_zero]

theorem scalarDirectional_eq_zero_off_support (V : SmoothField (n := n) (M := M))
    {f : M → ℝ} {x : M} (hx : x ∉ tsupport f) : scalarDirectional V f x = 0 := by
  have hzero : f =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := notMem_tsupport_iff_eventuallyEq.mp hx
  unfold scalarDirectional
  rw [hzero.mfderiv_eq, mfderiv_const, ContinuousLinearMap.zero_apply]

variable [CompactSpace M]

def partitionTest (i : d.centers) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) : 𝓢(E, ℝ) :=
  (chartScalar_compactSupport i.val (f := fun x => d.weight i x * f x)
    (d.weight_compactSupport i) (d.weight_support_subset i)
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])).toSchwartzMap
      (contDiff_chartScalar i.val ((d.weight_smooth i).mul hf) (d.weight_compactSupport i)
        (d.weight_support_subset i)
        (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]))

@[simp] theorem partitionTest_apply (i : d.centers) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (z : E) :
    d.partitionTest i hf z = chartScalar i.val (fun x => d.weight i x * f x) z := rfl

theorem partitionTest_tsupport_subset (i : d.centers) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    tsupport (d.partitionTest i hf) ⊆ (d.chart i).target :=
  (tsupport_chartScalar_subset i.val (f := fun x => d.weight i x * f x)
    (d.weight_compactSupport i) (d.weight_support_subset i)
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])).trans
      (by rintro _ ⟨x, hx, rfl⟩; exact (d.chart i).map_source (d.weight_support_subset i hx))

theorem partitionTest_compactSupport (i : d.centers) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) : HasCompactSupport (d.partitionTest i hf) :=
  chartScalar_compactSupport i.val (f := fun x => d.weight i x * f x)
    (d.weight_compactSupport i) (d.weight_support_subset i)
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])

def partitionAdjoint (i : d.centers) (V : SmoothField (n := n) (M := M))
    (f : M → ℝ) (x : M) : ℝ :=
  -scalarDirectional V (fun y => d.weight i y * f y) x -
    (d.weight i x * d.coordinateDivergence i.val V (d.chart i x)) * f x

theorem partitionAdjoint_contMDiff (i : d.centers) (V : SmoothField (n := n) (M := M))
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (d.partitionAdjoint i V f) :=
  (contMDiff_directional ((d.weight_smooth i).mul hf) V).neg.sub
    ((d.weight_mul_coordinateDivergence_contMDiff i V).mul hf)

theorem partitionAdjoint_eq_zero_off_weight (i : d.centers)
    (V : SmoothField (n := n) (M := M)) (f : M → ℝ) {x : M}
    (hx : x ∉ tsupport (d.weight i)) : d.partitionAdjoint i V f x = 0 := by
  have hproduct : x ∉ tsupport (fun y => d.weight i y * f y) :=
    fun hs => hx (tsupport_mul_subset_left hs)
  unfold partitionAdjoint
  rw [scalarDirectional_eq_zero_off_support V hproduct,
    image_eq_zero_of_notMem_tsupport hx]
  ring

theorem coordinateAdjoint_partitionTest (i : d.centers)
    (V : SmoothField (n := n) (M := M)) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {z : E}
    (hz : z ∈ (d.chart i).target) :
    d.coordinateAdjoint i.val V (d.partitionTest i hf) z =
      d.partitionAdjoint i V f ((d.chart i).symm z) := by
  change d.coordinateAdjoint i.val V
    (chartScalar i.val (fun x => d.weight i x * f x)) z = _
  rw [d.coordinateAdjoint_eventuallyEq i.val V
    (chartScalar_eventuallyEq i.val (fun x => d.weight i x * f x) hz)]
  have hwf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => d.weight i x * f x) :=
    (d.weight_smooth i).mul hf
  rw [d.coordinateAdjoint_native i.val V hwf hz]
  unfold partitionAdjoint
  rw [(d.chart i).right_inv hz]
  dsimp only [FiniteChartData.chart]
  ring

theorem integral_partition_directional_eq_adjoint (i : d.centers)
    (V : SmoothField (n := n) (M := M)) {f η : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η) :
    (∫ x, d.weight i x * scalarDirectional V f x * η x ∂d.measure) =
      ∫ x, f x * d.partitionAdjoint i V η x ∂d.measure := by
  let e : OpenPartialHomeomorph M E := d.chart i
  have hleft : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => d.weight i x * scalarDirectional V f x * η x) :=
    ((d.weight_smooth i).mul (contMDiff_directional hf V)).mul hη
  have hright : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => f x * d.partitionAdjoint i V η x) :=
    hf.mul (d.partitionAdjoint_contMDiff i V hη)
  have hleftzero : ∀ x ∉ tsupport (d.weight i),
      d.weight i x * scalarDirectional V f x * η x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have hrightzero : ∀ x ∉ tsupport (d.weight i),
      f x * d.partitionAdjoint i V η x = 0 := by
    intro x hx
    rw [d.partitionAdjoint_eq_zero_off_weight i V η hx, mul_zero]
  calc
    _ = ∫ z, d.chartDensity i.val z *
        chartScalar i.val (fun x => d.weight i x * scalarDirectional V f x * η x) z :=
      d.integral_eq_chartDensity i.val hleft (d.weight_compactSupport i)
        (d.weight_support_subset i) hleftzero
    _ = ∫ z, d.chartDensity i.val z * scalarDirectional V f (e.symm z) *
        d.partitionTest i hη z := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      dsimp only
      rw [d.partitionTest_apply]
      by_cases hz : z ∈ e.target
      · rw [chartScalar_of_mem i.val _ hz, chartScalar_of_mem i.val _ hz]
        change d.chartDensity i.val z *
          (d.weight i (e.symm z) * scalarDirectional V f (e.symm z) * η (e.symm z)) =
          d.chartDensity i.val z * scalarDirectional V f (e.symm z) *
            (d.weight i (e.symm z) * η (e.symm z))
        ring
      · rw [chartScalar_of_notMem i.val _ hz, chartScalar_of_notMem i.val _ hz,
          mul_zero, mul_zero]
    _ = ∫ z, d.chartDensity i.val z * f (e.symm z) *
        d.coordinateAdjoint i.val V (d.partitionTest i hη) z :=
      d.integral_nativeDirectional_chart_eq_adjoint i.val V (d.partitionTest i hη)
        (d.partitionTest_compactSupport i hη) (d.partitionTest_tsupport_subset i hη) hf
    _ = ∫ z, d.chartDensity i.val z *
        chartScalar i.val (fun x => f x * d.partitionAdjoint i V η x) z := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      dsimp only
      by_cases hz : z ∈ e.target
      · rw [d.coordinateAdjoint_partitionTest i V hη hz, chartScalar_of_mem i.val _ hz]
        change d.chartDensity i.val z * f (e.symm z) * d.partitionAdjoint i V η (e.symm z) =
          d.chartDensity i.val z * (f (e.symm z) * d.partitionAdjoint i V η (e.symm z))
        ring
      · rw [d.coordinateAdjoint_eq_zero_off_support i.val V
          (fun hs => hz (d.partitionTest_tsupport_subset i hη hs)),
          chartScalar_of_notMem i.val _ hz, mul_zero, mul_zero]
    _ = _ := (d.integral_eq_chartDensity i.val hright (d.weight_compactSupport i)
      (d.weight_support_subset i) hrightzero).symm

theorem sum_weight_directional_eq_zero (V : SmoothField (n := n) (M := M)) (x : M) :
    (∑ i : d.centers, scalarDirectional V (d.weight i) x) = 0 := by
  classical
  have hsum : (fun y => ∑ i : d.centers, d.weight i y) = fun _ => (1 : ℝ) :=
    funext d.weight_sum
  calc
    _ = scalarDirectional V (fun y => ∑ i : d.centers, d.weight i y) x :=
      (scalarDirectional_finsetSum_smooth Finset.univ V
        (fun i : d.centers => (d.weight i : M → ℝ)) (fun i _ => d.weight_smooth i) x).symm
    _ = 0 := by rw [hsum]; simp only [scalarDirectional, mfderiv_const, ContinuousLinearMap.zero_apply]

theorem sum_partitionAdjoint_eq (V : SmoothField (n := n) (M := M)) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    (∑ i : d.centers, d.partitionAdjoint i V f x) = d.fieldAdjoint V f x := by
  classical
  have hpoint (i : d.centers) : d.partitionAdjoint i V f x =
      -(d.weight i x * scalarDirectional V f x) -
        f x * scalarDirectional V (d.weight i) x -
        (d.weight i x * d.coordinateDivergence i.val V (d.chart i x)) * f x := by
    unfold partitionAdjoint
    rw [scalarDirectional_mul V ((d.weight_smooth i).mdifferentiable (by simp) x)
      (hf.mdifferentiable (by simp) x)]
    ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul,
    d.weight_sum, d.sum_weight_directional_eq_zero]
  simp only [one_mul, mul_zero, sub_zero, fieldAdjoint, fieldDivergence]

theorem integral_directional_eq_adjoint (V : SmoothField (n := n) (M := M))
    {f η : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η) :
    (∫ x, scalarDirectional V f x * η x ∂d.measure) =
      ∫ x, f x * d.fieldAdjoint V η x ∂d.measure := by
  classical
  have hleft (i : d.centers) : Integrable
      (fun x => d.weight i x * scalarDirectional V f x * η x) d.measure :=
    (((d.weight i).continuous.mul (contMDiff_directional hf V).continuous).mul
      hη.continuous).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  have hright (i : d.centers) : Integrable
      (fun x => f x * d.partitionAdjoint i V η x) d.measure :=
    (hf.continuous.mul (d.partitionAdjoint_contMDiff i V hη).continuous).integrable_of_hasCompactSupport
      (isClosed_tsupport _).isCompact
  calc
    _ = ∫ x, ∑ i : d.centers, d.weight i x * scalarDirectional V f x * η x ∂d.measure := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      rw [← Finset.sum_mul, ← Finset.sum_mul, d.weight_sum, one_mul]
    _ = ∑ i : d.centers,
        ∫ x, d.weight i x * scalarDirectional V f x * η x ∂d.measure :=
      integral_finsetSum Finset.univ (fun i _ => hleft i)
    _ = ∑ i : d.centers, ∫ x, f x * d.partitionAdjoint i V η x ∂d.measure :=
      Finset.sum_congr rfl (fun i _ => d.integral_partition_directional_eq_adjoint i V hf hη)
    _ = ∫ x, ∑ i : d.centers, f x * d.partitionAdjoint i V η x ∂d.measure :=
      (integral_finsetSum Finset.univ (fun i _ => hright i)).symm
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      rw [← Finset.mul_sum, d.sum_partitionAdjoint_eq V hη]

def principalDrift (V : SmoothField (n := n) (M := M)) (a : M → ℝ) (x : M) : ℝ :=
  scalarDirectional V a x + d.fieldDivergence V x * a x

theorem principalDrift_contMDiff (V : SmoothField (n := n) (M := M))
    {a : M → ℝ} (ha : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ a) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (d.principalDrift V a) :=
  (contMDiff_directional ha V).add ((d.fieldDivergence_contMDiff V).mul ha)

theorem exists_principalDrift_bound (V : SmoothField (n := n) (M := M))
    {a : M → ℝ} (ha : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : M, |d.principalDrift V a x| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_univ.bddAbove_image
    (d.principalDrift_contMDiff V ha).continuous.abs.continuousOn
  exact ⟨max B 0, le_max_right _ _, fun x =>
    (hB ⟨x, mem_univ x, rfl⟩).trans (le_max_left _ _)⟩

theorem integral_principal_pairing_eq
    (V W : SmoothField (n := n) (M := M)) {a f : M → ℝ}
    (ha : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ a)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    (∫ x, -a x * f x * scalarDirectional V (scalarDirectional W f) x ∂d.measure) =
      ∫ x, a x * scalarDirectional V f x * scalarDirectional W f x +
        d.principalDrift V a x * f x * scalarDirectional W f x ∂d.measure := by
  have hpair := d.integral_directional_eq_adjoint V
    (f := scalarDirectional W f) (η := fun y => a y * f y)
    (contMDiff_directional hf W) (ha.mul hf)
  calc
    _ = -(∫ x, scalarDirectional V (scalarDirectional W f) x * (a x * f x) ∂d.measure) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by ring)
    _ = -(∫ x, scalarDirectional W f x * d.fieldAdjoint V (fun y => a y * f y) x
        ∂d.measure) := congrArg Neg.neg hpair
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      rw [fieldAdjoint, scalarDirectional_mul V
        (ha.mdifferentiable (by simp) x) (hf.mdifferentiable (by simp) x)]
      dsimp only [principalDrift]
      ring

private theorem principal_pairing_pointwise_le {a b p q z delta B epsilon : ℝ}
    (hdelta : 0 ≤ delta) (hB : 0 ≤ B) (hepsilon : 0 < epsilon)
    (ha : |a| ≤ delta) (hb : |b| ≤ B) :
    |a * p * q + b * z * q| ≤
      (delta / 2) * p ^ 2 + (delta / 2 + epsilon) * q ^ 2 +
        (B ^ 2 / (4 * epsilon)) * z ^ 2 := by
  have hprod : |a * p * q| ≤ (delta / 2) * p ^ 2 + (delta / 2) * q ^ 2 := by
    have hbound : |a * p * q| ≤ delta * |p| * |q| := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ha (abs_nonneg p)) (abs_nonneg q)
    have hs := mul_nonneg hdelta (sq_nonneg (|p| - |q|))
    simp only [sub_sq, sq_abs] at hs
    nlinarith only [hbound, hs]
  have hlow : |b * z * q| ≤ epsilon * q ^ 2 + (B ^ 2 / (4 * epsilon)) * z ^ 2 := by
    have hbound : |b * z * q| ≤ B * |z| * |q| := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hb (abs_nonneg z)) (abs_nonneg q)
    have hyoung : B * |z| * |q| ≤
        epsilon * q ^ 2 + (B ^ 2 / (4 * epsilon)) * z ^ 2 := by
      have hfour : 0 < 4 * epsilon := by positivity
      apply (mul_le_mul_iff_right₀ hfour).mp
      have hs := sq_nonneg (2 * epsilon * |q| - B * |z|)
      simp only [sub_sq, mul_pow, sq_abs] at hs
      have hcancel : (4 * epsilon) * (B ^ 2 / (4 * epsilon)) * z ^ 2 = B ^ 2 * z ^ 2 := by
        rw [mul_div_cancel₀ _ hfour.ne']
      nlinarith only [hs, hcancel]
    exact hbound.trans hyoung
  exact (abs_add_le _ _).trans (by linarith)

theorem abs_integral_principal_pairing_le
    (V W : SmoothField (n := n) (M := M)) {a f : M → ℝ}
    (ha : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ a)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {delta B epsilon : ℝ} (hdelta : 0 ≤ delta) (hB : 0 ≤ B) (hepsilon : 0 < epsilon)
    (habound : ∀ x : M, |a x| ≤ delta)
    (hb : ∀ x : M, |d.principalDrift V a x| ≤ B) :
    |∫ x, -a x * f x * scalarDirectional V (scalarDirectional W f) x ∂d.measure| ≤
      (delta / 2) * (∫ x, scalarDirectional V f x ^ 2 ∂d.measure) +
        (delta / 2 + epsilon) * (∫ x, scalarDirectional W f x ^ 2 ∂d.measure) +
        (B ^ 2 / (4 * epsilon)) * (∫ x, f x ^ 2 ∂d.measure) := by
  let p : M → ℝ := scalarDirectional V f
  let q : M → ℝ := scalarDirectional W f
  let b : M → ℝ := d.principalDrift V a
  have hp : Continuous p := (contMDiff_directional hf V).continuous
  have hq : Continuous q := (contMDiff_directional hf W).continuous
  have hbc : Continuous b := (d.principalDrift_contMDiff V ha).continuous
  have hIp : Integrable (fun x => p x ^ 2) d.measure :=
    (hp.pow 2).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  have hIq : Integrable (fun x => q x ^ 2) d.measure :=
    (hq.pow 2).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  have hIf : Integrable (fun x => f x ^ 2) d.measure :=
    (hf.continuous.pow 2).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  have hI : Integrable (fun x => |a x * p x * q x + b x * f x * q x|) d.measure :=
    ((((ha.continuous.mul hp).mul hq).add ((hbc.mul hf.continuous).mul hq)).abs).integrable_of_hasCompactSupport
      (isClosed_tsupport _).isCompact
  have hIbound : Integrable (fun x =>
      (delta / 2) * p x ^ 2 + (delta / 2 + epsilon) * q x ^ 2 +
        (B ^ 2 / (4 * epsilon)) * f x ^ 2) d.measure :=
    ((hIp.const_mul (delta / 2)).add (hIq.const_mul (delta / 2 + epsilon))).add
      (hIf.const_mul (B ^ 2 / (4 * epsilon)))
  rw [d.integral_principal_pairing_eq V W ha hf]
  change |∫ x, a x * p x * q x + b x * f x * q x ∂d.measure| ≤
    (delta / 2) * (∫ x, p x ^ 2 ∂d.measure) +
      (delta / 2 + epsilon) * (∫ x, q x ^ 2 ∂d.measure) +
      (B ^ 2 / (4 * epsilon)) * (∫ x, f x ^ 2 ∂d.measure)
  calc
    _ ≤ ∫ x, |a x * p x * q x + b x * f x * q x| ∂d.measure := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => a x * p x * q x + b x * f x * q x)
    _ ≤ ∫ x, (delta / 2) * p x ^ 2 + (delta / 2 + epsilon) * q x ^ 2 +
        (B ^ 2 / (4 * epsilon)) * f x ^ 2 ∂d.measure :=
      integral_mono hI hIbound (fun x => principal_pairing_pointwise_le hdelta hB hepsilon
        (habound x) (hb x))
    _ = _ := by
      have hp' : Integrable (fun x => (delta / 2) * p x ^ 2) d.measure :=
        hIp.const_mul (delta / 2)
      have hq' : Integrable (fun x => (delta / 2 + epsilon) * q x ^ 2) d.measure :=
        hIq.const_mul (delta / 2 + epsilon)
      have hf' : Integrable (fun x => (B ^ 2 / (4 * epsilon)) * f x ^ 2) d.measure :=
        hIf.const_mul (B ^ 2 / (4 * epsilon))
      have hsum := integral_add (hp'.add hq') hf'
      simp only [Pi.add_apply] at hsum
      rw [integral_add hp' hq', integral_const_mul,
        integral_const_mul, integral_const_mul] at hsum
      exact hsum

theorem abs_integral_principal_sum_le {iota : Type*} [Fintype iota]
    (V : iota → SmoothField (n := n) (M := M)) {a : iota → iota → M → ℝ}
    {f : M → ℝ}
    (ha : ∀ i j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (a i j))
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {delta epsilon : ℝ} {B : iota → iota → ℝ}
    (hdelta : 0 ≤ delta) (hB : ∀ i j, 0 ≤ B i j) (hepsilon : 0 < epsilon)
    (habound : ∀ i j x, |a i j x| ≤ delta)
    (hb : ∀ i j x, |d.principalDrift (V i) (a i j) x| ≤ B i j) :
    |∫ x, ∑ i, ∑ j, -a i j x * f x *
      scalarDirectional (V i) (scalarDirectional (V j) f) x ∂d.measure| ≤
      (Fintype.card iota : ℝ) * (delta + epsilon) *
        (∑ i, ∫ x, scalarDirectional (V i) f x ^ 2 ∂d.measure) +
      (∑ i, ∑ j, B i j ^ 2 / (4 * epsilon)) * (∫ x, f x ^ 2 ∂d.measure) := by
  classical
  have hI (i j : iota) : Integrable (fun x => -a i j x * f x *
      scalarDirectional (V i) (scalarDirectional (V j) f) x) d.measure :=
    (((ha i j).continuous.neg.mul hf.continuous).mul
      (contMDiff_directional (contMDiff_directional hf (V j)) (V i)).continuous).integrable_of_hasCompactSupport
        (isClosed_tsupport _).isCompact
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _ (fun j _ => hI i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hI _ j)]
  calc
    _ ≤ ∑ i, |∑ j, ∫ x, -a i j x * f x *
        scalarDirectional (V i) (scalarDirectional (V j) f) x ∂d.measure| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |∫ x, -a i j x * f x *
        scalarDirectional (V i) (scalarDirectional (V j) f) x ∂d.measure| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, (
        (delta / 2) * (∫ x, scalarDirectional (V i) f x ^ 2 ∂d.measure) +
        (delta / 2 + epsilon) * (∫ x, scalarDirectional (V j) f x ^ 2 ∂d.measure) +
        (B i j ^ 2 / (4 * epsilon)) * (∫ x, f x ^ 2 ∂d.measure)) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        d.abs_integral_principal_pairing_le (V i) (V j) (ha i j) hf
          hdelta (hB i j) hepsilon (habound i j) (hb i j)))
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
      ring

theorem fieldAdjoint_directional_commutator
    (V W : SmoothField (n := n) (M := M)) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    d.fieldAdjoint V (scalarDirectional W f) x -
        scalarDirectional W (d.fieldAdjoint V f) x =
      -scalarDirectional (smoothFieldBracket V W) f x +
        scalarDirectional W (d.fieldDivergence V) x * f x := by
  have hVf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (scalarDirectional V f) := contMDiff_directional hf V
  have hdiv := d.fieldDivergence_contMDiff V
  have hneg : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => -scalarDirectional V f y) x := hVf.neg.mdifferentiable (by simp) x
  have hmul : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => d.fieldDivergence V y * f y) x := (hdiv.mul hf).mdifferentiable (by simp) x
  unfold fieldAdjoint
  rw [scalarDirectional_sub W hneg hmul,
    scalarDirectional_neg W,
    scalarDirectional_mul W (hdiv.mdifferentiable (by simp) x)
      (hf.mdifferentiable (by simp) x), scalarDirectional_bracket V W hf]
  ring

theorem integral_secondDirectional_sq_eq
    (V W : SmoothField (n := n) (M := M)) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    (∫ x, scalarDirectional V (scalarDirectional W f) x ^ 2 ∂d.measure) =
      (∫ x, d.fieldAdjoint V (scalarDirectional V f) x *
        d.fieldAdjoint W (scalarDirectional W f) x ∂d.measure) +
      (∫ x, scalarDirectional V (scalarDirectional W f) x *
        scalarDirectional (smoothFieldBracket V W) f x ∂d.measure) +
      (∫ x, scalarDirectional W f x *
        (-scalarDirectional (smoothFieldBracket V W) (scalarDirectional V f) x +
          scalarDirectional W (d.fieldDivergence V) x * scalarDirectional V f x)
        ∂d.measure) := by
  have hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (scalarDirectional V f) := contMDiff_directional hf V
  have hW : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (scalarDirectional W f) := contMDiff_directional hf W
  have hVW : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (scalarDirectional V (scalarDirectional W f)) :=
    contMDiff_directional hW V
  have hWV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (scalarDirectional W (scalarDirectional V f)) :=
    contMDiff_directional hV W
  have hB : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (scalarDirectional (smoothFieldBracket V W) f) :=
    contMDiff_directional hf (smoothFieldBracket V W)
  have hBV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (scalarDirectional (smoothFieldBracket V W) (scalarDirectional V f)) :=
    contMDiff_directional hV (smoothFieldBracket V W)
  have hdiv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (scalarDirectional W (d.fieldDivergence V)) :=
    contMDiff_directional (d.fieldDivergence_contMDiff V) W
  have hA := d.fieldAdjoint_contMDiff V hV
  have hDWadj : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (scalarDirectional W (d.fieldAdjoint V (scalarDirectional V f))) := contMDiff_directional hA W
  have hInt (q : M → ℝ) (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q) :
      Integrable q d.measure :=
    hq.continuous.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  have hcomm (x : M) :
      d.fieldAdjoint V (scalarDirectional W (scalarDirectional V f)) x =
        scalarDirectional W (d.fieldAdjoint V (scalarDirectional V f)) x +
          (-scalarDirectional (smoothFieldBracket V W) (scalarDirectional V f) x +
            scalarDirectional W (d.fieldDivergence V) x * scalarDirectional V f x) := by
    have h := d.fieldAdjoint_directional_commutator V W hV x
    linarith
  have hcross :
      (∫ x, scalarDirectional V (scalarDirectional W f) x *
        scalarDirectional W (scalarDirectional V f) x ∂d.measure) =
      (∫ x, d.fieldAdjoint V (scalarDirectional V f) x *
        d.fieldAdjoint W (scalarDirectional W f) x ∂d.measure) +
      (∫ x, scalarDirectional W f x *
        (-scalarDirectional (smoothFieldBracket V W) (scalarDirectional V f) x +
          scalarDirectional W (d.fieldDivergence V) x * scalarDirectional V f x)
        ∂d.measure) := by
    rw [d.integral_directional_eq_adjoint V hW hWV]
    simp_rw [hcomm]
    have hexpand (x : M) :
        scalarDirectional W f x *
          (scalarDirectional W (d.fieldAdjoint V (scalarDirectional V f)) x +
            (-scalarDirectional (smoothFieldBracket V W) (scalarDirectional V f) x +
              scalarDirectional W (d.fieldDivergence V) x * scalarDirectional V f x)) =
          scalarDirectional W f x *
            scalarDirectional W (d.fieldAdjoint V (scalarDirectional V f)) x +
          scalarDirectional W f x *
            (-scalarDirectional (smoothFieldBracket V W) (scalarDirectional V f) x +
              scalarDirectional W (d.fieldDivergence V) x * scalarDirectional V f x) := mul_add _ _ _
    simp_rw [hexpand]
    rw [integral_add
      (f := fun x => scalarDirectional W f x *
        scalarDirectional W (d.fieldAdjoint V (scalarDirectional V f)) x)
      (g := fun x => scalarDirectional W f x *
        (-scalarDirectional (smoothFieldBracket V W) (scalarDirectional V f) x +
          scalarDirectional W (d.fieldDivergence V) x * scalarDirectional V f x))
      (hInt _ (hW.mul hDWadj))
      (hInt _ (hW.mul (hBV.neg.add (hdiv.mul hV))))]
    congr 1
    simpa only [mul_comm] using d.integral_directional_eq_adjoint W hA hW
  have hsplit :
      (∫ x, scalarDirectional V (scalarDirectional W f) x ^ 2 ∂d.measure) =
        (∫ x, scalarDirectional V (scalarDirectional W f) x *
          scalarDirectional W (scalarDirectional V f) x ∂d.measure) +
        (∫ x, scalarDirectional V (scalarDirectional W f) x *
          scalarDirectional (smoothFieldBracket V W) f x ∂d.measure) := by
    rw [← integral_add
      (f := fun x => scalarDirectional V (scalarDirectional W f) x *
        scalarDirectional W (scalarDirectional V f) x)
      (g := fun x => scalarDirectional V (scalarDirectional W f) x *
        scalarDirectional (smoothFieldBracket V W) f x)
      (hInt _ (hVW.mul hWV)) (hInt _ (hVW.mul hB))]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only
    rw [scalarDirectional_bracket V W hf]
    ring
  rw [hsplit, hcross]
  ring

private theorem abs_integral_mul_mul_le {a u v : M → ℝ}
    (ha : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ a)
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    {C epsilon : ℝ} (hC : 0 ≤ C) (hepsilon : 0 < epsilon)
    (hbound : ∀ x, |a x| ≤ C) :
    |∫ x, a x * u x * v x ∂d.measure| ≤
      epsilon * (∫ x, v x ^ 2 ∂d.measure) +
        (C ^ 2 / (4 * epsilon)) * (∫ x, u x ^ 2 ∂d.measure) := by
  have hi : Integrable (fun x => a x * u x * v x) d.measure := (((ha.mul hu).mul hv).continuous.integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact)
  have hiu : Integrable (fun x => u x ^ 2) d.measure := ((hu.pow 2).continuous.integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact)
  have hiv : Integrable (fun x => v x ^ 2) d.measure := ((hv.pow 2).continuous.integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact)
  calc
    _ ≤ ∫ x, |a x * u x * v x| ∂d.measure := abs_integral_le_integral_abs
    _ ≤ ∫ x, epsilon * v x ^ 2 + (C ^ 2 / (4 * epsilon)) * u x ^ 2 ∂d.measure := by
      apply integral_mono hi.abs ((hiv.const_mul _).add (hiu.const_mul _))
      intro x
      simpa using principal_pairing_pointwise_le
        (a := 0) (b := a x) (p := 0) (q := v x) (z := u x)
        (delta := 0) (by norm_num) hC hepsilon (by norm_num) (hbound x)
    _ = _ := by rw [integral_add (hiv.const_mul _) (hiu.const_mul _),
      integral_const_mul, integral_const_mul]

theorem exists_directional_divergence_bound {iota : Type*} [Fintype iota]
    (F : iota → SmoothField (n := n) (M := M)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (i j : iota) (x : M),
      |scalarDirectional (F j) (d.fieldDivergence (F i)) x| ≤ B := by
  classical
  have hb (i : iota) := exists_scalarDirectional_bound F (d.fieldDivergence_contMDiff (F i))
  choose b hb0 hb using hb
  refine ⟨∑ i, b i, Finset.sum_nonneg (fun i _ => hb0 i), ?_⟩
  intro i j x
  exact (hb i j x).trans (Finset.single_le_sum (fun k _ => hb0 k) (Finset.mem_univ i))

theorem exists_secondDirectional_energy_bound {iota : Type*} [Fintype iota]
    (g : RiemannianMetric n M) (F : iota → SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ k, g.inner x (F k x) v • F k x) = v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : M → ℝ), ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f →
      (∑ i, ∑ j, ∫ x, scalarDirectional (F i) (scalarDirectional (F j) f) x ^ 2
        ∂d.measure) ≤
      2 * (∫ x, (∑ i, d.fieldAdjoint (F i) (scalarDirectional (F i) f) x) ^ 2
        ∂d.measure) + C * (∑ i, ∫ x, scalarDirectional (F i) f x ^ 2 ∂d.measure) := by
  classical
  obtain ⟨B, hB, hb⟩ := exists_bracketCoefficient_bound g F
  obtain ⟨D, hD, hd⟩ := d.exists_directional_divergence_bound F
  let N : ℝ := Fintype.card iota
  have hN : 0 ≤ N := Nat.cast_nonneg _
  let epsilon : ℝ := 1 / (4 * (N + 1) ^ 3)
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  let Q : ℝ := B ^ 2 / (4 * epsilon)
  have hQ : 0 ≤ Q := div_nonneg (sq_nonneg _) (by positivity)
  let C : ℝ := 2 * (2 * N ^ 3 * Q + N ^ 2 * (1 + D ^ 2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro f hf
  let Efirst : ℝ := ∑ i, ∫ x, scalarDirectional (F i) f x ^ 2 ∂d.measure
  let S : ℝ := ∑ i, ∑ j, ∫ x,
    scalarDirectional (F i) (scalarDirectional (F j) f) x ^ 2 ∂d.measure
  have hE : 0 ≤ Efirst := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))
  have hfirst (i : iota) :
      (∫ x, scalarDirectional (F i) f x ^ 2 ∂d.measure) ≤ Efirst := by
    exact Finset.single_le_sum (f := fun j : iota =>
      ∫ x, scalarDirectional (F j) f x ^ 2 ∂d.measure)
      (fun j _ => integral_nonneg (fun x => sq_nonneg (scalarDirectional (F j) f x)))
      (Finset.mem_univ i)
  have hsecond (i j : iota) :
      (∫ x, scalarDirectional (F i) (scalarDirectional (F j) f) x ^ 2 ∂d.measure) ≤ S := by
    calc
      _ ≤ ∑ k : iota, ∫ x,
          scalarDirectional (F i) (scalarDirectional (F k) f) x ^ 2 ∂d.measure :=
        Finset.single_le_sum (fun k _ => integral_nonneg (fun x =>
          sq_nonneg (scalarDirectional (F i) (scalarDirectional (F k) f) x)))
          (Finset.mem_univ j)
      _ ≤ S := Finset.single_le_sum (f := fun k : iota => ∑ l : iota, ∫ x,
          scalarDirectional (F k) (scalarDirectional (F l) f) x ^ 2 ∂d.measure)
        (fun k _ => Finset.sum_nonneg (fun l _ => integral_nonneg (fun x =>
          sq_nonneg (scalarDirectional (F k) (scalarDirectional (F l) f) x))))
        (Finset.mem_univ i)
  have hdf (i : iota) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (scalarDirectional (F i) f) :=
    contMDiff_directional hf (F i)
  have hddf (i j : iota) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (scalarDirectional (F i) (scalarDirectional (F j) f)) := contMDiff_directional (hdf j) (F i)
  have hInt (q : M → ℝ) (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q) :
      Integrable q d.measure :=
    hq.continuous.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  have hcross1 (i j : iota) :
      |∫ x, scalarDirectional (F i) (scalarDirectional (F j) f) x *
        scalarDirectional (smoothFieldBracket (F i) (F j)) f x ∂d.measure| ≤
        N * (epsilon * S + Q * Efirst) := by
    simp_rw [scalarDirectional_bracket_eq_sum g F hF, Finset.mul_sum]
    rw [integral_finsetSum (f := fun k x =>
      scalarDirectional (F i) (scalarDirectional (F j) f) x *
        (bracketCoefficient g F i j k x * scalarDirectional (F k) f x)) Finset.univ (fun k _ =>
      hInt _ ((hddf i j).mul ((bracketCoefficient_contMDiff g F i j k).mul (hdf k))))]
    calc
      _ ≤ ∑ k, |∫ x, scalarDirectional (F i) (scalarDirectional (F j) f) x *
          (bracketCoefficient g F i j k x * scalarDirectional (F k) f x) ∂d.measure| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : iota, (epsilon * S + Q * Efirst) := by
        apply Finset.sum_le_sum
        intro k _
        have h := d.abs_integral_mul_mul_le (bracketCoefficient_contMDiff g F i j k)
          (hdf k) (hddf i j) hB hepsilon (hb i j k)
        have h' := h.trans (add_le_add
          (mul_le_mul_of_nonneg_left (hsecond i j) hepsilon.le)
          (mul_le_mul_of_nonneg_left (hfirst k) hQ))
        simpa only [mul_comm, mul_left_comm, mul_assoc] using h'
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, N]
  have hcross2 (i j : iota) :
      |∫ x, scalarDirectional (F j) f x *
        scalarDirectional (smoothFieldBracket (F i) (F j)) (scalarDirectional (F i) f) x
        ∂d.measure| ≤ N * (epsilon * S + Q * Efirst) := by
    simp_rw [scalarDirectional_bracket_eq_sum g F hF, Finset.mul_sum]
    rw [integral_finsetSum (f := fun k x => scalarDirectional (F j) f x *
      (bracketCoefficient g F i j k x * scalarDirectional (F k) (scalarDirectional (F i) f) x))
      Finset.univ (fun k _ =>
      hInt _ ((hdf j).mul ((bracketCoefficient_contMDiff g F i j k).mul (hddf k i))))]
    calc
      _ ≤ ∑ k, |∫ x, scalarDirectional (F j) f x *
          (bracketCoefficient g F i j k x *
            scalarDirectional (F k) (scalarDirectional (F i) f) x) ∂d.measure| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : iota, (epsilon * S + Q * Efirst) := by
        apply Finset.sum_le_sum
        intro k _
        have h := d.abs_integral_mul_mul_le (bracketCoefficient_contMDiff g F i j k)
          (hdf j) (hddf k i) hB hepsilon (hb i j k)
        have h' := h.trans (add_le_add
          (mul_le_mul_of_nonneg_left (hsecond k i) hepsilon.le)
          (mul_le_mul_of_nonneg_left (hfirst j) hQ))
        simpa only [mul_comm, mul_left_comm, mul_assoc] using h'
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, N]
  have hdrift (i j : iota) :
      |∫ x, scalarDirectional (F j) f x *
        (scalarDirectional (F j) (d.fieldDivergence (F i)) x * scalarDirectional (F i) f x)
        ∂d.measure| ≤ (1 + D ^ 2) * Efirst := by
    have h := d.abs_integral_mul_mul_le
      (a := scalarDirectional (F j) (d.fieldDivergence (F i)))
      (contMDiff_directional (d.fieldDivergence_contMDiff (F i)) (F j))
      (hdf j) (hdf i) hD (by norm_num : (0 : ℝ) < 1) (hd i j)
    have h' := h.trans (add_le_add
      (mul_le_mul_of_nonneg_left (hfirst i) (by norm_num))
      (mul_le_mul_of_nonneg_left (hfirst j) (by positivity)))
    have h'' : (1 : ℝ) * Efirst + D ^ 2 / (4 * 1) * Efirst ≤ (1 + D ^ 2) * Efirst := by
      nlinarith [mul_nonneg (sq_nonneg D) hE]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h'.trans h''
  have hpair (i j : iota) :
      (∫ x, scalarDirectional (F i) (scalarDirectional (F j) f) x ^ 2 ∂d.measure) ≤
        (∫ x, d.fieldAdjoint (F i) (scalarDirectional (F i) f) x *
          d.fieldAdjoint (F j) (scalarDirectional (F j) f) x ∂d.measure) +
          2 * N * (epsilon * S + Q * Efirst) + (1 + D ^ 2) * Efirst := by
    rw [d.integral_secondDirectional_sq_eq (F i) (F j) hf]
    have herr :
        (∫ x, scalarDirectional (F j) f x *
          (-scalarDirectional (smoothFieldBracket (F i) (F j)) (scalarDirectional (F i) f) x +
            scalarDirectional (F j) (d.fieldDivergence (F i)) x * scalarDirectional (F i) f x)
          ∂d.measure) ≤ N * (epsilon * S + Q * Efirst) + (1 + D ^ 2) * Efirst := by
      simp_rw [mul_add, mul_neg]
      rw [integral_add
        (f := fun x => -(scalarDirectional (F j) f x *
          scalarDirectional (smoothFieldBracket (F i) (F j)) (scalarDirectional (F i) f) x))
        (g := fun x => scalarDirectional (F j) f x *
          (scalarDirectional (F j) (d.fieldDivergence (F i)) x * scalarDirectional (F i) f x))
        (hInt _ (((hdf j).mul (contMDiff_directional (hdf i)
          (smoothFieldBracket (F i) (F j)))).neg))
        (hInt _ ((hdf j).mul
          ((contMDiff_directional (d.fieldDivergence_contMDiff (F i)) (F j)).mul (hdf i)))),
        integral_neg]
      simpa only [mul_add] using
        add_le_add ((neg_le_abs _).trans (hcross2 i j))
          ((le_abs_self _).trans (hdrift i j))
    have h1 := (le_abs_self _).trans (hcross1 i j)
    linarith
  have hmain : (∑ i, ∑ j,
      ∫ x, d.fieldAdjoint (F i) (scalarDirectional (F i) f) x *
        d.fieldAdjoint (F j) (scalarDirectional (F j) f) x ∂d.measure) =
      ∫ x, (∑ i, d.fieldAdjoint (F i) (scalarDirectional (F i) f) x) ^ 2 ∂d.measure := by
    have hint (i j : iota) : Integrable
        (fun x => d.fieldAdjoint (F i) (scalarDirectional (F i) f) x *
          d.fieldAdjoint (F j) (scalarDirectional (F j) f) x) d.measure :=
      hInt _ ((d.fieldAdjoint_contMDiff (F i) (hdf i)).mul
        (d.fieldAdjoint_contMDiff (F j) (hdf j)))
    calc
      _ = ∑ i, ∫ x, ∑ j, d.fieldAdjoint (F i) (scalarDirectional (F i) f) x *
          d.fieldAdjoint (F j) (scalarDirectional (F j) f) x ∂d.measure := by
        apply Finset.sum_congr rfl
        intro i _
        exact (integral_finsetSum Finset.univ (fun j _ => hint i j)).symm
      _ = ∫ x, ∑ i, ∑ j, d.fieldAdjoint (F i) (scalarDirectional (F i) f) x *
          d.fieldAdjoint (F j) (scalarDirectional (F j) f) x ∂d.measure :=
        (integral_finsetSum Finset.univ (fun i _ =>
          integrable_finsetSum Finset.univ (fun j _ => hint i j))).symm
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by
          simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_comm)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpair i j))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hmain] at hsum
  have heps : 2 * N ^ 3 * epsilon ≤ 1 / 2 := by
    have hden : 0 < 4 * (N + 1) ^ 3 := by positivity
    have hcancel : (4 * (N + 1) ^ 3) * epsilon = 1 := by
      dsimp [epsilon]
      exact mul_one_div_cancel hden.ne'
    have hcube : N ^ 3 ≤ (N + 1) ^ 3 := pow_le_pow_left₀ hN (by linarith) 3
    have hscale := mul_le_mul_of_nonneg_right hcube hepsilon.le
    nlinarith only [hcancel, hscale]
  have habsorb := mul_le_mul_of_nonneg_right heps hS
  change S ≤ _
  dsimp only [C]
  dsimp only [S, N, Efirst] at hsum habsorb ⊢
  nlinarith only [hsum, habsorb]

theorem directional_energy_le_graph {iota : Type*} [Fintype iota]
    (F : iota → SmoothField (n := n) (M := M)) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    (∑ i, ∫ x, scalarDirectional (F i) f x ^ 2 ∂d.measure) ≤
      (∫ x, f x ^ 2 ∂d.measure) +
        ∫ x, (∑ i, d.fieldAdjoint (F i) (scalarDirectional (F i) f) x) ^ 2
          ∂d.measure := by
  classical
  let L : M → ℝ := fun x => ∑ i,
    d.fieldAdjoint (F i) (scalarDirectional (F i) f) x
  have hdf (i : iota) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (scalarDirectional (F i) f) :=
    contMDiff_directional hf (F i)
  have hA (i : iota) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (d.fieldAdjoint (F i) (scalarDirectional (F i) f)) := d.fieldAdjoint_contMDiff (F i) (hdf i)
  have hL : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ L := by
    apply contMDiff_finsetSum
    intro i _
    exact hA i
  have hInt (q : M → ℝ) (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q) :
      Integrable q d.measure :=
    hq.continuous.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  calc
    _ = ∑ i, ∫ x, f x * d.fieldAdjoint (F i) (scalarDirectional (F i) f) x
        ∂d.measure := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [pow_two] using d.integral_directional_eq_adjoint (F i) hf (hdf i)
    _ = ∫ x, f x * L x ∂d.measure := by
      rw [← integral_finsetSum (f := fun i x => f x *
        d.fieldAdjoint (F i) (scalarDirectional (F i) f) x)
          Finset.univ (fun i _ => hInt _ (hf.mul (hA i)))]
      simp only [L, Finset.mul_sum]
    _ ≤ ∫ x, f x ^ 2 + L x ^ 2 ∂d.measure :=
      integral_mono (hInt _ (hf.mul hL)) (hInt _ ((hf.pow 2).add (hL.pow 2)))
        (fun x => by nlinarith [sq_nonneg (f x - L x), sq_nonneg (f x + L x)])
    _ = _ := integral_add (hInt _ (hf.pow 2)) (hInt _ (hL.pow 2))

theorem exists_secondDirectional_graph_bound {iota : Type*} [Fintype iota]
    (g : RiemannianMetric n M) (F : iota → SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ k, g.inner x (F k x) v • F k x) = v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : M → ℝ), ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f →
      (∑ i, ∑ j, ∫ x, scalarDirectional (F i) (scalarDirectional (F j) f) x ^ 2
        ∂d.measure) ≤ C * ((∫ x, f x ^ 2 ∂d.measure) +
        ∫ x, (∑ i, d.fieldAdjoint (F i) (scalarDirectional (F i) f) x) ^ 2
          ∂d.measure) := by
  obtain ⟨C, hC, hbound⟩ := d.exists_secondDirectional_energy_bound g F hF
  refine ⟨2 + C, by positivity, ?_⟩
  intro f hf
  have hfirst := mul_le_mul_of_nonneg_left (d.directional_energy_le_graph F hf) hC
  have hzero : 0 ≤ ∫ x, f x ^ 2 ∂d.measure := integral_nonneg (fun _ => sq_nonneg _)
  have hsecond := hbound f hf
  nlinarith only [hfirst, hsecond, hzero]

end PoincareConjecture.ChartMeasureNative.FiniteChartData
