import PoincareConjecture.Proofs.M03.Existence.NativeChartScalarLocalization
import PoincareConjecture.Proofs.M03.Existence.NativeChartLocalizationData
import PoincareConjecture.Proofs.M03.Existence.FiniteLocalizationCompactnessNative









set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal Manifold ContDiff SchwartzMap

universe u

namespace PoincareConjecture.ChartMeasureNative.FiniteChartLocalizationData

open ChartLpNative ChartPushforwardLpNative EuclideanDerivativeNative
  NativeChartScalarLocalization EuclideanTranslationNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]

local notation "E" => EuclideanSpace ℝ (Fin n)

variable {d : FiniteChartData (n := n) (M := M)} (L : FiniteChartLocalizationData d)

theorem weight_compactSupport (a : L.patches) : IsCompact (tsupport (L.weight a)) :=
  (isClosed_tsupport (L.weight a)).isCompact

theorem weight_zero_off_support (a : L.patches) :
    ∀ x ∉ tsupport (L.weight a), L.weight a x = 0 :=
  fun _ hx => image_eq_zero_of_notMem_tsupport hx

def scalarCutoff (a : L.patches) : 𝓢(E, ℝ) :=
  (chartScalar_compactSupport a.val.1.val (L.weight_compactSupport a)
    (L.weight_support_source a) (L.weight_zero_off_support a)).toSchwartzMap
      (contDiff_chartScalar a.val.1.val (L.weight_smooth a) (L.weight_compactSupport a)
        (L.weight_support_source a) (L.weight_zero_off_support a))

@[simp] theorem scalarCutoff_apply (a : L.patches) (z : E) :
    L.scalarCutoff a z = chartScalar a.val.1.val (L.weight a) z := rfl

theorem scalarCutoff_tsupport_subset (a : L.patches) :
    tsupport (L.scalarCutoff a) ⊆ L.region a :=
  (tsupport_chartScalar_subset a.val.1.val (L.weight_compactSupport a)
    (L.weight_support_source a) (L.weight_zero_off_support a)).trans
      (L.supportImage_subset_region a)


def localizationL2 (a : L.patches) : Lp ℝ 2 d.measure →L[ℝ] ScalarL2 n :=
  (cutoffL2 (L.scalarCutoff a) (L.region_open a).measurableSet).comp
    (chartPullbackL2 (L.chart a) (L.region_open a).measurableSet (L.region_subset_target a)
      (L.lowerConstant_pos a) (L.region_measure_lower a))

theorem localizationL2_coe (a : L.patches) (F : Lp ℝ 2 d.measure) :
    L.localizationL2 a F =ᵐ[volume] fun z => L.scalarCutoff a z * F ((L.chart a).symm z) := by
  have hp := chartPullbackL2_coe (L.chart a) (L.region_open a).measurableSet
    (L.region_subset_target a) (L.lowerConstant_pos a) (L.region_measure_lower a) F
  filter_upwards [cutoffL2_coe (L.scalarCutoff a) (L.region_open a).measurableSet
    (L.scalarCutoff_tsupport_subset a)
    (chartPullbackL2 (L.chart a) (L.region_open a).measurableSet (L.region_subset_target a)
      (L.lowerConstant_pos a) (L.region_measure_lower a) F),
    (ae_restrict_iff' (L.region_open a).measurableSet).mp hp] with z hcut hpz
  apply hcut.trans
  by_cases hz : z ∈ L.region a
  · exact congrArg (fun q : ℝ => L.scalarCutoff a z * q) (hpz hz)
  · have hzero : L.scalarCutoff a z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz (L.scalarCutoff_tsupport_subset a h))
    simp only [hzero, zero_mul]

theorem localizationL2_toLp_coe (a : L.patches) {f : M → ℝ} (hf : MemLp f 2 d.measure) :
    L.localizationL2 a (hf.toLp f) =ᵐ[volume]
      fun z => L.scalarCutoff a z * f ((L.chart a).symm z) := by
  have hp := chartPullbackL2_toLp_coe (L.chart a) (L.region_open a).measurableSet
    (L.region_subset_target a) (L.lowerConstant_pos a) (L.region_measure_lower a) hf
  filter_upwards [cutoffL2_coe (L.scalarCutoff a) (L.region_open a).measurableSet
    (L.scalarCutoff_tsupport_subset a)
    (chartPullbackL2 (L.chart a) (L.region_open a).measurableSet (L.region_subset_target a)
      (L.lowerConstant_pos a) (L.region_measure_lower a) (hf.toLp f)),
    (ae_restrict_iff' (L.region_open a).measurableSet).mp hp] with z hcut hpz
  apply hcut.trans
  by_cases hz : z ∈ L.region a
  · exact congrArg (fun q : ℝ => L.scalarCutoff a z * q) (hpz hz)
  · have hzero : L.scalarCutoff a z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz (L.scalarCutoff_tsupport_subset a h))
    simp only [hzero, zero_mul]

theorem scalarCutoff_mul_eq_chartScalar (a : L.patches) (f : M → ℝ) (z : E) :
    L.scalarCutoff a z * f ((L.chart a).symm z) =
      chartScalar a.val.1.val (fun x => L.weight a x * f x) z := by
  rw [scalarCutoff_apply]
  by_cases hz : z ∈ (L.chart a).target
  · rw [chartScalar_of_mem a.val.1.val (L.weight a) hz,
      chartScalar_of_mem a.val.1.val (fun x => L.weight a x * f x) hz]
    rfl
  · rw [chartScalar_of_notMem a.val.1.val (L.weight a) hz,
      chartScalar_of_notMem a.val.1.val (fun x => L.weight a x * f x) hz, zero_mul]

theorem localizedProduct_zero (a : L.patches) (f : M → ℝ) :
    ∀ x ∉ tsupport (L.weight a), L.weight a x * f x = 0 := by
  intro x hx
  rw [L.weight_zero_off_support a x hx, zero_mul]

theorem localizedProduct_memLp (a : L.patches) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    MemLp (chartScalar (n := n) a.val.1.val (fun x => L.weight a x * f x)) 2 volume :=
  chartScalar_memLp a.val.1.val ((L.weight_smooth a).mul hf) (L.weight_compactSupport a)
    (L.weight_support_source a) (L.localizedProduct_zero a f)

theorem localizationL2_toLp_eq (a : L.patches) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hfμ : MemLp f 2 d.measure) :
    L.localizationL2 a (hfμ.toLp f) =
      (L.localizedProduct_memLp a hf).toLp (chartScalar a.val.1.val (fun x => L.weight a x * f x)) := by
  apply Lp.ext
  apply (L.localizationL2_toLp_coe a hfμ).trans
  apply EventuallyEq.trans _ (L.localizedProduct_memLp a hf).coeFn_toLp.symm
  exact Eventually.of_forall (L.scalarCutoff_mul_eq_chartScalar a f)

def reconstructionConstant (a : L.patches) : ℝ≥0∞ :=
  (d.exists_measure_restrict_le_chart a.val.1.val (L.weight_compactSupport a)
    (L.weight_support_source a)).choose

theorem reconstructionConstant_ne_top (a : L.patches) : L.reconstructionConstant a ≠ ⊤ :=
  (d.exists_measure_restrict_le_chart a.val.1.val (L.weight_compactSupport a)
    (L.weight_support_source a)).choose_spec.1

theorem reconstructionMeasureBound (a : L.patches) :
    d.measure.restrict (tsupport (L.weight a)) ≤
      L.reconstructionConstant a • coordinatePushforward (L.chart a) (tsupport (L.weight a)) :=
  (d.exists_measure_restrict_le_chart a.val.1.val (L.weight_compactSupport a)
    (L.weight_support_source a)).choose_spec.2


def reconstructionL2 (a : L.patches) : ScalarL2 n →L[ℝ] Lp ℝ 2 d.measure :=
  chartExtensionL2 (L.chart a) (isClosed_tsupport (L.weight a)).measurableSet
    (L.weight_support_source a) (L.reconstructionConstant_ne_top a) (L.reconstructionMeasureBound a)

theorem globalProduct_memLp (a : L.patches) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) : MemLp (fun x => L.weight a x * f x) 2 d.measure :=
  ((L.weight a).continuous.mul hf.continuous).memLp_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

theorem reconstruction_localization_toLp_eq (a : L.patches) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hfμ : MemLp f 2 d.measure) :
    L.reconstructionL2 a (L.localizationL2 a (hfμ.toLp f)) =
      (L.globalProduct_memLp a hf).toLp (fun x => L.weight a x * f x) := by
  rw [L.localizationL2_toLp_eq a hf hfμ]
  exact chartExtension_chartScalar a.val.1.val ((L.weight_smooth a).mul hf)
    (L.weight_compactSupport a) (L.weight_support_source a) (L.localizedProduct_zero a f)
    (L.globalProduct_memLp a hf) (L.reconstructionConstant_ne_top a) (L.reconstructionMeasureBound a)


theorem sum_reconstruction_localization (f : M → ℝ)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hfμ : MemLp f 2 d.measure) :
    (∑ a : L.patches, L.reconstructionL2 a (L.localizationL2 a (hfμ.toLp f))) = hfμ.toLp f := by
  classical
  simp_rw [L.reconstruction_localization_toLp_eq _ hf hfμ]
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun a : L.patches => (L.globalProduct_memLp a hf).toLp (fun x => L.weight a x * f x)),
    ae_all_iff.mpr (fun a : L.patches => (L.globalProduct_memLp a hf).coeFn_toLp),
    hfμ.coeFn_toLp] with x hsum hproduct hfx
  rw [hsum, hfx]
  calc
    _ = ∑ a : L.patches, L.weight a x * f x := Finset.sum_congr rfl (fun a _ => hproduct a)
    _ = (∑ a : L.patches, L.weight a x) * f x := (Finset.sum_mul _ _ _).symm
    _ = f x := by rw [L.weight_sum, one_mul]

end PoincareConjecture.ChartMeasureNative.FiniteChartLocalizationData
