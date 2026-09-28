import PoincareConjecture.Proofs.M03.Existence.EuclideanTranslationNative
import PoincareConjecture.Proofs.M03.Existence.CompactKernelNative
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace PoincareConjecture.CompactSupportLpNative

open EuclideanTranslationNative (ScalarL2)

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

def extension (K : Set E) (f : K →ᵇ ℝ) : E → ℝ :=
  Function.extend Subtype.val f (fun _ => 0)

theorem extension_of_mem (K : Set E) (f : K →ᵇ ℝ) {x : E} (hx : x ∈ K) :
    extension K f x = f ⟨x, hx⟩ :=
  Subtype.val_injective.extend_apply f (fun _ => 0) ⟨x, hx⟩

theorem extension_of_notMem (K : Set E) (f : K →ᵇ ℝ) {x : E} (hx : x ∉ K) :
    extension K f x = 0 := by
  apply Function.extend_apply'
  rintro ⟨y, hy⟩
  exact hx (hy ▸ y.property)

theorem measurable_extension {K : Set E} (hK : MeasurableSet K) (f : K →ᵇ ℝ) :
    Measurable (extension K f) :=
  (MeasurableEmbedding.subtype_coe hK).measurable_extend f.continuous.measurable measurable_const

theorem norm_extension_le_indicator (K : Set E) (f : K →ᵇ ℝ) (x : E) :
    ‖extension K f x‖ ≤ ‖K.indicator (fun _ => ‖f‖) x‖ := by
  by_cases hx : x ∈ K
  · rw [extension_of_mem K f hx, indicator_of_mem hx]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg f)] using
      f.norm_coe_le_norm ⟨x, hx⟩
  · rw [extension_of_notMem K f hx, indicator_of_notMem hx]

theorem memLp_extension {K : Set E} (hK : IsCompact K) (f : K →ᵇ ℝ) :
    MemLp (extension K f) 2 volume := by
  have hi := memLp_indicator_const (μ := (volume : Measure E)) 2
    hK.isClosed.measurableSet ‖f‖ (Or.inr hK.measure_ne_top)
  exact hi.of_le (measurable_extension hK.isClosed.measurableSet f).aestronglyMeasurable
    (Eventually.of_forall (norm_extension_le_indicator K f))

def extensionLp {K : Set E} (hK : IsCompact K) (f : K →ᵇ ℝ) : ScalarL2 n :=
  (memLp_extension hK f).toLp (extension K f)

theorem extensionLp_ae_eq {K : Set E} (hK : IsCompact K) (f : K →ᵇ ℝ) :
    extensionLp hK f =ᵐ[volume] extension K f :=
  (memLp_extension hK f).coeFn_toLp

theorem norm_extensionLp_le {K : Set E} (hK : IsCompact K) (f : K →ᵇ ℝ) :
    ‖extensionLp hK f‖ ≤ (volume.real K) ^ (1 / (2 : ℝ)) * ‖f‖ := by
  have hnorm : ‖extensionLp hK f‖ ≤
      ‖indicatorConstLp (μ := (volume : Measure E)) 2 hK.isClosed.measurableSet
        hK.measure_ne_top ‖f‖‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [extensionLp_ae_eq hK f,
      indicatorConstLp_coeFn (μ := (volume : Measure E)) (p := 2)
        (hs := hK.isClosed.measurableSet) (hμs := hK.measure_ne_top) (c := ‖f‖)]
        with x hfx hix
    rw [hfx, hix]
    exact norm_extension_le_indicator K f x
  calc
    _ ≤ _ := hnorm
    _ = _ := by
      rw [norm_indicatorConstLp (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ∞)]
      simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg f), ENNReal.toReal_ofNat]
      ring

theorem extension_add (K : Set E) (f g : K →ᵇ ℝ) :
    extension K (f + g) = extension K f + extension K g := by
  funext x
  by_cases hx : x ∈ K
  · simp only [Pi.add_apply, extension_of_mem K _ hx, BoundedContinuousFunction.add_apply]
  · simp only [Pi.add_apply, extension_of_notMem K _ hx, add_zero]

theorem extension_smul (K : Set E) (a : ℝ) (f : K →ᵇ ℝ) :
    extension K (a • f) = a • extension K f := by
  funext x
  by_cases hx : x ∈ K
  · simp only [Pi.smul_apply, extension_of_mem K _ hx, BoundedContinuousFunction.smul_apply]
  · simp only [Pi.smul_apply, extension_of_notMem K _ hx, smul_zero]

theorem extensionLp_add {K : Set E} (hK : IsCompact K) (f g : K →ᵇ ℝ) :
    extensionLp hK (f + g) = extensionLp hK f + extensionLp hK g := by
  unfold extensionLp
  rw [← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact Eventually.of_forall (fun x => congrFun (extension_add K f g) x)

theorem extensionLp_smul {K : Set E} (hK : IsCompact K) (a : ℝ) (f : K →ᵇ ℝ) :
    extensionLp hK (a • f) = a • extensionLp hK f := by
  unfold extensionLp
  rw [← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  exact Eventually.of_forall (fun x => congrFun (extension_smul K a f) x)

def extensionLinearMap {K : Set E} (hK : IsCompact K) : (K →ᵇ ℝ) →ₗ[ℝ] ScalarL2 n where
  toFun := extensionLp hK
  map_add' := extensionLp_add hK
  map_smul' := extensionLp_smul hK

def extensionOperator {K : Set E} (hK : IsCompact K) : (K →ᵇ ℝ) →L[ℝ] ScalarL2 n :=
  (extensionLinearMap hK).mkContinuous ((volume.real K) ^ (1 / (2 : ℝ)))
    (fun f => by
      change ‖extensionLp hK f‖ ≤ (volume.real K) ^ (1 / (2 : ℝ)) * ‖f‖
      exact norm_extensionLp_le hK f)

@[simp] theorem extensionOperator_apply {K : Set E} (hK : IsCompact K) (f : K →ᵇ ℝ) :
    extensionOperator hK f = extensionLp hK f := rfl

theorem norm_extensionOperator_le {K : Set E} (hK : IsCompact K) :
    ‖extensionOperator hK‖ ≤ (volume.real K) ^ (1 / (2 : ℝ)) :=
  (extensionLinearMap hK).mkContinuous_norm_le (by positivity) _

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem isCompactOperator_extendedKernel {K : Set E} (hK : IsCompact K)
    [CompactSpace K] (k : C(K, H)) :
    IsCompactOperator ((extensionOperator hK).comp (CompactKernelNative.kernelOperator k)) :=
  (CompactKernelNative.isCompactOperator_kernelOperator k).clm_comp (extensionOperator hK)

end PoincareConjecture.CompactSupportLpNative
