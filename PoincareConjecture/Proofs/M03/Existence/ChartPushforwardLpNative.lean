import PoincareConjecture.Proofs.M03.Existence.ChartMeasureUpperNative
import PoincareConjecture.Proofs.M03.Existence.ChartLpNative
import PoincareConjecture.Proofs.M03.Existence.EuclideanCutoffNative









set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

universe u v

namespace PoincareConjecture.ChartPushforwardLpNative

open ChartMeasureNative ChartLpNative EuclideanDerivativeNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]

local notation "E" => EuclideanSpace ℝ (Fin n)


def measurableChart (e : OpenPartialHomeomorph M E) : M → E := e.source.indicator e

theorem measurable_measurableChart (e : OpenPartialHomeomorph M E) :
    Measurable (measurableChart e) := by
  classical
  change Measurable (e.source.piecewise e (fun _ => 0))
  exact e.continuousOn.measurable_piecewise continuous_const.continuousOn e.open_source.measurableSet

theorem measurableChart_of_mem (e : OpenPartialHomeomorph M E) {x : M} (hx : x ∈ e.source) :
    measurableChart e x = e x := indicator_of_mem hx _

theorem map_coordinatePushforward (e : OpenPartialHomeomorph M E)
    {K : Set M} (hK : MeasurableSet K) (hKs : K ⊆ e.source) :
    (coordinatePushforward e K).map (measurableChart e) = volume.restrict (e '' K) := by
  unfold coordinatePushforward
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_measurableChart e).aemeasurable
    (coordinateInverse_aemeasurable e hK hKs)]
  calc
    _ = (volume.restrict (e '' K)).map id := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (measurableSet_chart_image e hK hKs)] with y hy
      obtain ⟨x, hxK, rfl⟩ := hy
      change measurableChart e (e.symm (e x)) = e x
      rw [e.left_inv (hKs hxK), measurableChart_of_mem e (hKs hxK)]
    _ = _ := Measure.map_id

theorem map_restrict_le_smul_volume (e : OpenPartialHomeomorph M E)
    {K : Set M} (hK : MeasurableSet K) (hKs : K ⊆ e.source)
    {μ : Measure M} {C : ℝ≥0∞} (hdom : μ.restrict K ≤ C • coordinatePushforward e K) :
    (μ.restrict K).map (measurableChart e) ≤ C • (volume : Measure E) := by
  have hm := Measure.map_mono_of_aemeasurable hdom (measurable_measurableChart e).aemeasurable
  rw [Measure.map_smul, map_coordinatePushforward e hK hKs] at hm
  exact hm.trans (smul_le_smul_left C Measure.restrict_le_self)

variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]


def chartExtensionL2 (e : OpenPartialHomeomorph M E)
    {K : Set M} (hK : MeasurableSet K) (hKs : K ⊆ e.source)
    {μ : Measure M} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hdom : μ.restrict K ≤ C • coordinatePushforward e K) :
    Lp V 2 (volume : Measure E) →L[ℝ] Lp V 2 μ :=
  (zeroExtendL2 hK).toContinuousLinearMap.comp
    (dominatedPullbackL2 (measurableChart e) (measurable_measurableChart e).aemeasurable hC
      (map_restrict_le_smul_volume e hK hKs hdom))

theorem chartExtensionL2_coe (e : OpenPartialHomeomorph M E)
    {K : Set M} (hK : MeasurableSet K) (hKs : K ⊆ e.source)
    {μ : Measure M} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hdom : μ.restrict K ≤ C • coordinatePushforward e K)
    (F : Lp V 2 (volume : Measure E)) :
    chartExtensionL2 e hK hKs hC hdom F =ᵐ[μ] K.indicator (fun x => F (e x)) := by
  have hp := dominatedPullbackL2_coe (measurableChart e)
    (measurable_measurableChart e).aemeasurable hC
    (map_restrict_le_smul_volume e hK hKs hdom) F
  apply (zeroExtendL2_coe hK _).trans
  apply ((ae_eq_restrict_iff_indicator_ae_eq hK).mp hp).trans
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · simp only [indicator_of_mem hx, Function.comp_apply, measurableChart_of_mem e (hKs hx)]
  · simp only [indicator_of_notMem hx]

theorem chartExtensionL2_toLp_coe (e : OpenPartialHomeomorph M E)
    {K : Set M} (hK : MeasurableSet K) (hKs : K ⊆ e.source)
    {μ : Measure M} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hdom : μ.restrict K ≤ C • coordinatePushforward e K)
    {f : E → V} (hf : MemLp f 2 volume) :
    chartExtensionL2 e hK hKs hC hdom (hf.toLp f) =ᵐ[μ] K.indicator (fun x => f (e x)) := by
  have hp := dominatedPullbackL2_toLp_coe (measurableChart e)
    (measurable_measurableChart e).aemeasurable hC
    (map_restrict_le_smul_volume e hK hKs hdom) hf
  apply (zeroExtendL2_coe hK _).trans
  apply ((ae_eq_restrict_iff_indicator_ae_eq hK).mp hp).trans
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · simp only [indicator_of_mem hx, Function.comp_apply, measurableChart_of_mem e (hKs hx)]
  · simp only [indicator_of_notMem hx]

theorem norm_chartExtensionL2_apply_le (e : OpenPartialHomeomorph M E)
    {K : Set M} (hK : MeasurableSet K) (hKs : K ⊆ e.source)
    {μ : Measure M} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hdom : μ.restrict K ≤ C • coordinatePushforward e K)
    (F : Lp V 2 (volume : Measure E)) :
    ‖chartExtensionL2 e hK hKs hC hdom F‖ ≤ C.toReal ^ (1 / (2 : ℝ≥0∞)).toReal * ‖F‖ := by
  change ‖zeroExtendL2 hK (dominatedPullbackL2 (measurableChart e)
    (measurable_measurableChart e).aemeasurable hC
    (map_restrict_le_smul_volume e hK hKs hdom) F)‖ ≤ _
  rw [(zeroExtendL2 hK).norm_map]
  exact norm_dominatedPullbackL2_apply_le _ _ _ _ F

end PoincareConjecture.ChartPushforwardLpNative
