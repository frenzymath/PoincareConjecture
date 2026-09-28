import PoincareConjecture.Proofs.M03.Existence.ChartMeasureComparisonNative
import Mathlib.MeasureTheory.Function.LpSpace.Basic










set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

universe u v w

namespace PoincareConjecture.ChartLpNative

section Pullback

variable {X : Type u} {Y : Type v} {E : Type w}
  [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ν : Measure X} (b : X → Y) (hb : AEMeasurable b ν)

def mapPullbackL2Fun (f : Lp E 2 (ν.map b)) : Lp E 2 ν :=
  ((Lp.memLp f).comp_of_map hb).toLp (f ∘ b)

theorem mapPullbackL2Fun_coe (f : Lp E 2 (ν.map b)) :
    mapPullbackL2Fun b hb f =ᵐ[ν] f ∘ b :=
  MemLp.coeFn_toLp _


def mapPullbackL2 : Lp E 2 (ν.map b) →ₗᵢ[ℝ] Lp E 2 ν where
  toFun := mapPullbackL2Fun b hb
  map_add' f g := by
    apply Lp.ext
    filter_upwards [mapPullbackL2Fun_coe b hb (f + g),
      mapPullbackL2Fun_coe b hb f, mapPullbackL2Fun_coe b hb g,
      Lp.coeFn_add (mapPullbackL2Fun b hb f) (mapPullbackL2Fun b hb g),
      ae_of_ae_map hb (Lp.coeFn_add f g)] with x hsum hf hg hadd hmap
    change mapPullbackL2Fun b hb (f + g) x =
      (mapPullbackL2Fun b hb f + mapPullbackL2Fun b hb g) x
    rw [hsum, hadd, Pi.add_apply, hf, hg]
    exact hmap
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [mapPullbackL2Fun_coe b hb (a • f),
      mapPullbackL2Fun_coe b hb f,
      Lp.coeFn_smul a (mapPullbackL2Fun b hb f),
      ae_of_ae_map hb (Lp.coeFn_smul a f)] with x hsmul hf ha hmap
    change mapPullbackL2Fun b hb (a • f) x = (a • mapPullbackL2Fun b hb f) x
    rw [hsmul, ha, Pi.smul_apply, hf]
    exact hmap
  norm_map' f := by
    change ‖((Lp.memLp f).comp_of_map hb).toLp (f ∘ b)‖ = ‖f‖
    rw [Lp.norm_toLp, ← eLpNorm_map_measure (Lp.memLp f).aestronglyMeasurable hb,
      Lp.norm_def]

theorem mapPullbackL2_coe (f : Lp E 2 (ν.map b)) :
    mapPullbackL2 b hb f =ᵐ[ν] f ∘ b :=
  mapPullbackL2Fun_coe b hb f

variable {μ : Measure Y} {C : ℝ≥0∞} (hC : C ≠ ∞) (hdom : ν.map b ≤ C • μ)


def dominatedPullbackL2 : Lp E 2 μ →L[ℝ] Lp E 2 ν :=
  (mapPullbackL2 b hb).toContinuousLinearMap.comp
    (Lp.LpToLpOfMeasureLeSMul hC hdom)

theorem dominatedPullbackL2_coe (f : Lp E 2 μ) :
    dominatedPullbackL2 b hb hC hdom f =ᵐ[ν] f ∘ b := by
  apply (mapPullbackL2_coe b hb (Lp.LpToLpOfMeasureLeSMul hC hdom f)).trans
  exact ae_of_ae_map hb (Lp.coeFn_LpToLpOfMeasureLeSMul hC hdom f)

theorem dominatedPullbackL2_toLp_coe {f : Y → E} (hf : MemLp f 2 μ) :
    dominatedPullbackL2 b hb hC hdom (hf.toLp f) =ᵐ[ν] f ∘ b := by
  apply (dominatedPullbackL2_coe b hb hC hdom (hf.toLp f)).trans
  exact ae_of_ae_map hb (ae_mono hdom (Measure.ae_smul_measure hf.coeFn_toLp C))

theorem norm_dominatedPullbackL2_apply_le (f : Lp E 2 μ) :
    ‖dominatedPullbackL2 b hb hC hdom f‖ ≤ C.toReal ^ (1 / (2 : ℝ≥0∞)).toReal * ‖f‖ := by
  change ‖mapPullbackL2 b hb (Lp.LpToLpOfMeasureLeSMul hC hdom f)‖ ≤ _
  rw [(mapPullbackL2 b hb).norm_map]
  exact ((Lp.LpToLpOfMeasureLeSMul hC hdom).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right
      (Lp.norm_LpToLpOfMeasureLeSMul_le (E := E) (p := 2) hC hdom) (norm_nonneg _))

theorem norm_dominatedPullbackL2_le :
    ‖(dominatedPullbackL2 b hb hC hdom : Lp E 2 μ →L[ℝ] Lp E 2 ν)‖ ≤
      C.toReal ^ (1 / (2 : ℝ≥0∞)).toReal := by
  apply (dominatedPullbackL2 (E := E) b hb hC hdom).opNorm_le_bound
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  intro f
  exact norm_dominatedPullbackL2_apply_le b hb hC hdom f

end Pullback

section Chart

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]

local notation "ModelE" => EuclideanSpace ℝ (Fin n)

theorem le_inv_smul_of_smul_le {ν μ : Measure M} {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hctop : c ≠ ∞) (h : c • ν ≤ μ) : ν ≤ c⁻¹ • μ := by
  have hscaled := smul_le_smul_left c⁻¹ h
  simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul] using hscaled

theorem coordinateMeasure_le (e : OpenPartialHomeomorph M ModelE) (φ : C(M, ℝ))
    {A : Set ModelE} (hA : MeasurableSet A) (hAt : A ⊆ e.target) {c : ℝ}
    (hc : 0 < c) (hbound : ∀ y ∈ A, c ≤ φ (e.symm y)) :
    (volume.restrict A).map e.symm ≤ (ENNReal.ofReal c)⁻¹ •
      ChartMeasureNative.weightedChartMeasure e φ := by
  apply le_inv_smul_of_smul_le (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top
  exact ChartMeasureNative.weightedChartMeasure_lower e φ hA hAt
    (fun y hy => ENNReal.ofReal_le_ofReal (hbound y hy))

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]


def chartPullbackL2 (e : OpenPartialHomeomorph M ModelE) {A : Set ModelE}
    (hA : MeasurableSet A) (hAt : A ⊆ e.target) {μ : Measure M} {c : ℝ}
    (hc : 0 < c)
    (hdom : ENNReal.ofReal c • (volume.restrict A).map e.symm ≤ μ) :
    Lp E 2 μ →L[ℝ] Lp E 2 (volume.restrict A) :=
  dominatedPullbackL2 e.symm ((e.symm.continuousOn.mono hAt).aemeasurable hA)
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hc)))
    (le_inv_smul_of_smul_le (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top hdom)

theorem chartPullbackL2_coe (e : OpenPartialHomeomorph M ModelE) {A : Set ModelE}
    (hA : MeasurableSet A) (hAt : A ⊆ e.target) {μ : Measure M} {c : ℝ}
    (hc : 0 < c)
    (hdom : ENNReal.ofReal c • (volume.restrict A).map e.symm ≤ μ) (f : Lp E 2 μ) :
    chartPullbackL2 e hA hAt hc hdom f =ᵐ[volume.restrict A] f ∘ e.symm :=
  dominatedPullbackL2_coe _ _ _ _ f

theorem chartPullbackL2_toLp_coe (e : OpenPartialHomeomorph M ModelE) {A : Set ModelE}
    (hA : MeasurableSet A) (hAt : A ⊆ e.target) {μ : Measure M} {c : ℝ}
    (hc : 0 < c)
    (hdom : ENNReal.ofReal c • (volume.restrict A).map e.symm ≤ μ)
    {f : M → E} (hf : MemLp f 2 μ) :
    chartPullbackL2 e hA hAt hc hdom (hf.toLp f) =ᵐ[volume.restrict A] f ∘ e.symm :=
  dominatedPullbackL2_toLp_coe _ _ _ _ hf

theorem chartPullbackL2_tendsto (e : OpenPartialHomeomorph M ModelE) {A : Set ModelE}
    (hA : MeasurableSet A) (hAt : A ⊆ e.target) {μ : Measure M} {c : ℝ}
    (hc : 0 < c)
    (hdom : ENNReal.ofReal c • (volume.restrict A).map e.symm ≤ μ)
    {f : ℕ → Lp E 2 μ} {g : Lp E 2 μ} (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun j => chartPullbackL2 e hA hAt hc hdom (f j)) atTop
      (𝓝 (chartPullbackL2 e hA hAt hc hdom g)) := by
  simpa only [Function.comp_def] using
    ((chartPullbackL2 e hA hAt hc hdom).continuous.tendsto _).comp hf

end Chart

end PoincareConjecture.ChartLpNative
