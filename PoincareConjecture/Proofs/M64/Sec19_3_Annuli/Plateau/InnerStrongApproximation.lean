import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerVectorMollification
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAverageDerivative
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff Convolution ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak M60

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

private theorem restrict_approximation
    {K : Set Plane} (hK : MeasurableSet K) {f : ℕ → Plane → E} {u U : Plane → E}
    (heq : EqOn U u K)
    (hlim : Tendsto (fun j => eLpNorm (f j - U) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (f j - u) 2 (volume.restrict K)) atTop (𝓝 0) := by
  have hb (j : ℕ) : eLpNorm (f j - u) 2 (volume.restrict K) ≤ eLpNorm (f j - U) 2 volume := by
    calc
      _ = eLpNorm (f j - U) 2 (volume.restrict K) := eLpNorm_congr_ae (by
        filter_upwards [ae_restrict_mem hK] with x hx
        simp only [Pi.sub_apply, heq hx])
      _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hb

private theorem integral_square_tendsto
    {K : Set Plane} {f : ℕ → Plane → E} {u : Plane → E}
    (hf : ∀ j, MemLp (f j) 2 (volume.restrict K)) (hu : MemLp u 2 (volume.restrict K))
    (hlim : Tendsto (fun j => eLpNorm (f j - u) 2 (volume.restrict K)) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x in K, ‖f j x - u x‖ ^ 2) atTop (𝓝 0) := by
  have hL := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hlim
  have hs := (hL.sub_const (hu.toLp u)).norm.pow 2
  have heq (j : ℕ) : ‖(hf j).toLp (f j) - hu.toLp u‖ ^ 2 =
      ∫ x in K, ‖f j x - u x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf j).toLp (f j)) (hu.toLp u),
      (hf j).coeFn_toLp, hu.coeFn_toLp] with x hx hxf hxu
    simp only [hx, Pi.sub_apply, hxf, hxu]
  simpa only [heq, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using hs

theorem m64WeakMap_inner_strong_approximation
    {O K : Set Plane} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (u : Plane → E) (V : Fin 2 → Plane → E)
    (hu : MemLp u 2 (volume.restrict O)) (hV : ∀ i, MemLp (V i) 2 (volume.restrict O))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun p => V i p b) (fun p => u p b) O) :
    ∃ f : ℕ → Plane → E, (∀ j, ContDiff ℝ ∞ (f j)) ∧
      Tendsto (fun j => ∫ p in K, ‖f j p - u p‖ ^ 2) atTop (𝓝 0) ∧
      ∀ i : Fin 2, Tendsto (fun j => ∫ p in K,
        ‖fderiv ℝ (f j) p (EuclideanSpace.single i 1) - V i p‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨delta, hdelta, hbuffer⟩ := hK.exists_cthickening_subset_open hO hKO
  let U := O.indicator u
  let W := fun i => O.indicator (V i)
  have hU : MemLp U 2 volume := (memLp_indicator_iff_restrict hO.measurableSet).mpr hu
  have hW (i : Fin 2) : MemLp (W i) 2 volume :=
    (memLp_indicator_iff_restrict hO.measurableSet).mpr (hV i)
  let r := fun j : ℕ => delta * (1 / 2 : ℝ) ^ (j + 1)
  have hr (j : ℕ) : 0 < r j := mul_pos hdelta (pow_pos (by norm_num) _)
  have hrb (j : ℕ) : r j ≤ delta := mul_le_of_le_one_right hdelta.le
    (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  have hrz : Tendsto r atTop (𝓝 0) := by
    simpa only [r, pow_succ, mul_zero, zero_mul] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2)).const_mul delta
  let f := fun j => mollifierEps (hr j) ⋆[lsmul ℝ ℝ, volume] U
  let D := fun j i => mollifierEps (hr j) ⋆[lsmul ℝ ℝ, volume] W i
  have hf (j : ℕ) : ContDiff ℝ ∞ (f j) :=
    (mollifierEps_compactSupport (hr j)).contDiff_convolution_left (lsmul ℝ ℝ)
      (mollifierEps_smooth (hr j)) (hU.locallyIntegrable (by norm_num))
  have hD (j : ℕ) (i : Fin 2) : ContDiff ℝ ∞ (D j i) :=
    (mollifierEps_compactSupport (hr j)).contDiff_convolution_left (lsmul ℝ ℝ)
      (mollifierEps_smooth (hr j)) ((hW i).locallyIntegrable (by norm_num))
  have hdf (j : ℕ) (i : Fin 2) (p : Plane) (hp : p ∈ K) :
      fderiv ℝ (f j) p (EuclideanSpace.single i 1) = D j i p := by
    apply suWeak_convolution_fderiv hO.measurableSet (hw i)
      (hU.locallyIntegrable (by norm_num)) ((hW i).locallyIntegrable (by norm_num))
      (mollifierEps_smooth (hr j)) (mollifierEps_compactSupport (hr j))
    rw [suMollifier_translated_tsupport]
    intro q hq
    exact hbuffer (Metric.mem_cthickening_of_dist_le q p delta K hp
      ((Metric.mem_closedBall.mp hq).trans (hrb j)))
  have hfl (j : ℕ) : MemLp (f j) 2 (volume.restrict K) := by
    apply (memLp_two_iff_integrable_sq_norm (hf j).continuous.aestronglyMeasurable).mpr
    exact ((hf j).continuous.norm.pow 2).continuousOn.integrableOn_compact hK
  have hDl (j : ℕ) (i : Fin 2) : MemLp (D j i) 2 (volume.restrict K) := by
    apply (memLp_two_iff_integrable_sq_norm (hD j i).continuous.aestronglyMeasurable).mpr
    exact ((hD j i).continuous.norm.pow 2).continuousOn.integrableOn_compact hK
  have hval : Tendsto (fun j => eLpNorm (f j - u) 2 (volume.restrict K)) atTop (𝓝 0) :=
    restrict_approximation hK.measurableSet (fun p hp => indicator_of_mem (hKO hp) u)
      (suVectorMollifier_Lp_tendsto (by norm_num) (by norm_num) hU hr hrz)
  have hcol (i : Fin 2) : Tendsto (fun j => eLpNorm (D j i - V i) 2 (volume.restrict K))
      atTop (𝓝 0) :=
    restrict_approximation hK.measurableSet (fun p hp => indicator_of_mem (hKO hp) (V i))
      (suVectorMollifier_Lp_tendsto (by norm_num) (by norm_num) (hW i) hr hrz)
  refine ⟨f, hf, integral_square_tendsto hfl
    (hu.mono_measure (Measure.restrict_mono hKO le_rfl)) hval, ?_⟩
  intro i
  have hlim := integral_square_tendsto (fun j => hDl j i)
    ((hV i).mono_measure (Measure.restrict_mono hKO le_rfl)) (hcol i)
  have heq (j : ℕ) : (∫ p in K,
      ‖fderiv ℝ (f j) p (EuclideanSpace.single i 1) - V i p‖ ^ 2) =
        ∫ p in K, ‖D j i p - V i p‖ ^ 2 := by
    apply setIntegral_congr_fun hK.measurableSet
    intro p hp
    exact congrArg (fun z : E => ‖z - V i p‖ ^ 2) (hdf j i p hp)
  simpa only [heq] using hlim

end PoincareConjecture
