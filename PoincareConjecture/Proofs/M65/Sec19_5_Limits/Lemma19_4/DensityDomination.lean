import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.DensityVariation
import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.FlowMetricScaling
import PoincareConjecture.Proofs.M65.Mathlib.ExpIncrement
import PoincareConjecture.Proofs.M65.Mathlib.AreaDensityMeasurable
import Mathlib.Analysis.Calculus.Deriv.Slope










set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Icc a b)) {K0 K1 K2 : ℝ}



theorem m65AreaDensity_time_lipschitz_bound
    (bounds : CurveEvolutionAmbientBounds F K0 K1 K2) (hK2 : 0 ≤ K2)
    (f : LoopPlane → M) (z : LoopPlane) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    |m60AreaDensity (F.metric t) f z - m60AreaDensity (F.metric s) f z| ≤
      ((2 * K2) * (Real.exp ((2 * K2) * (b - a))) ^ 2 *
        m60AreaDensity (F.metric a) f z) * |t - s| := by
  let c := 2 * K2
  let E := Real.exp (c * (b - a))
  let j := fun r => m60AreaDensity (F.metric r) f z
  have hc : 0 ≤ c := mul_nonneg (by norm_num) hK2
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hj (r : ℝ) : 0 ≤ j r := Real.sqrt_nonneg _
  have ha : a ∈ Icc a b := ⟨le_rfl, hs.1.trans hs.2⟩
  have htime {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) :
      |v - u| ≤ b - a := abs_le.mpr ⟨by linarith [hu.2, hv.1],
        by linarith [hu.1, hv.2]⟩
  have huniform {r : ℝ} (hr : r ∈ Icc a b) : j r ≤ E * j a := by
    exact (m65FlowAreaDensity_scaling F bounds ha hr f z).trans
      (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (htime ha hr) hc)) (hj a))
  have hforward {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) :
      j v - j u ≤ (c * E ^ 2 * j a) * |v - u| := by
    have hcmp := m65FlowAreaDensity_scaling F bounds hu hv f z
    change j v ≤ Real.exp (c * |v - u|) * j u at hcmp
    have hx : 0 ≤ c * |v - u| := mul_nonneg hc (abs_nonneg _)
    have hincr := Real.exp_sub_one_le_mul_exp hx
      (mul_le_mul_of_nonneg_left (htime hu hv) hc)
    change Real.exp (c * |v - u|) - 1 ≤ c * |v - u| * E at hincr
    calc
      j v - j u ≤ (Real.exp (c * |v - u|) - 1) * j u := by linarith
      _ ≤ (c * |v - u| * E) * j u :=
        mul_le_mul_of_nonneg_right hincr (hj u)
      _ ≤ (c * |v - u| * E) * (E * j a) :=
        mul_le_mul_of_nonneg_left (huniform hu) (mul_nonneg hx hE)
      _ = (c * E ^ 2 * j a) * |v - u| := by ring
  apply abs_le.mpr
  refine ⟨?_, hforward hs ht⟩
  have hreverse := hforward ht hs
  rw [abs_sub_comm] at hreverse
  change -((c * E ^ 2 * j a) * |t - s|) ≤ j t - j s
  linarith




theorem m65PlaneRicciTraceDensity_aestronglyMeasurable
    {f : LoopPlane → M} {domain : Set LoopPlane}
    (hcompact : IsCompact domain) (hf : ContinuousOn f domain)
    (hdf : ∀ᵐ z ∂volume, z ∈ domain → MDifferentiableAt (𝓡 2) (𝓡 n) f z)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    AEStronglyMeasurable (m65PlaneRicciTraceDensity (F.connection t) f)
      (volume.restrict domain) := by
  have hmeas (s : ℝ) :=
    m65AreaDensity_aestronglyMeasurable (F.metric s) hcompact hf hdf
  have hquot (h : ℝ) : AEStronglyMeasurable
      (fun z => h⁻¹ • (m60AreaDensity (F.metric (t + h)) f z -
        m60AreaDensity (F.metric t) f z)) (volume.restrict domain) :=
    ((hmeas (t + h)).sub (hmeas t)).const_smul h⁻¹
  have hlimit : AEStronglyMeasurable
      (fun z => -m65PlaneRicciTraceDensity (F.connection t) f z)
      (volume.restrict domain) := by
    apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℝ)) hquot
    refine Eventually.of_forall fun z => ?_
    exact (m65AreaDensity_metric_hasDerivAt F f z
      (by simpa only [interior_Icc] using ht)).tendsto_slope_zero
  exact hlimit.neg.congr (Eventually.of_forall fun z => neg_neg _)

end PoincareConjecture
