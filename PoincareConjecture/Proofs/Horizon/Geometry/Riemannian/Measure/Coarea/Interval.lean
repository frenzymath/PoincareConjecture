import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Continuity
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed








set_option autoImplicit false

open Set Filter MeasureTheory TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

private theorem tendsto_integral_apprSeq_mul
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {H : X → ℝ}
    (hH : Integrable H μ) {f : X → ℝ} (hf : Measurable f)
    {s : Set ℝ} (hs : IsClosed s) :
    Tendsto (fun k : ℕ => ∫ x, (hs.apprSeq k (f x) : ℝ) * H x ∂μ)
      atTop (𝓝 (∫ x in f ⁻¹' s, H x ∂μ)) := by
  rw [← integral_indicator (hs.measurableSet.preimage hf)]
  apply tendsto_integral_of_dominated_convergence (fun x => ‖H x‖)
  · intro k
    have hmeas : Measurable (fun x => (hs.apprSeq k (f x) : ℝ)) :=
      (NNReal.continuous_coe.comp (hs.apprSeq k).continuous).measurable.comp hf
    exact hmeas.aestronglyMeasurable.mul hH.aestronglyMeasurable
  · exact hH.norm
  · intro k
    filter_upwards [] with x
    rw [norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (hs.apprSeq k (f x)).coe_nonneg]
    exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hs k (f x)
  · filter_upwards [] with x
    have ht := (NNReal.continuous_coe.tendsto _).comp
      (tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hs) (f x))
    have hm := ht.mul_const (H x)
    by_cases hx : f x ∈ s
    · simpa [hx] using hm
    · simpa [hx] using hm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  (g : RiemannianMetric (n + 1) M)
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (U : Opens M)
  (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)

include hf hreg in

theorem integral_coarea_isClosed
    {h : M → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (hU : tsupport h ⊆ U) {s : Set ℝ} (hs : IsClosed s) :
    (∫ x in f ⁻¹' s, h x * g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure) =
    ∫ c in s, ∫ z, h (openLevelIncl f U c z)
      ∂g.regularLevelVolume hf U hreg c := by
  let H : ℝ → ℝ := fun c => ∫ z, h (openLevelIncl f U c z)
    ∂g.regularLevelVolume hf U hreg c
  have hHi : Integrable H :=
    (g.continuous_regularLevelIntegral hf U hreg hh hc hU).integrable_of_hasCompactSupport
      (g.hasCompactSupport_regularLevelIntegral hf U hreg hc)
  have hleft := tendsto_integral_apprSeq_mul
    (g.integrable_volumeMeasure_of_hasCompactSupport
      (hh.mul (g.continuous_tangentNorm_gradient hf)) hc.mul_right)
    hf.continuous.measurable hs
  have hright := tendsto_integral_apprSeq_mul hHi measurable_id hs
  have heq (k : ℕ) :
      (∫ x, (hs.apprSeq k (f x) : ℝ) *
        (h x * g.tangentNorm x (g.gradient f x)) ∂g.volumeMeasure) =
      ∫ c, (hs.apprSeq k c : ℝ) * H c := by
    have hcont : Continuous (fun x => h x * (hs.apprSeq k (f x) : ℝ)) :=
      hh.mul ((NNReal.continuous_coe.comp (hs.apprSeq k).continuous).comp hf.continuous)
    have hcoarea := g.integral_coarea hf U hreg hcont hc.mul_right
      (tsupport_mul_subset_left.trans hU)
    calc
      _ = ∫ x in (U : Set M), (h x * (hs.apprSeq k (f x) : ℝ)) *
          g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
        · apply integral_congr_ae
          filter_upwards [] with x
          ring
        · intro x hx
          rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hU ht)), zero_mul, zero_mul]
      _ = _ := by
        rw [hcoarea]
        apply integral_congr_ae
        filter_upwards [] with c
        have hlevel (z : openLevelSet f U c) : f (openLevelIncl f U c z) = c := z.2
        simp_rw [hlevel]
        rw [integral_mul_const]
        exact mul_comm _ _
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall fun k => (heq k).symm))


theorem integral_coarea_Icc
    {h : M → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (hU : tsupport h ⊆ U) (a b : ℝ) :
    (∫ x in f ⁻¹' Icc a b, h x * g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure) =
    ∫ c in Icc a b, ∫ z, h (openLevelIncl f U c z)
      ∂g.regularLevelVolume hf U hreg c :=
  g.integral_coarea_isClosed hf U hreg hh hc hU isClosed_Icc

end PoincareConjecture.RiemannianMetric
