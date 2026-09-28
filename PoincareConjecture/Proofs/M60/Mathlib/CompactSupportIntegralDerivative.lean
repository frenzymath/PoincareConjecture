import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M60

theorem hasDerivAt_integral_of_common_compact_support
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {F F' : ℝ → X → ℝ}
    {K : Set X} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε)
    (hF : ∀ s ∈ Ioo (-ε) ε, Continuous (F s))
    (hF' : ContinuousOn (Function.uncurry F') (Ioo (-ε) ε ×ˢ (univ : Set X)))
    (hdiff : ∀ s ∈ Ioo (-ε) ε, ∀ x, HasDerivAt (fun t => F t x) (F' s x) s)
    (hsupport : ∀ s ∈ Ioo (-ε) ε, ∀ x ∉ K, F s x = 0) :
    Integrable (F' 0) μ ∧
      HasDerivAt (fun s => ∫ x, F s x ∂μ) (∫ x, F' 0 x ∂μ) 0 := by
  classical
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hsmall : Icc (-ε / 2) (ε / 2) ⊆ Ioo (-ε) ε := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hK' : IsCompact (Icc (-ε / 2) (ε / 2) ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨C, hC⟩ := hK'.exists_bound_of_continuousOn
    (hF'.mono (prod_mono hsmall (subset_univ K)))
  let bound : X → ℝ := K.indicator (fun _ => max C 0)
  have hbound : Integrable bound μ := by
    rw [integrable_indicator_iff hK.measurableSet]
    exact integrableOn_const hK.measure_ne_top
  have hFint : Integrable (F 0) μ := by
    apply (hF 0 hzero).integrable_of_hasCompactSupport
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    exact hx (hsupport 0 hzero x hxK)
  have hF'meas : AEStronglyMeasurable (F' 0) μ :=
    (hF'.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨hzero, mem_univ x⟩)).aestronglyMeasurable
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo (-ε / 2) (ε / 2)) (bound := bound)
    (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩) _ hFint hF'meas _ hbound _
  · filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
    exact (hF s hs).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x s hs
    change ‖F' s x‖ ≤ K.indicator (fun _ => max C 0) x
    have hs' : s ∈ Ioo (-ε) ε := hsmall ⟨hs.1.le, hs.2.le⟩
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      exact (hC (s, x) ⟨⟨hs.1.le, hs.2.le⟩, hx⟩).trans (le_max_left _ _)
    · have hz : F' s x = 0 := (hdiff s hs' x).unique
        ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq (by
          filter_upwards [isOpen_Ioo.mem_nhds hs'] with t ht
          exact hsupport t ht x hx))
      simp only [hz, norm_zero, indicator_of_notMem hx, le_refl]
  · exact Filter.Eventually.of_forall (fun x s hs => hdiff s (hsmall ⟨hs.1.le, hs.2.le⟩) x)

end PoincareConjecture.M60
