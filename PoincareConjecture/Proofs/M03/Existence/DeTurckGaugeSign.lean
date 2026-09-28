import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PoincareConjecture.Definitions.Ch03.RicciFlow

set_option autoImplicit false

namespace PoincareConjecture.DeTurckNative

theorem pullback_source_cancel (A L : ℝ) :
    (A + L) + (-L) = A := by
  ring

theorem hasDerivWithinAt_pullback_source_cancel
    {f h : ℝ → ℝ} {A L : ℝ} {J : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f (A + L) J t)
    (hh : HasDerivWithinAt h (-L) J t) :
    HasDerivWithinAt (fun s ↦ f s + h s) A J t := by
  have hadd := hf.add hh
  exact hadd.congr_deriv (by ring)

open Filter MeasureTheory Set

theorem integral_hasDerivWithinAt_Ico
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {a b t : ℝ} (hf : ContinuousOn f (Ico a b))
    (ht : t ∈ Ico a b) :
    HasDerivWithinAt (fun u => ∫ s in a..u, f s) (f t) (Ico a b) t := by
  obtain ⟨c, htc, hcb⟩ := exists_between ht.2
  have hsub : Icc a c ⊆ Ico a b := by
    intro s hs
    exact ⟨hs.1, hs.2.trans_lt hcb⟩
  have hfc : ContinuousOn f (Icc a c) := hf.mono hsub
  have hft : ContinuousOn f (Icc a t) :=
    hfc.mono (Icc_subset_Icc le_rfl htc.le)
  have htc_mem : t ∈ Icc a c := ⟨ht.1, htc.le⟩
  letI : Fact (t ∈ Icc a c) := ⟨htc_mem⟩
  have hderiv :
      HasDerivWithinAt (fun u => ∫ s in a..u, f s) (f t) (Icc a c) t :=
    intervalIntegral.integral_hasDerivWithinAt_right
      (hft.intervalIntegrable_of_Icc ht.1)
      (hfc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
      (hfc t htc_mem)
  apply hderiv.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htc)] with s hs hsc
  exact ⟨hs.1, hsc.le⟩

universe u

open scoped Manifold ContDiff

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem hasDerivWithinAt_metric_of_intervalIntegral_Ico
    {g₀ : RiemannianMetric n M} {g : ℝ → RiemannianMetric n M}
    {h : ℝ → ∀ p : M, TangentSpace (𝓡 n) p →
      TangentSpace (𝓡 n) p → ℝ} {T : ℝ}
    (hcont : ∀ (p : M) (v w : TangentSpace (𝓡 n) p),
      ContinuousOn (fun s ↦ h s p v w) (Ico 0 T))
    (hint : ∀ t ∈ Ico 0 T, ∀ (p : M)
      (v w : TangentSpace (𝓡 n) p),
      (g t).inner p v w = g₀.inner p v w +
        ∫ s in (0 : ℝ)..t, h s p v w)
    {t : ℝ} (ht : t ∈ Ico 0 T) (p : M)
    (v w : TangentSpace (𝓡 n) p) :
    HasDerivWithinAt (fun s ↦ (g s).inner p v w)
      (h t p v w) (Ico 0 T) t := by
  have hd := (integral_hasDerivWithinAt_Ico (hcont p v w) ht).const_add
    (g₀.inner p v w)
  exact hd.congr_of_mem (fun s hs ↦ hint s hs p v w) ht

end PoincareConjecture.DeTurckNative
