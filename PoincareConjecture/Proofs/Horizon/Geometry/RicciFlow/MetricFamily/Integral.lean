import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricFamily.RelativeDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem integral_volumeMeasure_eq_reference
    (F : RicciFlow n M J) (h : RiemannianMetric n M) (t : ℝ) (f : M → ℝ) :
    (∫ x, f x ∂(F.metric t).volumeMeasure) =
      ∫ x, (F.metric t).relativeVolumeDensity h x * f x ∂h.volumeMeasure := by
  rw [F.volumeMeasure_eq_reference_withDensity h t]
  have hd : AEMeasurable
      (fun x => ENNReal.ofReal ((F.metric t).relativeVolumeDensity h x)) h.volumeMeasure :=
    (ENNReal.continuous_ofReal.comp
      ((F.metric t).continuous_relativeVolumeDensity h)).measurable.aemeasurable
  rw [integral_withDensity_eq_integral_toReal_smul₀ hd (by simp)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal ((F.metric t).relativeVolumeDensity_pos h x).le,
      smul_eq_mul]

theorem continuousOn_integral_volumeMeasure_of_compact_support
    (F : RicciFlow n M J) {s : Set ℝ} {A : Set M} {f : ℝ × M → ℝ}
    (hs : s ⊆ interior J) (hA : IsCompact A)
    (hf : ContinuousOn f (s ×ˢ univ))
    (hfs : ∀ t ∈ s, ∀ x ∉ A, f (t, x) = 0) :
    ContinuousOn (fun t => ∫ x, f (t, x) ∂(F.metric t).volumeMeasure) s := by
  have hρ := ((F.contMDiffOn_relativeVolumeDensity (F.metric 0)).continuousOn).mono
    (prod_mono hs (Subset.rfl : (univ : Set M) ⊆ univ))
  have hc : ContinuousOn (fun t => ∫ x,
      (F.metric t).relativeVolumeDensity (F.metric 0) x * f (t, x)
        ∂(F.metric 0).volumeMeasure) s := by
    apply continuousOn_integral_of_compact_support hA (hρ.mul hf)
    intro t x ht hx
    rw [hfs t ht x hx, mul_zero]
  apply hc.congr
  intro t _
  exact F.integral_volumeMeasure_eq_reference (F.metric 0) t (fun x => f (t, x))

theorem integrableOn_integral_volumeMeasure_Icc_of_compact_support
    (F : RicciFlow n M J) {a b : ℝ} {A : Set M} {f : ℝ × M → ℝ}
    (hab : Icc a b ⊆ interior J) (hA : IsCompact A)
    (hf : ContinuousOn f (Icc a b ×ˢ univ))
    (hfs : ∀ t ∈ Icc a b, ∀ x ∉ A, f (t, x) = 0) :
    IntegrableOn (fun t => ∫ x, f (t, x) ∂(F.metric t).volumeMeasure) (Icc a b) :=
  (F.continuousOn_integral_volumeMeasure_of_compact_support hab hA hf hfs).integrableOn_Icc

theorem continuousOn_backward_integral_volumeMeasure_of_compact_support
    (F : RicciFlow n M J) {α β : ℝ} {A : Set M} {f : M × ℝ → ℝ}
    (ht : ∀ τ ∈ Icc α β, -τ ∈ interior J) (hA : IsCompact A)
    (hf : ContinuousOn f (univ ×ˢ Icc α β))
    (hfs : ∀ τ ∈ Icc α β, ∀ x ∉ A, f (x, τ) = 0) :
    ContinuousOn (fun τ => ∫ x, f (x, τ) ∂(F.metric (-τ)).volumeMeasure) (Icc α β) := by
  have hneg (t : ℝ) (ht : t ∈ Icc (-β) (-α)) : -t ∈ Icc α β := by
    constructor <;> linarith [ht.1, ht.2]
  have hs : Icc (-β) (-α) ⊆ interior J := by
    intro t ht'
    simpa only [neg_neg] using ht (-t) (hneg t ht')
  have hg : ContinuousOn (fun z : ℝ × M => f (z.2, -z.1))
      (Icc (-β) (-α) ×ˢ univ) :=
    hf.comp ((continuous_snd.prodMk continuous_fst.neg).continuousOn)
      (fun z hz => ⟨mem_univ _, hneg z.1 hz.1⟩)
  have hc := F.continuousOn_integral_volumeMeasure_of_compact_support hs hA hg
    (fun t ht' x hx => hfs (-t) (hneg t ht') x hx)
  have hcomp := hc.comp continuous_neg.continuousOn
    (show MapsTo (fun τ : ℝ => -τ) (Icc α β) (Icc (-β) (-α)) from
      fun τ hτ => ⟨neg_le_neg hτ.2, neg_le_neg hτ.1⟩)
  simpa only [Function.comp_def, neg_neg] using hcomp

theorem integrableOn_backward_integral_volumeMeasure_Icc_of_compact_support
    (F : RicciFlow n M J) {α β : ℝ} {A : Set M} {f : M × ℝ → ℝ}
    (ht : ∀ τ ∈ Icc α β, -τ ∈ interior J) (hA : IsCompact A)
    (hf : ContinuousOn f (univ ×ˢ Icc α β))
    (hfs : ∀ τ ∈ Icc α β, ∀ x ∉ A, f (x, τ) = 0) :
    IntegrableOn (fun τ => ∫ x, f (x, τ) ∂(F.metric (-τ)).volumeMeasure) (Icc α β) :=
  (F.continuousOn_backward_integral_volumeMeasure_of_compact_support ht hA hf hfs).integrableOn_Icc

end PoincareConjecture.RicciFlow
