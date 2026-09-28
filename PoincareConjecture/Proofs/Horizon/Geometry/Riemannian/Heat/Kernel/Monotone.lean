import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite
import Mathlib.MeasureTheory.Integral.DominatedConvergence












set_option autoImplicit false

open MeasureTheory Filter Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem integrable_limit_of_monotone_of_integral_le (g : RiemannianMetric n M)
    {F : ℕ → M → ℝ} {U : M → ℝ} {C : ℝ}
    (hF : ∀ j, Integrable (F j) g.volumeMeasure)
    (hpos : ∀ j x, 0 ≤ F j x) (hmono : ∀ x, Monotone (fun j => F j x))
    (hlim : ∀ x, Tendsto (fun j => F j x) atTop (𝓝 (U x)))
    (hbound : ∀ j, ∫ x, F j x ∂g.volumeMeasure ≤ C) :
    Integrable U g.volumeMeasure ∧ (∫ x, U x ∂g.volumeMeasure) ≤ C := by
  have hUpos (x : M) : 0 ≤ U x := ge_of_tendsto' (hlim x) (fun j => hpos j x)
  have hUm : AEStronglyMeasurable U g.volumeMeasure :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun j => (hF j).aestronglyMeasurable)
      (ae_of_all _ hlim)
  have hl := lintegral_tendsto_of_tendsto_of_monotone
    (μ := g.volumeMeasure) (fun j => (hF j).aemeasurable.ennreal_ofReal)
    (ae_of_all _ (fun x j k hjk => ENNReal.ofReal_le_ofReal (hmono x hjk)))
    (ae_of_all _ (fun x => (ENNReal.continuous_ofReal.tendsto _).comp (hlim x)))
  have hb : (∫⁻ x, ENNReal.ofReal (U x) ∂g.volumeMeasure) ≤ ENNReal.ofReal C := by
    apply le_of_tendsto' hl
    intro j
    rw [← ofReal_integral_eq_lintegral_ofReal (hF j) (ae_of_all _ (hpos j))]
    exact ENNReal.ofReal_le_ofReal (hbound j)
  have hUi : Integrable U g.volumeMeasure :=
    ⟨hUm, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hUpos)).mpr
      (hb.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hUi, ?_⟩
  have hC : 0 ≤ C := (integral_nonneg (hpos 0)).trans (hbound 0)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hUpos) hUm]
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb



theorem integrable_iSup_of_monotone_of_integral_le (g : RiemannianMetric n M)
    {F : ℕ → M → ℝ} {C : ℝ}
    (hF : ∀ j, Integrable (F j) g.volumeMeasure)
    (hpos : ∀ j x, 0 ≤ F j x) (hmono : ∀ x, Monotone (fun j => F j x))
    (hbdd : ∀ x, BddAbove (range (fun j => F j x)))
    (hbound : ∀ j, ∫ x, F j x ∂g.volumeMeasure ≤ C) :
    Integrable (fun x => ⨆ j, F j x) g.volumeMeasure ∧
      (∫ x, ⨆ j, F j x ∂g.volumeMeasure) ≤ C := by
  apply g.integrable_limit_of_monotone_of_integral_le hF hpos hmono ?_ hbound
  intro x
  exact tendsto_atTop_ciSup (hmono x) (hbdd x)



theorem integral_iSup_of_monotone_of_integral_le (g : RiemannianMetric n M)
    {F : ℕ → M → ℝ} {C : ℝ}
    (hF : ∀ j, Integrable (F j) g.volumeMeasure)
    (hpos : ∀ j x, 0 ≤ F j x) (hmono : ∀ x, Monotone (fun j => F j x))
    (hbdd : ∀ x, BddAbove (range (fun j => F j x)))
    (hbound : ∀ j, ∫ x, F j x ∂g.volumeMeasure ≤ C) :
    (∫ x, ⨆ j, F j x ∂g.volumeMeasure) = ⨆ j, ∫ x, F j x ∂g.volumeMeasure := by
  have hUi := (g.integrable_iSup_of_monotone_of_integral_le hF hpos hmono hbdd hbound).1
  have hl := integral_tendsto_of_tendsto_of_monotone hF hUi (ae_of_all _ hmono)
    (ae_of_all _ (fun x => tendsto_atTop_ciSup (hmono x) (hbdd x)))
  have hmi : Monotone (fun j => ∫ x, F j x ∂g.volumeMeasure) := by
    intro j k hjk
    exact integral_mono (hF j) (hF k) (fun x => hmono x hjk)
  have hbi : BddAbove (range (fun j => ∫ x, F j x ∂g.volumeMeasure)) :=
    ⟨C, forall_mem_range.mpr hbound⟩
  exact tendsto_nhds_unique hl (tendsto_atTop_ciSup hmi hbi)



theorem integrable_first_moment_limit_of_monotone (g : RiemannianMetric n M)
    {F : ℕ → M → ℝ} {U : M → ℝ} {x : M} {C : ℝ}
    (hF : ∀ j, Integrable (fun y => (g.edist x y).toReal * F j y) g.volumeMeasure)
    (hpos : ∀ j y, 0 ≤ F j y) (hmono : ∀ y, Monotone (fun j => F j y))
    (hlim : ∀ y, Tendsto (fun j => F j y) atTop (𝓝 (U y)))
    (hbound : ∀ j, ∫ y, (g.edist x y).toReal * F j y ∂g.volumeMeasure ≤ C) :
    Integrable (fun y => (g.edist x y).toReal * U y) g.volumeMeasure ∧
      (∫ y, (g.edist x y).toReal * U y ∂g.volumeMeasure) ≤ C := by
  apply g.integrable_limit_of_monotone_of_integral_le hF
    (fun j y => mul_nonneg ENNReal.toReal_nonneg (hpos j y))
    (fun y j k hjk => mul_le_mul_of_nonneg_left (hmono y hjk) ENNReal.toReal_nonneg)
    (fun y => (hlim y).const_mul _) hbound

end PoincareConjecture.RiemannianMetric
