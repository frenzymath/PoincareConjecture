import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.RiemannianMetric

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem integral_target_eq_integral_pullback_density
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {f : M → ℝ} (hf : ContinuousOn f e.target) :
    (∫ y in e.target, f y ∂g.volumeMeasure) =
      ∫ x in e.source, f (e x) * g.pullbackVolumeDensity e x := by
  have hmap := g.map_restrict_volumeMeasure_symm e he hei
  have hc : ContinuousOn (fun x => f (e x)) e.source :=
    hf.comp e.continuousOn e.mapsTo
  have hm : AEStronglyMeasurable (fun x => f (e x))
      ((g.volumeMeasure.restrict e.target).map e.symm) := by
    rw [hmap]
    exact hc.aestronglyMeasurable e.open_source.measurableSet
  have hi := integral_map (e.symm.continuousOn.aemeasurable e.open_target.measurableSet) hm
  have hid : (∫ y in e.target, f (e (e.symm y)) ∂g.volumeMeasure) =
      ∫ y in e.target, f y ∂g.volumeMeasure := by
    apply setIntegral_congr_fun e.open_target.measurableSet
    intro y hy
    exact congrArg f (e.right_inv hy)
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) e.source := by
    intro x hx
    have h := g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx))
      (hD.mfderiv_injective hx)
    exact h.1.continuousAt.continuousWithinAt
  change (∫ x, f (e x) ∂(g.volumeMeasure.restrict e.target).map e.symm) =
    (∫ y in e.target, f (e (e.symm y)) ∂g.volumeMeasure) at hi
  rw [hid, hmap] at hi
  rw [← hi]
  have hwith := setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (μ := volume)
    (f := fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))
    (s := e.source)
    ((ENNReal.continuous_ofReal.comp_continuousOn hρ).aemeasurable
      e.open_source.measurableSet)
    (show ∀ᵐ x ∂volume.restrict e.source,
      ENNReal.ofReal (g.pullbackVolumeDensity e x) < (⊤ : ℝ≥0∞) from
      Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    (fun x => f (e x)) e.open_source.measurableSet
  rw [hwith]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro x hx
  simp [pullbackVolumeDensity, ENNReal.toReal_ofReal, Real.sqrt_nonneg,
    smul_eq_mul, mul_comm]

end PoincareConjecture.RiemannianMetric
