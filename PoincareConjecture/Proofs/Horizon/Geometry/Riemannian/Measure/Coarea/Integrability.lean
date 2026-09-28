import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.ChartSupport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.ChangeOfVariables

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]

theorem continuous_chartPullback
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {h : M → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (hs : tsupport h ⊆ e.target) : Continuous (chartPullback e h) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ e.source
  · exact (hh.continuousAt.comp (e.continuousAt hx)).congr_of_eventuallyEq
      (chartPullback_eventuallyEq e h hx)
  · have hx' : x ∉ tsupport (chartPullback e h) :=
      fun ht => hx (tsupport_chartPullback_subset_source e hc hs ht)
    exact continuousAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hx')

namespace RiemannianMetric

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem integrable_chartPullback_density_of_continuous
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {h : M → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (hs : tsupport h ⊆ e.target) :
    Integrable (fun x => chartPullback e h x * g.pullbackVolumeDensity e x) := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) e.source := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx))
      (hD.mfderiv_injective hx)).1.continuousAt.continuousWithinAt
  have hU := continuous_chartPullback e hh hc hs
  have hUs := tsupport_chartPullback_subset_source e hc hs
  have hUc := hasCompactSupport_chartPullback e hc hs
  apply Continuous.integrable_of_hasCompactSupport _ hUc.mul_right
  exact (hU.continuousOn.mul hρ).continuous_of_tsupport_subset e.open_source
    (tsupport_mul_subset_left.trans hUs)

theorem integrableOn_pullbackVolumeDensity
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {h : M → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (hs : tsupport h ⊆ e.target) :
    IntegrableOn (fun x => h (e x) * g.pullbackVolumeDensity e x) e.source := by
  apply (g.integrable_chartPullback_density_of_continuous e he hei hh hc hs).integrableOn.congr_fun
    _ e.open_source.measurableSet
  intro x hx
  simp only [chartPullback_apply e h hx]

end RiemannianMetric
end PoincareConjecture
