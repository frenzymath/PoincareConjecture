import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.RelativeDensity.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem contMDiff_relativeVolumeDensity (g h : RiemannianMetric n M) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (g.relativeVolumeDensity h) := by
  intro p
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart_symm
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart
  have hp : p ∈ e.target := mem_chart_source _ p
  have hx : e.symm p ∈ e.source := e.map_target hp
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hg := g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds hx)) (hD.mfderiv_injective hx)
  have hh := h.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds hx)) (hD.mfderiv_injective hx)
  have hquot := (hg.1.div hh.1 hh.2.ne').contMDiffAt.comp p
    (hei.contMDiffAt (e.open_target.mem_nhds hp))
  apply hquot.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hp] with y hy
  symm
  change g.pullbackVolumeDensity e (e.symm y) /
    h.pullbackVolumeDensity e (e.symm y) = g.relativeVolumeDensity h y
  rw [← g.relativeVolumeDensity_eq_pullback_div h e (e.symm y)
    (hD.mfderiv_injective (e.map_target hy)), e.right_inv hy]

theorem continuous_relativeVolumeDensity (g h : RiemannianMetric n M) :
    Continuous (g.relativeVolumeDensity h) :=
  (g.contMDiff_relativeVolumeDensity h).continuous

end PoincareConjecture.RiemannianMetric
