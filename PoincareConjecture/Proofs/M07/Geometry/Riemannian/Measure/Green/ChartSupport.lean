import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.Algebra.Support

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]

noncomputable def chartPullback
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M) (u : M → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  e.source.indicator (u ∘ e)

theorem chartPullback_apply
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M) (u : M → ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) :
    chartPullback e u x = u (e x) :=
  indicator_of_mem hx _

theorem chartPullback_eventuallyEq
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M) (u : M → ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) :
    chartPullback e u =ᶠ[𝓝 x] u ∘ e := by
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  exact chartPullback_apply e u hy

theorem tsupport_chartPullback_subset_image
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M) {u : M → ℝ}
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ e.target) :
    tsupport (chartPullback e u) ⊆ e.symm '' tsupport u := by
  have hK : IsCompact (e.symm '' tsupport u) :=
    hc.isCompact.image_of_continuousOn (e.symm.continuousOn.mono hs)
  apply closure_minimal _ hK.isClosed
  intro x hx
  have hxsource : x ∈ e.source := by
    by_contra h
    exact hx (indicator_of_notMem h _)
  refine ⟨e x, subset_tsupport u ?_, e.left_inv hxsource⟩
  simpa only [Function.mem_support, chartPullback_apply e u hxsource] using hx

theorem tsupport_chartPullback_subset_source
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M) {u : M → ℝ}
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ e.target) :
    tsupport (chartPullback e u) ⊆ e.source := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := tsupport_chartPullback_subset_image e hc hs hx
  exact e.map_target (hs hy)

theorem hasCompactSupport_chartPullback
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M) {u : M → ℝ}
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ e.target) :
    HasCompactSupport (chartPullback e u) := by
  exact IsCompact.of_isClosed_subset
    (hc.isCompact.image_of_continuousOn (e.symm.continuousOn.mono hs))
    (isClosed_tsupport _) (tsupport_chartPullback_subset_image e hc hs)

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem contDiff_chartPullback
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M) {u : M → ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ e.target) :
    ContDiff ℝ ∞ (chartPullback e u) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ e.source
  · apply ContDiffAt.congr_of_eventuallyEq _ (chartPullback_eventuallyEq e u hx)
    exact ((hu (e x)).comp x (he.contMDiffAt (e.open_source.mem_nhds hx))).contDiffAt
  · have hx' : x ∉ tsupport (chartPullback e u) :=
      fun h => hx (tsupport_chartPullback_subset_source e hc hs h)
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const
      (notMem_tsupport_iff_eventuallyEq.mp hx')

end PoincareConjecture
