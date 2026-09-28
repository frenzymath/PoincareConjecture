import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallShrinking
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Chart
import Mathlib.Analysis.Normed.Module.Ball.Pointwise










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

variable {E A H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NormedAddCommGroup A] [NormedSpace Real A]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners Real A H}



theorem exists_supported_chart_shrinking_isotopy
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn 𝓘(Real, E) I ∞ e e.source)
    (hei : ContMDiffOn I 𝓘(Real, E) ∞ e.symm e.target)
    {r c : Real} (hr : 0 < r) (hc : 0 < c) (hc1 : c ≤ 1)
    (hball : closedBall (0 : E) r ⊆ e.source) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ e.target ∧
      ∃ Phi : Real -> Diffeomorph I I M M ∞,
      (∀ x, Phi 0 x = x) ∧
      ContMDiff (𝓘(Real, Real).prod I) I ∞ (fun p : Real × M => Phi p.1 p.2) ∧
      (∀ t x, x ∉ K -> Phi t x = x) ∧
      ∀ t ∈ Icc (0 : Real) 1, ∀ x ∈ closedBall (0 : E) r,
        Phi t (e x) = e (Real.exp (t * Real.log c) • x) := by
  classical
  obtain ⟨delta, hd, hdsub⟩ := (isCompact_closedBall (0 : E) r).exists_cthickening_subset_open
    e.open_source hball
  rw [cthickening_closedBall hd.le hr.le] at hdsub
  let R := delta + r
  have hrR : r < R := by dsimp [R]; linarith
  obtain ⟨F, hF0, hFs, hFfix, hmotion⟩ :=
    exists_supported_ball_shrinking_isotopy (E := E) hr hrR hc hc1
  have hR : closedBall (0 : E) R ⊆ e.source := hdsub
  obtain ⟨hK, hKU, Phi, hi, hs, hfix, hcoord⟩ :=
    exists_supported_chart_isotopy e he hei (isCompact_closedBall 0 R) hR F hF0 hFs hFfix
  refine ⟨e '' closedBall (0 : E) R, hK, hKU, Phi, hi, hs, hfix, ?_⟩
  intro t ht x hx
  rw [hcoord t x (hball hx), hmotion t ht x hx]

end Poincare.Manifold.Schoenflies
