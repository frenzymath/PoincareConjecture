import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.BallImages
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Geometry.Manifold.Instances.Sphere



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Pointwise

namespace Poincare.Manifold.Schoenflies.ParallelDisks

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

theorem exists_rescaled_disk_chart
    {R : Real} (hR : 0 < R) (e : OpenPartialHomeomorph E2 S2)
    (hsource : closedBall 0 R ⊆ e.source)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target) :
    ∃ d : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      d '' closedBall 0 1 = e '' closedBall 0 R ∧
      d '' ball 0 1 = e '' ball 0 R ∧
      d '' sphere (0 : E2) 1 = e '' sphere (0 : E2) R := by
  let L : E2 ≃L[Real] E2 :=
    (LinearEquiv.smulOfNeZero Real E2 R hR.ne').toContinuousLinearEquiv
  have hLclosed : L '' closedBall (0 : E2) 1 = closedBall 0 R := by
    change (fun x : E2 => R • x) '' closedBall 0 1 = _
    rw [image_smul, _root_.smul_closedBall' hR.ne', smul_zero, Real.norm_eq_abs,
      abs_of_pos hR, mul_one]
  have hLball : L '' ball (0 : E2) 1 = ball 0 R := by
    change (fun x : E2 => R • x) '' ball 0 1 = _
    rw [image_smul, _root_.smul_ball hR.ne', smul_zero, Real.norm_eq_abs,
      abs_of_pos hR, mul_one]
  have hLsphere : L '' sphere (0 : E2) 1 = sphere 0 R := by
    change (fun x : E2 => R • x) '' sphere 0 1 = _
    rw [image_smul, _root_.smul_sphere' hR.ne', smul_zero, Real.norm_eq_abs,
      abs_of_pos hR, mul_one]
  let d := L.toHomeomorph.toOpenPartialHomeomorph.trans e
  refine ⟨d, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨mem_univ _, hsource (hLclosed ▸ mem_image_of_mem L hx)⟩
  · exact he.comp L.contDiff.contMDiff.contMDiffOn (fun _ hx => hx.2)
  · exact L.symm.contDiff.contMDiff.comp_contMDiffOn (hei.mono (fun _ hx => hx.1))
  · change (e ∘ L) '' closedBall 0 1 = _
    rw [image_comp, hLclosed]
  · change (e ∘ L) '' ball 0 1 = _
    rw [image_comp, hLball]
  · change (e ∘ L) '' sphere 0 1 = _
    rw [image_comp, hLsphere]

theorem closure_image_ball {R : Real} (hR : 0 < R)
    (e : OpenPartialHomeomorph E2 S2) (hs : closedBall 0 R ⊆ e.source) :
    closure (e '' ball 0 R) = e '' closedBall 0 R := by
  have hK : IsCompact (e '' closedBall 0 R) :=
    (isCompact_closedBall 0 R).image_of_continuousOn (e.continuousOn.mono hs)
  apply Subset.antisymm (closure_minimal (image_mono ball_subset_closedBall) hK.isClosed)
  have hcont : ContinuousOn e (closure (ball (0 : E2) R)) := by
    rw [closure_ball _ hR.ne']
    exact e.continuousOn.mono hs
  simpa only [closure_ball _ hR.ne'] using hcont.image_closure

theorem frontier_image_ball {R : Real} (hR : 0 < R)
    (e : OpenPartialHomeomorph E2 S2) (hs : closedBall 0 R ⊆ e.source)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target) :
    frontier (e '' ball 0 R) = e '' sphere (0 : E2) R := by
  obtain ⟨d, hds, _, _, hdclosed, hdball, hdsphere⟩ :=
    exists_rescaled_disk_chart hR e hs he hei
  have hopen := d.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hds)
  have hclosed : IsClosed (d '' closedBall 0 1) :=
    ((isCompact_closedBall 0 1).image_of_continuousOn (d.continuousOn.mono hds)).isClosed
  rw [← hdball, hopen.frontier_eq, closure_image_ball zero_lt_one d hds,
    d.image_ball_eq_interior hds rfl, ← hclosed.frontier_eq,
    ← d.image_sphere_eq_frontier hds rfl, hdsphere]

end Poincare.Manifold.Schoenflies.ParallelDisks
