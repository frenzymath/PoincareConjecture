import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.DiskSublevels
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential
import Mathlib.Analysis.Calculus.TangentCone.Real



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1



theorem mfderiv_eq_on_smooth_closed_disk
    {h k : S2 → Real}
    (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hk : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ k)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (heq : EqOn h k (d '' closedBall 0 1)) :
    ∀ x ∈ d '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) h x = mfderiv (𝓡 2) 𝓘(Real, Real) k x := by
  let P : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ :=
    { toPartialEquiv := d.toPartialEquiv
      open_source := d.open_source
      open_target := d.open_target
      contMDiffOn_toFun := hd
      contMDiffOn_invFun := hdi }
  have hball : UniqueDiffOn Real (closedBall (0 : E2) 1) :=
    uniqueDiffOn_convex (convex_closedBall 0 1)
      (by rw [interior_closedBall (0 : E2) one_ne_zero]; exact ⟨0, mem_ball_self zero_lt_one⟩)
  rintro _ ⟨x, hx, rfl⟩
  have hloc := P.isLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ (hds hx)
  have hud : UniqueMDiffWithinAt (𝓡 2) (d '' closedBall (0 : E2) 1) (d x) :=
    (hball x hx).uniqueMDiffWithinAt.image_denseRange
      (hloc.contMDiffAt.mdifferentiableAt (by simp)).hasMFDerivAt.hasMFDerivWithinAt
      (hloc.mfderivToContinuousLinearEquiv (by simp)).surjective.denseRange
  rw [← mfderivWithin_eq_mfderiv hud (hh.mdifferentiable (by simp) (d x)),
    ← mfderivWithin_eq_mfderiv hud (hk.mdifferentiable (by simp) (d x))]
  exact mfderivWithin_congr_of_mem heq (mem_image_of_mem d hx)

end Poincare.Manifold.Schoenflies
