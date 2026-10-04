import PoincareLib.Geometry.Riemannian.Coordinates.Coefficients
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The actual inverse partial chart in a neck pullback

The literal inverse identity recovers both tangent slots of a parameter
map. The inverse metric coefficients are smooth and positive on their
actual coordinate domain.
Source: derivations/terminal-curvature-moving-jets.md, Stage H5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M]

omit [IsManifold (𝓡 3) ∞ M] in
/-- The differential of the genuine inverse partial chart recovers the
original parameter differential at every included chart point. -/
theorem terminalCurvature_partial_chart_inverse_derivative
    (c : PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞)
    {phi : E → M} {x : E}
    (hphi : MDifferentiableAt (𝓡 3) (𝓡 3) phi x)
    (hx : phi x ∈ c.source) :
    (mfderiv (𝓡 3) (𝓡 3) c.symm (c (phi x))).comp
        (fderiv ℝ ((c : M → E) ∘ phi) x) =
      mfderiv (𝓡 3) (𝓡 3) phi x := by
  have hc := (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hx)).mdifferentiableAt
    (by simp)
  have hci := (c.contMDiffOn_invFun.contMDiffAt
    (c.open_target.mem_nhds (c.map_source hx))).mdifferentiableAt (by simp)
  have heq : (c.symm : E → M) ∘ ((c : M → E) ∘ phi) =ᶠ[𝓝 x] phi := by
    filter_upwards [hphi.continuousAt.tendsto.eventually (c.open_source.mem_nhds hx)]
      with y hy
    exact c.left_inv hy
  have hd := mfderiv_comp x hci (hc.comp x hphi)
  rw [mfderiv_eq_fderiv] at hd
  exact hd.symm.trans heq.mfderiv_eq

/-- Both metric slots use the same actual partial-chart inverse. -/
theorem terminalCurvature_partial_chart_metric
    (g : RiemannianMetric 3 M)
    (c : PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞)
    {phi : E → M} {x : E}
    (hphi : MDifferentiableAt (𝓡 3) (𝓡 3) phi x)
    (hx : phi x ∈ c.source) :
    (g.pullbackCoefficients c.symm (c (phi x))).bilinearComp
        (fderiv ℝ ((c : M → E) ∘ phi) x)
        (fderiv ℝ ((c : M → E) ∘ phi) x) = g.pullbackCoefficients phi x := by
  have hd := terminalCurvature_partial_chart_inverse_derivative c hphi hx
  ext v w
  change g.inner _
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c (phi x))
        (fderiv ℝ ((c : M → E) ∘ phi) x v))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c (phi x))
        (fderiv ℝ ((c : M → E) ∘ phi) x w)) =
    g.inner (phi x) (mfderiv (𝓡 3) (𝓡 3) phi x v)
      (mfderiv (𝓡 3) (𝓡 3) phi x w)
  exact (congrArg₂ (fun V W : E => g.inner (c.symm (c (phi x))) V W)
    (congrArg (fun A => A v) hd) (congrArg (fun A => A w) hd)).trans
      (congrArg (fun y : M => g.inner y (mfderiv (𝓡 3) (𝓡 3) phi x v)
        (mfderiv (𝓡 3) (𝓡 3) phi x w)) (c.left_inv hx))

/-- Inverse partial-chart coefficients have their actual smoothness and
nonsingularity on the literal target, without a global extension. -/
theorem terminalCurvature_partial_chart_coefficients
    (g : RiemannianMetric 3 M)
    (c : PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞) :
    ContDiffOn ℝ ∞ (g.pullbackCoefficients c.symm) c.target ∧
      ∀ y ∈ c.target, (g.pullbackCoefficients c.symm y).IsInvertible := by
  constructor
  · intro y hy
    exact (g.contDiffAt_pullbackCoefficients
      (c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds hy))).contDiffWithinAt
  · intro y hy
    have hlocal := c.symm.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hy
    exact g.isInvertible_pullbackCoefficients
      (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective

end PoincareMT.M47
