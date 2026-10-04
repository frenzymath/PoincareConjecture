import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Cylinder.Geometry.CylinderRigidity
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Mathlib.DiffeomorphDerivative

/-!
# Metric rigidity of actual compatible cylinders

Morgan-Tian Theorem 12.28, pp. 323-324. A compatible cylinder with
identity at zero follows the fixed original spatial points. On its
open carrier this equality also identifies the actual differentials
and hence the normalized metric pullback.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M35.OrdinaryRealization

/-- Theorem 12.28: every compatible identity cylinder on an open
ordinary slice pulls back the original metric by the same inclusion. -/
theorem cylinder_pullbackInner_eq {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    {a Q : ℝ} {I : Set ℝ} {U : Set (slice J a).carrier}
    (e : GeneralizedFlowCylinder (generalizedFlow F) (slice J a) a Q I U)
    (hI : IsPreconnected I) (hU : IsOpen U) (h₀ : 0 ∈ I)
    (hzero : ∀ y ∈ U, e.pointMap 0 h₀ y = (⟨a, y⟩ : (generalizedFlow F).point))
    {s : ℝ} (hs : s ∈ I) {x : (slice J a).carrier} (hx : x ∈ U)
    (v w : TangentSpace (𝓡 3) x) :
    e.pullbackInner s hs x v w = Q * (F.metric (a + s / Q)).inner x.val
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : (slice J a).carrier → StandardCapSpace) x v)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : (slice J a).carrier → StandardCapSpace) x w) := by
  have htime : a + s / Q ∈ J := (e.forward s hs x).property
  let d := sliceDiffeomorph htime
  have heq : EqOn (d ∘ e.forward s hs)
      (Subtype.val : (slice J a).carrier → StandardCapSpace) U := by
    intro y hy
    exact (cylinder_spatial_eq F e hI hy hs h₀).trans
      (congrArg (fun p : (generalizedFlow F).point => p.2.val) (hzero y hy))
  have hevent : d ∘ e.forward s hs =ᶠ[𝓝 x]
      (Subtype.val : (slice J a).carrier → StandardCapSpace) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx) heq
  have hf := (e.forward_smooth s hs).contMDiffAt (hU.mem_nhds hx)
  have hderiv : mfderiv (𝓡 3) (𝓡 3) (d ∘ e.forward s hs) x =
      mfderiv (𝓡 3) (𝓡 3)
        (Subtype.val : (slice J a).carrier → StandardCapSpace) x := hevent.mfderiv_eq
  have hd (v : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) d (e.forward s hs x)
          (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v) =
        mfderiv (𝓡 3) (𝓡 3)
          (Subtype.val : (slice J a).carrier → StandardCapSpace) x v := by
    exact (mfderiv_comp_apply x (d.contMDiff.mdifferentiable (by simp) _)
      (hf.mdifferentiableAt (by simp)) v).symm.trans
        (congrArg (fun L => L v) hderiv)
  change Q * (F.metric (a + s / Q)).inner (d (e.forward s hs x))
    (mfderiv (𝓡 3) (𝓡 3) d (e.forward s hs x)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v))
    (mfderiv (𝓡 3) (𝓡 3) d (e.forward s hs x)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x w)) = _
  have hpoint : d (e.forward s hs x) = x.val := heq hx
  rw [hd v, hd w, hpoint]

end PoincareMT.M35.OrdinaryRealization
