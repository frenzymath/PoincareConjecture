import PoincareLib.Geometry.RicciFlow.Splitting.MaximumPrinciple.RicciNullity
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometryRicci
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Ricci nullity under an actual local isometry

The differential of a supplied metric-preserving local diffeomorphism
identifies the full Ricci kernels of the two actual connections. Their
dimensions agree. This transports terminal nullity in Morgan--Tian
Claim 11.7, pp. 270-271, without a common source time interval.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold PoincareMT.RicciFlow.Splitting
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareMT.M30

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- An actual local isometry preserves the full Ricci-kernel dimension,
as used to transport terminal nullity in Claim 11.7, pp. 270-271. -/
theorem ricciNullity_eq_of_local_isometry
    {n : ℕ} {N : Type u} {M : Type v}
    [TopologicalSpace N] [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ N] [IsManifold (𝓡 n) ∞ M]
    {gN : RiemannianMetric n N} {gM : RiemannianMetric n M}
    (DN : LeviCivitaData gN) (DM : LeviCivitaData gM)
    {f : N → M} (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f)
    (hmetric : ∀ y : N, ∀ v1 v2 : TangentSpace (𝓡 n) y,
      gN.inner y v1 v2 = gM.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y v1) (mfderiv (𝓡 n) (𝓡 n) f y v2))
    (x : N) : ricciNullity DN x = ricciNullity DM (f x) := by
  let L := ((hf x).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  have hric (v w : TangentSpace (𝓡 n) x) :
      DN.ricci x v w = DM.ricci (f x) (L v) (L w) :=
    DN.ricci_eq_of_local_isometry DM isOpen_univ hf.contMDiff.contMDiffOn
      (fun y _ v1 v2 => hmetric y v1 v2) (mem_univ x) v w
  have hker : ricciKernel DM (f x) = (ricciKernel DN x).map L.toLinearMap := by
    ext v
    rw [Submodule.mem_map_equiv, mem_ricciKernel, mem_ricciKernel]
    constructor
    · intro hv w
      rw [hric, L.apply_symm_apply]
      exact hv _
    · intro hv w
      obtain ⟨z, rfl⟩ := L.surjective w
      have hz := hv z
      rw [hric, L.apply_symm_apply] at hz
      exact hz
  unfold ricciNullity
  rw [hker, LinearEquiv.finrank_map_eq]

end PoincareMT.M30
