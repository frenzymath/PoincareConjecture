import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.RicciNullity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometryRicci
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold PoincareConjecture.RicciFlow.Splitting
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M30

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

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

end PoincareConjecture.M30
