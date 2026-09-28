import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction.SmoothInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47



theorem terminalCurvature_exists_actual_partial_inverse
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]
    [Nonempty M]
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hembed : Topology.IsOpenEmbedding (fun x : U => f x))
    (hsmooth : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f U) :
    ∃ phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞,
      (phi : M → N) = f ∧ phi.source = U ∧ phi.target = f '' U := by
  have hinj : InjOn f U := fun x hx y hy hxy =>
    congrArg Subtype.val (hembed.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  let q := hinj.toPartialEquiv f U
  let H := OpenPartialHomeomorph.ofContinuousOpenRestrict q
    hsmooth.contMDiffOn.continuousOn hembed.isOpenMap hU
  have hinverse : ContMDiffOn (𝓡 3) (𝓡 3) ∞ H.symm H.target := by
    intro y hy
    have hx := H.map_target hy
    have hleft : ∀ᶠ z in 𝓝 (H.symm y), H.symm (f z) = z := by
      filter_upwards [H.open_source.mem_nhds hx] with z hz
      exact H.left_inv hz
    have hlocal := hsmooth ⟨H.symm y, hx⟩
    have h := Poincare.contMDiffAt_of_local_left_inverse hlocal.contMDiffAt
      (hlocal.mfderivToContinuousLinearEquiv (by simp)).bijective hleft
    have hright : f (H.symm y) = y := H.right_inv hy
    rw [hright] at h
    exact h.contMDiffWithinAt
  exact ⟨{ H.toPartialEquiv with
    open_source := H.open_source
    open_target := H.open_target
    contMDiffOn_toFun := hsmooth.contMDiffOn
    contMDiffOn_invFun := hinverse }, rfl, rfl, rfl⟩

end PoincareConjecture.M47
