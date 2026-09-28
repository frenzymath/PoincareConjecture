import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightCoordinates
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection












set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



noncomputable def heightPlaneCoordinates (u : UnitTwoSphere) : E3 ≃L[ℝ] E2 × ℝ :=
  let R := (ℝ ∙ ((u : E3) - EuclideanSpace.single (2 : Fin 3) 1))ᗮ.reflection
  R.toContinuousLinearEquiv.trans heightCoordinates


theorem heightPlaneCoordinates_snd (u : UnitTwoSphere) (y : E3) :
    (heightPlaneCoordinates u y).2 = ⟪(u : E3), y⟫_ℝ := by
  let v : E3 := EuclideanSpace.single (2 : Fin 3) 1
  let R : E3 ≃ₗᵢ[ℝ] E3 := (ℝ ∙ ((u : E3) - v))ᗮ.reflection
  have huv : ‖(u : E3)‖ = ‖v‖ := by simp [v, norm_eq_of_mem_sphere u]
  have hRu : R (u : E3) = v := Submodule.reflection_sub huv
  change (heightCoordinates (R y)).2 = ⟪(u : E3), y⟫_ℝ
  rw [heightCoordinates_snd_apply]
  calc
    R y 2 = ⟪v, R y⟫_ℝ := by simp [v, EuclideanSpace.inner_single_left]
    _ = ⟪R (u : E3), R y⟫_ℝ := by rw [hRu]
    _ = ⟪(u : E3), y⟫_ℝ := R.inner_map_map _ _



theorem heightPlaneCoordinates_reconstruct (u : UnitTwoSphere) (y : E3)
    (t : ℝ) (ht : ⟪(u : E3), y⟫_ℝ = t) :
    (heightPlaneCoordinates u).symm ((heightPlaneCoordinates u y).1, t) = y := by
  apply (heightPlaneCoordinates u).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact Prod.ext rfl ((heightPlaneCoordinates_snd u y).trans ht).symm



theorem isPlanarEmbedding_height_projection (u : UnitTwoSphere)
    (c : UnitCircle → E3) (hc : ContMDiff (𝓡 1) 𝓘(ℝ, E3) ∞ c)
    (hci : Injective c)
    (hcd : ∀ q, Injective (mfderiv (𝓡 1) 𝓘(ℝ, E3) c q))
    (t : ℝ) (ht : ∀ q, ⟪(u : E3), c q⟫_ℝ = t) :
    IsPlanarEmbedding (fun q => (heightPlaneCoordinates u (c q)).1) := by
  let E := heightPlaneCoordinates u
  let g : UnitCircle → E2 := fun q => (E (c q)).1
  let A : E2 → E3 := fun p => E.symm (p, t)
  have hA : ContDiff ℝ ∞ A :=
    E.symm.contDiff.comp (contDiff_id.prodMk contDiff_const)
  have hg : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞ g :=
    contDiff_fst.contMDiff.comp (E.contDiff.contMDiff.comp hc)
  have hrec : A ∘ g = c := by
    funext q
    exact heightPlaneCoordinates_reconstruct u (c q) t (ht q)
  refine ⟨hg, ?_, ?_⟩
  · intro p q hpq
    apply hci
    rw [← congrFun hrec p, ← congrFun hrec q]
    exact congrArg A hpq
  · intro q
    have hd := (hA.contMDiff.mdifferentiable (by simp) (g q)).hasMFDerivAt.comp q
      (hg.mdifferentiable (by simp) q).hasMFDerivAt
    rw [hrec] at hd
    intro a b hab
    apply hcd q
    rw [hd.mfderiv]
    exact congrArg (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E3) A (g q)) hab

end PoincareConjecture.M25.Topology3D
