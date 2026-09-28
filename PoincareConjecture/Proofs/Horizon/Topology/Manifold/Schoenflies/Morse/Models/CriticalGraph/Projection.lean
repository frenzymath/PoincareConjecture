import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Coordinates.Ambient
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



theorem bijective_fderiv_critical_planar_projection
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) :
    Bijective (fderiv Real
      (fun x => J.symm ((Real ∙ v)ᗮ.orthogonalProjectionOnto (f (e x)))) 0) := by
  let d : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := he
    contMDiffOn_invFun := hei }
  have heloc : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ e 0 :=
    ⟨d, he0, fun _ _ => rfl⟩
  have hebij : Bijective (mfderiv (𝓡 2) (𝓡 2) e 0) :=
    (heloc.mfderivToContinuousLinearEquiv (by simp)).bijective
  let g : E2 → E3 := f ∘ e
  have hg : ContDiffAt Real ∞ g 0 :=
    ((hf.contMDiff (e 0)).comp 0 heloc.contMDiffAt).contDiffAt
  have hchain (u : E2) : fderiv Real g 0 u =
      mfderiv (𝓡 2) (𝓡 3) f p (mfderiv (𝓡 2) (𝓡 2) e 0 u) := by
    have h := mfderiv_comp 0
      ((hf.contMDiff (e 0)).mdifferentiableAt (by simp))
      (heloc.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv, hep] at h
    exact congrArg (fun L : E2 →L[Real] E3 => L u) h
  have hinj : Injective (fderiv Real g 0) := by
    intro u w huw
    apply hebij.injective
    apply injective_mfderiv_sphere_embedding hf p
    simpa only [hchain] using huw
  have horth (u : E2) : inner Real v (fderiv Real g 0 u) = 0 := by
    rw [hchain, ← mfderiv_height_apply hf.contMDiff, hp]
    rfl
  have hsplit (u : E2) : fderiv Real g 0 u =
      (((Real ∙ v)ᗮ.orthogonalProjectionOnto (fderiv Real g 0 u) : (Real ∙ v)ᗮ) : E3) := by
    nth_rw 1 [← (Real ∙ v).starProjection_add_starProjection_orthogonal (fderiv Real g 0 u)]
    rw [Submodule.starProjection_unit_singleton Real hv, horth]
    simp
  have hder : HasFDerivAt
      (fun x => J.symm ((Real ∙ v)ᗮ.orthogonalProjectionOnto (f (e x))))
      (J.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((Real ∙ v)ᗮ.orthogonalProjectionOnto.comp (fderiv Real g 0))) 0 :=
    J.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp 0
      ((Real ∙ v)ᗮ.orthogonalProjectionOnto.hasFDerivAt.comp 0
        (hg.differentiableAt (by simp)).hasFDerivAt)
  rw [hder.fderiv]
  have hi : Injective (J.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((Real ∙ v)ᗮ.orthogonalProjectionOnto.comp (fderiv Real g 0))) := by
    intro u w huw
    apply hinj
    rw [hsplit u, hsplit w]
    exact congrArg Subtype.val (J.symm.injective huw)
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

end Poincare.Manifold.Schoenflies
