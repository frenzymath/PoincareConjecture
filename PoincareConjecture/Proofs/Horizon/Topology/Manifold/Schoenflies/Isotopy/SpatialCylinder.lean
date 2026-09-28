import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Cylinder
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.HeightCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Differential



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩



theorem exists_supported_ambient_cylinder
    {v : E3} (hv : ‖v‖ = 1) (c : Real) {r : Real} (hr : 0 < r)
    (f : Real × S1 -> (Real ∙ v)ᗮ)
    (hf : ContMDiff (𝓘(Real, Real).prod (𝓡 1)) 𝓘(Real, (Real ∙ v)ᗮ) ∞ f)
    (hemb : ∀ t ∈ Icc (-r) r, _root_.Manifold.IsSmoothEmbedding
      (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞ (fun p : S1 => f (t, p))) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ x, inner Real v (F x) = inner Real v x) ∧
      (∃ K : Set E3, IsCompact K ∧ ∀ x ∉ K, F x = x) ∧
      ∀ t ∈ Icc (-r) r, ∀ p : S1,
        F ((c + t) • v + (f (0, p) : E3)) = (c + t) • v + (f (t, p) : E3) := by
  let J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by
      intro heq
      simp [heq] at hv)).repr
  let g : Real × S1 -> E2 := fun z => J (f z)
  have hg : ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞ g :=
    J.toContinuousLinearEquiv.contDiff.contMDiff.comp hf
  have hgemb (t : Real) (ht : t ∈ Icc (-r) r) :
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (fun p : S1 => g (t, p)) := by
    have hs := (hemb t ht).contMDiff
    apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
      (J.toContinuousLinearEquiv.contDiff.contMDiff.comp hs)
      (J.injective.comp (hemb t ht).isEmbedding.injective)
    intro p
    have hJ : ContMDiff 𝓘(Real, (Real ∙ v)ᗮ) (𝓡 2) ∞ J.toContinuousLinearEquiv :=
      J.toContinuousLinearEquiv.contDiff.contMDiff
    change Function.Injective (mfderiv (𝓡 1) (𝓡 2)
      (J.toContinuousLinearEquiv ∘ (fun q => f (t, q))) p)
    rw [mfderiv_comp p (hJ.mdifferentiable (by simp) _) (hs.mdifferentiable (by simp) p)]
    exact (J.toContinuousLinearEquiv.toDiffeomorph.mfderivToContinuousLinearEquiv
      (by simp) (f (t, p))).injective.comp
      (((hemb t ht).isImmersion.isImmersionAt p).injective_mfderiv_modelWithCornersSelf
        (by simp))
  obtain ⟨G, hGt, ⟨K, hK, hGfix⟩, hG⟩ :=
    exists_supported_cylinder_parametrization hr g hg hgemb
  let A := ((ContinuousLinearEquiv.refl Real Real).prodCongr
    J.symm.toContinuousLinearEquiv).trans (Poincare.Geometry.Euclidean.heightCoordinates hv)
  let T : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ := {
    toEquiv := Equiv.addRight (c • v)
    contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
    contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff }
  let D := A.toDiffeomorph.trans T
  have hD (z : Real × E2) : D z = (c + z.1) • v + (J.symm z.2 : E3) := by
    change z.1 • v + (J.symm z.2 : E3) + c • v = _
    rw [add_smul]
    abel
  have hheight (z : Real × E2) : inner Real v (D z) = c + z.1 := by
    rw [hD]
    simp [inner_add_right, inner_smul_right, hv,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (J.symm z.2).property]
  let F := (D.symm.trans G).trans D
  refine ⟨F, ?_, ⟨D '' K, hK.image D.contMDiff.continuous, ?_⟩, ?_⟩
  · intro x
    change inner Real v (D (G (D.symm x))) = inner Real v x
    rw [hheight, hGt, ← hheight, D.apply_symm_apply]
  · intro x hx
    have hnot : D.symm x ∉ K := by
      intro hin
      exact hx ⟨D.symm x, hin, D.apply_symm_apply x⟩
    change D (G (D.symm x)) = x
    rw [hGfix _ hnot, D.apply_symm_apply]
  · intro t ht p
    have hDg (s : Real) : D (t, g (s, p)) = (c + t) • v + (f (s, p) : E3) := by
      rw [hD]
      simp [g]
    rw [← hDg 0]
    change D (G (D.symm (D (t, g (0, p))))) = _
    rw [D.symm_apply_apply, hG t ht p, hDg t]

end Poincare.Manifold.Schoenflies
