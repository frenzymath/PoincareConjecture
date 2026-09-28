import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.BoundaryAlignment
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.PlaneLift
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Hemisphere



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Manifold
open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩




theorem exists_spatial_upper_boundary_alignment_of_fillings
    {v : E3} (hv : ‖v‖ = 1)
    (γ : S1 → Hemisphere.Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ)
    (A B : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hA : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (hB : B '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    {a b : Real} (hab : a < b) :
    ∃ J : Hemisphere.Plane v ≃ₗᵢ[Real] E2,
      ∃ q : Diffeomorph (𝓡 1) (𝓡 1) S1 S1 ∞,
        (∀ p : S1, B (J.symm (q p)) = A (J.symm p)) ∧
        ∃ ε : Real, 0 < ε ∧ ε < 1 ∧
          ∃ S : Set (Hemisphere.Plane v), IsCompact S ∧
          ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
            (∀ x, inner Real v (D x) = inner Real v x) ∧
            (∀ x, inner Real v x ≤ a → D x = x) ∧
            (∀ x, (Hemisphere.Plane v).orthogonalProjectionOnto x ∉ S → D x = x) ∧
            (∀ (t : Real) (p : S1), D (t • v + (γ p : E3)) = t • v + (γ p : E3)) ∧
            ∀ (t : Real) (p : S1) (ρ : Real), b ≤ t → |ρ - 1| < ε →
              D (t • v + (B (ρ • J.symm (q p)) : E3)) =
                t • v + (A (ρ • J.symm p) : E3) := by
  let J : Hemisphere.Plane v ≃ₗᵢ[Real] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by
      intro heq
      simp [heq] at hv)).repr
  let j := J.toContinuousLinearEquiv.toDiffeomorph
  let A₂ := (j.symm.trans A).trans j
  let B₂ := (j.symm.trans B).trans j
  let γ₂ : S1 → E2 := J ∘ γ
  have hγ₂ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ γ₂ := by
    apply isSmoothEmbedding_of_injective_mfderiv (j.contMDiff.comp hγ.contMDiff)
      (J.injective.comp hγ.isEmbedding.injective)
    intro p
    change Injective (mfderiv (𝓡 1) (𝓡 2) (j ∘ γ) p)
    rw [mfderiv_comp p (j.contMDiff.mdifferentiable (by simp) _)
      (hγ.contMDiff.mdifferentiable (by simp) _)]
    exact (j.mfderivToContinuousLinearEquiv (by simp) (γ p)).injective.comp
      ((hγ.isImmersion.isImmersionAt p).injective_mfderiv_modelWithCornersSelf (by simp))
  have hA₂ : A₂ '' sphere (0 : E2) 1 = range γ₂ := by
    change (J ∘ A ∘ J.symm) '' sphere (0 : E2) 1 = range (J ∘ γ)
    rw [image_comp, image_comp, J.symm.image_sphere, map_zero, hA, range_comp]
  have hB₂ : B₂ '' sphere (0 : E2) 1 = range γ₂ := by
    change (J ∘ B ∘ J.symm) '' sphere (0 : E2) 1 = range (J ∘ γ)
    rw [image_comp, image_comp, J.symm.image_sphere, map_zero, hB, range_comp]
  obtain ⟨q, hq, ε, hε, hε1, K, hK, G, hGheight, hGlower, hGsupport, hGcircle, hGgerm⟩ :=
    exists_upper_boundary_alignment_of_planar_fillings γ₂ hγ₂ A₂ B₂ hA₂ hB₂ hab
  let C := (((ContinuousLinearEquiv.refl Real Real).prodCongr
    J.symm.toContinuousLinearEquiv).trans (heightCoordinates hv)).toDiffeomorph
  have hC (z : Real × E2) : C z = z.1 • v + (J.symm z.2 : E3) := rfl
  have hCheight (z : Real × E2) : inner Real v (C z) = z.1 := by
    rw [hC]
    simp [inner_add_right, inner_smul_right, hv,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (J.symm z.2).property]
  have hCinv (x : E3) : C.symm x =
      (inner Real v x, J ((Hemisphere.Plane v).orthogonalProjectionOnto x)) := rfl
  let D := (C.symm.trans G).trans C
  have hD (z : Real × E2) : D (C z) = C (G z) := by
    change C (G (C.symm (C z))) = C (G z)
    rw [C.symm_apply_apply]
  refine ⟨J, q, ?_, ε, hε, hε1, J.symm '' K,
    hK.image J.symm.continuous, D, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact J.injective (hq p)
  · intro x
    change inner Real v (C (G (C.symm x))) = inner Real v x
    rw [hCheight, hGheight, hCinv]
  · intro x hx
    change C (G (C.symm x)) = x
    rw [hCinv, hGlower _ _ hx]
    exact C.apply_symm_apply x
  · intro x hx
    have hxK : J ((Hemisphere.Plane v).orthogonalProjectionOnto x) ∉ K := by
      intro h
      exact hx ⟨_, h, J.symm_apply_apply _⟩
    change C (G (C.symm x)) = x
    rw [hCinv, hGsupport _ _ hxK]
    exact C.apply_symm_apply x
  · intro t p
    have hpoint : C (t, γ₂ p) = t • v + (γ p : E3) := by
      rw [hC]
      change t • v + (J.symm (J (γ p)) : E3) = _
      rw [J.symm_apply_apply]
    rw [← hpoint, hD, hGcircle]
  · intro t p ρ ht hρ
    have hleft : C (t, B₂ (ρ • (q p : E2))) =
        t • v + (B (ρ • J.symm (q p)) : E3) := by
      rw [hC]
      change t • v + (J.symm (J (B (J.symm (ρ • (q p : E2))))) : E3) = _
      rw [J.symm_apply_apply, map_smul]
    have hright : C (t, A₂ (ρ • (p : E2))) =
        t • v + (A (ρ • J.symm p) : E3) := by
      rw [hC]
      change t • v + (J.symm (J (A (J.symm (ρ • (p : E2))))) : E3) = _
      rw [J.symm_apply_apply, map_smul]
    rw [← hleft, ← hright, hD, hGgerm t p ρ ht hρ]

end Poincare.Manifold.Schoenflies
