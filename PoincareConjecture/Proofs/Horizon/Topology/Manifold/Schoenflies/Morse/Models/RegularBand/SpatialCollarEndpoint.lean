import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CollarEndpoint
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.SpatialBoundaryAlignment

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Manifold Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1

theorem exists_spatial_collar_alignment_with_constant_endpoint
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
        ∃ ε : Real, 0 < ε ∧ ε < 1 ∧
          ∃ Q : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
              (Hemisphere.Plane v) (Hemisphere.Plane v) ∞,
            ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
              (∀ y, inner Real v (D y) = inner Real v y) ∧
              (∀ y, inner Real v y ≤ a → D y = y) ∧
              (∀ (t : Real) (p : S1), D (t • v + (γ p : E3)) = t • v + (γ p : E3)) ∧
              (∀ p : S1, Q (γ p) = γ p) ∧
              (∀ (t : Real) (x : Hemisphere.Plane v), b ≤ t →
                D (t • v + (x : E3)) = t • v + (Q x : E3)) ∧
              ∀ (p : S1) (ρ : Real), |ρ - 1| < ε →
                Q (B (ρ • J.symm (q p))) = A (ρ • J.symm p) := by
  let J : Hemisphere.Plane v ≃ₗᵢ[Real] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by intro h; simp [h] at hv)).repr
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
  obtain ⟨q, _, ε, hε, hε1, Q₂, G, hGfirst, hGlower, hGcircle, hGupper, hQgerm⟩ :=
    exists_upper_boundary_alignment_with_constant_endpoint γ₂ hγ₂ A₂ B₂ hA₂ hB₂ hab
  let Q := (j.trans Q₂).trans j.symm
  let C := (((ContinuousLinearEquiv.refl Real Real).prodCongr
    J.symm.toContinuousLinearEquiv).trans (heightCoordinates hv)).toDiffeomorph
  have hC (z : Real × E2) : C z = z.1 • v + (J.symm z.2 : E3) := rfl
  have hCinv (y : E3) : C.symm y =
      (inner Real v y, J ((Hemisphere.Plane v).orthogonalProjectionOnto y)) := rfl
  have hCh (z : Real × E2) : inner Real v (C z) = z.1 :=
    congrArg Prod.fst (C.symm_apply_apply z)
  let D := (C.symm.trans G).trans C
  have hD (z : Real × E2) : D (C z) = C (G z) := by
    change C (G (C.symm (C z))) = _
    rw [C.symm_apply_apply]
  have hpoint (t : Real) (x : Hemisphere.Plane v) : C (t, J x) = t • v + (x : E3) := by
    rw [hC, J.symm_apply_apply]
  refine ⟨J, q, ε, hε, hε1, Q, D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    change inner Real v (C (G (C.symm y))) = _
    rw [hCh, hGfirst]
    rfl
  · intro y hy
    change C (G (C.symm y)) = y
    rw [hCinv, hGlower _ _ hy]
    exact C.apply_symm_apply y
  · intro t p
    rw [← hpoint t (γ p), hD]
    change C (G (t, γ₂ p)) = _
    rw [hGcircle]
    rfl
  · intro p
    have hq : Q₂ (γ₂ p) = γ₂ p := by
      have h := hGcircle b p
      rw [hGupper b _ le_rfl] at h
      exact congrArg Prod.snd h
    change J.symm (Q₂ (γ₂ p)) = γ p
    rw [hq]
    exact J.symm_apply_apply _
  · intro t x ht
    rw [← hpoint t x, hD, hGupper t _ ht, hC]
    rfl
  · intro p ρ hρ
    apply J.injective
    change J (J.symm (Q₂ (J (B (ρ • J.symm (q p)))))) = J (A (ρ • J.symm p))
    rw [J.apply_symm_apply]
    have h := hQgerm p ρ hρ
    change Q₂ (J (B (J.symm (ρ • (q p : E2))))) =
      J (A (J.symm (ρ • (p : E2)))) at h
    simpa only [map_smul] using h

end Poincare.Manifold.Schoenflies
