import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.TransportedCap
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.BoundaryReparametrization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.RadialGerm
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

theorem exists_parametrized_cylindrical_cap_with_range
    {v : E3} (hv : ‖v‖ = 1)
    (γ : S1 → Hemisphere.Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (c s : Real) (hs : s ≠ 0) :
    ∃ g : E2 → E3,
      ContDiff Real ∞ g ∧ Injective g ∧
      (∀ x, Injective (fderiv Real g x)) ∧
      (∀ p : S1, g p = c • v + (γ p : E3)) ∧
      (∀ x, ‖x‖ < 1 → 0 < (inner Real v (g x) - c) / s) ∧
      (∃ η : Real, 0 < η ∧ η < 1 ∧
        ∀ p : S1, ∀ ρ : Real, |ρ - 1| < η →
          g (ρ • (p : E2)) =
            (c + s * ((1 - ρ ^ 2) / (2 * ρ))) • v + (γ p : E3)) ∧
      (∀ x, (Hemisphere.Plane v).orthogonalProjectionOnto (g x) ∈
        A '' closedBall 0 1 ∧ |inner Real v (g x) - c| ≤ 2 * |s|) ∧
      g '' closedBall (0 : E2) 1 =
        Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv c s hs A ''
          ((fun p : sphere (0 : E3) 1 => boundedCylinderRadius v p • (p : E3)) ''
            {p : sphere (0 : E3) 1 | 0 ≤ inner Real v (p : E3)}) := by
  let J : Hemisphere.Plane v ≃ₗᵢ[Real] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by
      intro heq
      simp [heq] at hv)).repr
  let B := (J.symm.toContinuousLinearEquiv.toDiffeomorph.trans A).trans
    J.toContinuousLinearEquiv.toDiffeomorph
  have hJ : ContMDiff 𝓘(Real, Hemisphere.Plane v) (𝓡 2) ∞ J :=
    J.toContinuousLinearEquiv.contDiff.contMDiff
  have hemb : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (J ∘ γ) := by
    apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
      (hJ.comp hγ.contMDiff) (J.injective.comp hγ.isEmbedding.injective)
    intro p
    rw [mfderiv_comp p (hJ.mdifferentiable (by simp) _)
      (hγ.contMDiff.mdifferentiable (by simp) p)]
    exact (J.toContinuousLinearEquiv.toDiffeomorph.mfderivToContinuousLinearEquiv
      (by simp) (γ p)).injective.comp
      ((hγ.isImmersion.isImmersionAt p).injective_mfderiv_modelWithCornersSelf (by simp))
  have hBboundary : B '' sphere (0 : E2) 1 = range (J ∘ γ) := by
    change (J ∘ A ∘ J.symm) '' sphere (0 : E2) 1 = _
    rw [image_comp, image_comp, J.symm.image_sphere, map_zero, hboundary,
      ← range_comp]
  obtain ⟨q, hq⟩ := exists_planar_boundary_reparametrization (J ∘ γ) hemb B hBboundary
  have hqplane (p : S1) : A (J.symm (q p : E2)) = γ p := by
    apply J.injective
    exact hq p
  obtain ⟨H, hHclosed, hHball, η, hη, _, hradial⟩ :=
    exists_radial_ambient_diffeomorph_of_circle_diffeomorph q
  have hHcircle (p : S1) : H p = (q p : E2) := by
    simpa only [one_smul] using hradial p 1 (by simpa using hη)
  let D := H.trans J.symm.toContinuousLinearEquiv.toDiffeomorph
  have hDcircle (p : S1) : D p = J.symm (q p : E2) :=
    congrArg J.symm (hHcircle p)
  have hDball {x : E2} (hx : ‖x‖ < 1) : ‖D x‖ < 1 := by
    have hHx : H x ∈ ball (0 : E2) 1 :=
      hHball ▸ mem_image_of_mem H (mem_ball_zero_iff.mpr hx)
    change ‖J.symm (H x)‖ < 1
    simpa only [J.symm.norm_map] using mem_ball_zero_iff.mp hHx
  have hDclosed : D '' closedBall (0 : E2) 1 = closedBall (0 : Hemisphere.Plane v) 1 := by
    change (J.symm ∘ H) '' closedBall (0 : E2) 1 = _
    rw [image_comp, hHclosed, J.symm.image_closedBall, map_zero]
  obtain ⟨k, hk, hki, hkder, hkb, hkh, hkc, hkbound, hkrange⟩ :=
    exists_cylindrical_cap_over_disk_with_range hv c s hs A
  let g : E2 → E3 := k ∘ D
  refine ⟨g, hk.comp D.contDiff, hki.comp D.injective, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have hDder : Injective (fderiv Real D x) := by
      have h := (D.mfderivToContinuousLinearEquiv (by simp) x).injective
      change Injective (mfderiv (𝓡 2) 𝓘(Real, Hemisphere.Plane v) D x) at h
      simpa only [mfderiv_eq_fderiv, TangentSpace] using h
    rw [show g = k ∘ D from rfl, fderiv_comp x
      (hk.differentiable (by simp) (D x))
      (D.contDiff.differentiable (by simp) x)]
    exact (hkder (D x)).comp hDder
  · intro p
    change k (D p) = _
    rw [hDcircle, hkb _ (by simp only [J.symm.norm_map, norm_eq_of_mem_sphere]), hqplane]
  · intro x hx
    exact hkh (D x) (hDball hx)
  · refine ⟨min η (1 / 4), lt_min hη (by norm_num),
      (min_le_right _ _).trans_lt (by norm_num), fun p ρ hρ => ?_⟩
    have hρη : |ρ - 1| < η := hρ.trans_le (min_le_left _ _)
    have hρsmall : |ρ - 1| < (1 / 4 : Real) := hρ.trans_le (min_le_right _ _)
    have hρbounds := abs_lt.mp hρsmall
    change k (J.symm (H (ρ • (p : E2)))) = _
    rw [hradial p ρ hρη, map_smul, hkc _
      (by simp only [J.symm.norm_map, norm_eq_of_mem_sphere]) ρ
      (by linarith [hρbounds.1]) (by linarith [hρbounds.2]), hqplane]
  · intro x
    exact hkbound (D x)
  · change (k ∘ D) '' closedBall (0 : E2) 1 = _
    rw [image_comp, hDclosed, hkrange]

theorem exists_parametrized_cylindrical_cap
    {v : E3} (hv : ‖v‖ = 1)
    (γ : S1 → Hemisphere.Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (c s : Real) (hs : s ≠ 0) :
    ∃ g : E2 → E3,
      ContDiff Real ∞ g ∧ Injective g ∧
      (∀ x, Injective (fderiv Real g x)) ∧
      (∀ p : S1, g p = c • v + (γ p : E3)) ∧
      (∀ x, ‖x‖ < 1 → 0 < (inner Real v (g x) - c) / s) ∧
      (∃ η : Real, 0 < η ∧ η < 1 ∧
        ∀ p : S1, ∀ ρ : Real, |ρ - 1| < η →
          g (ρ • (p : E2)) =
            (c + s * ((1 - ρ ^ 2) / (2 * ρ))) • v + (γ p : E3)) ∧
      (∀ x, (Hemisphere.Plane v).orthogonalProjectionOnto (g x) ∈
        A '' closedBall 0 1 ∧ |inner Real v (g x) - c| ≤ 2 * |s|) := by
  obtain ⟨g, hg, hi, hd, hb, hh, hc, hbound, _⟩ :=
    exists_parametrized_cylindrical_cap_with_range hv γ hγ A hboundary c s hs
  exact ⟨g, hg, hi, hd, hb, hh, hc, hbound⟩

end Poincare.Manifold.Schoenflies
