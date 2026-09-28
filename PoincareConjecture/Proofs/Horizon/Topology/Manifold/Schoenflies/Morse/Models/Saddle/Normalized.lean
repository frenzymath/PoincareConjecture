import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.MorseCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.NormalForm
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev axis : E3 := EuclideanSpace.single 2 1
private abbrev HorizontalPlane := (Real ∙ axis)ᗮ
private instance : Fact (Module.finrank Real E3 = 2+1) := ⟨by simp⟩

theorem shear_sphere_smoothEmbedding :
    _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun p : S2 => shear p) := by
  have hc := contMDiff_coe_sphere (n := 2) (m := ∞) (E := E3)
  apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
    (shear.contMDiff.comp hc) (shear.injective.comp Subtype.val_injective)
  intro p
  rw [mfderiv_comp p ((shear.contMDiff (p : E3)).mdifferentiableAt (by simp))
    ((hc p).mdifferentiableAt (by simp))]
  apply (shear.mfderivToContinuousLinearEquiv (by simp) (p : E3)).injective.comp
  convert! injective_mvfderiv_subtypeVal_sphere p

theorem exists_height_preserving_quadratic_model :
    ∃ e : OpenPartialHomeomorph E2 S2,
      0 ∈ e.source ∧ e 0 = saddlePoint ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      ∃ J : E2 ≃ₗᵢ[Real] HorizontalPlane, ∃ r > 0,
        closedBall (0 : E2) r ⊆ e.source ∧
        ∃ A : Diffeomorph 𝓘(Real, HorizontalPlane) 𝓘(Real, HorizontalPlane)
            HorizontalPlane HorizontalPlane ∞,
        ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ y : E3, D y 2 = y 2) ∧
          (∀ (t : Real) (x : HorizontalPlane),
            D (t • axis + (x : E3)) = t • axis + (A x : E3)) ∧
          (∀ p : S2, D (shear p) 2 = height p) ∧
          ∀ x ∈ closedBall (0 : E2) r,
            D (shear (e x)) = (J x : E3) + (-1-(x 0)^2+(x 1)^2) • axis := by
  obtain ⟨e, he0, hep, he, hei, hform⟩ := exists_saddle_coordinates
  have haxis (y : E3) : inner Real axis y = y 2 := by
    simp [axis, PiLp.inner_apply]
  have hcrit : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun p : S2 => inner Real axis (shear p)) saddlePoint = 0 := by
    have heq : (fun p : S2 => inner Real axis (shear p)) = height :=
      funext (fun p => haxis (shear p))
    rw [heq]
    exact saddlePoint_critical
  have hf : ∀ x ∈ e.source, inner Real axis (shear (e x)) =
      inner Real axis (shear saddlePoint) + ∑ i : Fin 2, (![(-1 : Real), 1] i) * (x i)^2 := by
    intro x hx
    rw [haxis, haxis]
    change height (e x) = height saddlePoint + _
    rw [hform x hx, height_saddlePoint]
    simp [Fin.sum_univ_two]
    ring
  obtain ⟨J, r, hr, hrs, A, D, hDheight, hDplane, hD⟩ :=
    exists_height_preserving_critical_graph_with_plane_action shear_sphere_smoothEmbedding
      (show ‖axis‖ = 1 by simp [axis]) saddlePoint hcrit e he0 hep he hei ![-1, 1] hf
  refine ⟨e, he0, hep, he, hei, J, r, hr, hrs, A, D, ?_, hDplane, ?_, ?_⟩
  · intro y
    simpa only [haxis] using hDheight y
  · intro p
    simpa only [haxis, height] using hDheight (shear p)
  · intro x hx
    rw [hD x hx, haxis]
    change (J x : E3) + (height saddlePoint + _) • axis = _
    rw [height_saddlePoint]
    congr 2
    simp [Fin.sum_univ_two]
    ring

theorem exists_height_preserving_filled_quadratic_model :
    ∃ e : OpenPartialHomeomorph E2 S2,
      0 ∈ e.source ∧ e 0 = saddlePoint ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      ∃ J : E2 ≃ₗᵢ[Real] HorizontalPlane, ∃ r > 0,
        closedBall (0 : E2) r ⊆ e.source ∧
        ∃ D F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ y : E3, D y 2 = y 2) ∧
          (∀ y : E3, F y = D (shear y)) ∧
          F '' closedBall (0 : E3) 1 = D '' {p | polynomial p ≤ 1} ∧
          F '' ball (0 : E3) 1 = D '' {p | polynomial p < 1} ∧
          F '' sphere (0 : E3) 1 =
            (D '' band) ∪ ((D ∘ lowerCap 1) '' closedBall (0 : E2) (Real.sqrt (1/8))) ∪
              ((D ∘ lowerCap (-1)) '' closedBall (0 : E2) (Real.sqrt (1/8))) ∪
              ((D ∘ upperCap) '' closedBall (0 : E2) (Real.sqrt (3/4))) ∧
          (∀ p : S2, F p 2 = height p) ∧
          (∀ p : S2, mfderiv (𝓡 2) 𝓘(Real, Real) (fun q : S2 => F q 2) p = 0 ↔
            mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0) ∧
          ∀ x ∈ closedBall (0 : E2) r,
            F (e x) = (J x : E3) + (-1-(x 0)^2+(x 1)^2) • axis := by
  obtain ⟨e, he0, hep, he, hei, J, r, hr, hrs, _, D, hD, _, hheight, hpatch⟩ :=
    exists_height_preserving_quadratic_model
  let F := shear.trans D
  have hF (y : E3) : F y = D (shear y) := rfl
  have himage (K : Set E3) : F '' K = D '' (shear '' K) := image_comp D shear K
  refine ⟨e, he0, hep, he, hei, J, r, hr, hrs, D, F, hD, hF, ?_, ?_, ?_,
    hheight, ?_, hpatch⟩
  · rw [himage, shear_image_closedBall]
  · rw [himage, shear_image_ball]
  · rw [himage, shear_image_sphere_eq_band_union_caps,
      image_union, image_union, image_union, image_comp, image_comp, image_comp]
  · have heq : (fun q : S2 => F q 2) = height := funext hheight
    intro p
    rw [heq]

end Poincare.Manifold.Schoenflies.Saddle
