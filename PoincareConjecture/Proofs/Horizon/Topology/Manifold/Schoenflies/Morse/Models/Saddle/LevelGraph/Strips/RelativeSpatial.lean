import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Strips.RelativeMatching
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.HeightCoordinates

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev P2 := Real × E2

def physicalStripHeightCoordinates {v : E3} (hv : ‖v‖ = 1)
    (J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2) (c : Real) :
    Diffeomorph 𝓘(Real, P2) (𝓡 3) P2 E3 ∞ :=
  let A := ((ContinuousLinearEquiv.refl Real Real).prodCongr
    J.symm.toContinuousLinearEquiv).trans (Poincare.Geometry.Euclidean.heightCoordinates hv)
  let T : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ := {
    toEquiv := Equiv.addRight (c • v)
    contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
    contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff }
  A.toDiffeomorph.trans T

theorem physicalStripHeightCoordinates_apply {v : E3} (hv : ‖v‖ = 1)
    (J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2) (c : Real) (z : P2) :
    physicalStripHeightCoordinates hv J c z = (c + z.1) • v + (J.symm z.2 : E3) := by
  change z.1 • v + (J.symm z.2 : E3) + c • v = _
  rw [add_smul]
  abel

theorem physicalStripHeightCoordinates_height {v : E3} (hv : ‖v‖ = 1)
    (J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2) (c : Real) (z : P2) :
    inner Real v (physicalStripHeightCoordinates hv J c z) = c + z.1 := by
  rw [physicalStripHeightCoordinates_apply]
  simp [inner_add_right, inner_smul_right, hv,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (J.symm z.2).property]

theorem physicalStripHeightCoordinates_symm {v : E3} (hv : ‖v‖ = 1)
    (J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2) (c : Real) (x : E3) :
    (physicalStripHeightCoordinates hv J c).symm x =
      (inner Real v x - c, J ((Real ∙ v)ᗮ.orthogonalProjectionOnto x)) := by
  apply (physicalStripHeightCoordinates hv J c).injective
  change physicalStripHeightCoordinates hv J c
      ((physicalStripHeightCoordinates hv J c).symm x) =
    physicalStripHeightCoordinates hv J c
      (inner Real v x - c, J ((Real ∙ v)ᗮ.orthogonalProjectionOnto x))
  rw [Diffeomorph.apply_symm_apply, physicalStripHeightCoordinates_apply,
    show c + (inner Real v x - c) = inner Real v x by ring, J.symm_apply_apply]
  exact ((Poincare.Geometry.Euclidean.heightCoordinates hv).apply_symm_apply x).symm

def physicalStripConjugate {v : E3} (hv : ‖v‖ = 1)
    (J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2) (c : Real)
    (H : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞) :
    Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ :=
  ((physicalStripHeightCoordinates hv J c).symm.trans H).trans
    (physicalStripHeightCoordinates hv J c)

theorem physicalStripConjugate_preserves_height {v : E3} (hv : ‖v‖ = 1)
    (J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2) (c : Real)
    (H : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞)
    (hH : ∀ z, (H z).1 = z.1) (x : E3) :
    inner Real v (physicalStripConjugate hv J c H x) = inner Real v x := by
  change inner Real v (physicalStripHeightCoordinates hv J c
    (H ((physicalStripHeightCoordinates hv J c).symm x))) = _
  rw [physicalStripHeightCoordinates_height, hH, physicalStripHeightCoordinates_symm]
  dsimp only
  ring

theorem physicalStripHeightCoordinates_strip {v : E3} (hv : ‖v‖ = 1)
    (J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2) (c : Real)
    (g : S2 → E3) (F : OpenPartialHomeomorph (Real × Real) S2)
    (z : Real × Real) (hh : inner Real v (g (F z)) = c + z.2) :
    physicalStripHeightCoordinates hv J c (z.2, stripPlaneMap g v J F z) = g (F z) := by
  rw [physicalStripHeightCoordinates_apply]
  simp only [stripPlaneMap, J.symm_apply_apply]
  rw [← hh]
  exact (Poincare.Geometry.Euclidean.heightCoordinates hv).apply_symm_apply _

theorem physicalStripConjugate_apply_strip {v : E3} (hv : ‖v‖ = 1)
    (J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2) (c : Real)
    (H : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞)
    (g₀ g₁ : S2 → E3) (F₀ F₁ : OpenPartialHomeomorph (Real × Real) S2)
    (z : Real × Real)
    (hh₀ : inner Real v (g₀ (F₀ z)) = c + z.2)
    (hh₁ : inner Real v (g₁ (F₁ z)) = c + z.2)
    (hH : H (z.2, stripPlaneMap g₀ v J F₀ z) = (z.2, stripPlaneMap g₁ v J F₁ z)) :
    physicalStripConjugate hv J c H (g₀ (F₀ z)) = g₁ (F₁ z) := by
  rw [← physicalStripHeightCoordinates_strip hv J c g₀ F₀ z hh₀]
  change physicalStripHeightCoordinates hv J c (H
    ((physicalStripHeightCoordinates hv J c).symm
      (physicalStripHeightCoordinates hv J c (z.2, stripPlaneMap g₀ v J F₀ z)))) = _
  rw [Diffeomorph.symm_apply_apply, hH,
    physicalStripHeightCoordinates_strip hv J c g₁ F₁ z hh₁]

theorem physicalStripConjugate_image_strip {v : E3} (hv : ‖v‖ = 1)
    (J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2) (c : Real)
    (H : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞)
    (g₀ g₁ : S2 → E3) (F₀ F₁ : OpenPartialHomeomorph (Real × Real) S2)
    (B : Set (Real × Real))
    (hh₀ : ∀ z ∈ B, inner Real v (g₀ (F₀ z)) = c + z.2)
    (hh₁ : ∀ z ∈ B, inner Real v (g₁ (F₁ z)) = c + z.2)
    (hH : ∀ z ∈ B,
      H (z.2, stripPlaneMap g₀ v J F₀ z) = (z.2, stripPlaneMap g₁ v J F₁ z)) :
    physicalStripConjugate hv J c H '' (g₀ '' (F₀ '' B)) = g₁ '' (F₁ '' B) := by
  have hpoint (z : Real × Real) (hz : z ∈ B) :=
    physicalStripConjugate_apply_strip hv J c H g₀ g₁ F₀ F₁ z
      (hh₀ z hz) (hh₁ z hz) (hH z hz)
  apply Subset.antisymm
  · rintro _ ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, (hpoint z hz).symm⟩
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, hpoint z hz⟩

theorem physicalStripConjugate_preserved_germ {v : E3} (hv : ‖v‖ = 1)
    (J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2) (c : Real)
    (H : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞)
    (Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {V : Set P2} (hV : IsOpen V) (hH : ∀ z ∈ V, H z = (z.1, Q z.2)) :
    IsOpen (physicalStripHeightCoordinates hv J c '' V) ∧
      ∀ x ∈ physicalStripHeightCoordinates hv J c '' V,
        physicalStripConjugate hv J c H x = inner Real v x • v +
          (J.symm (Q (J ((Real ∙ v)ᗮ.orthogonalProjectionOnto x))) : E3) := by
  refine ⟨(physicalStripHeightCoordinates hv J c).toHomeomorph.isOpenMap _ hV, ?_⟩
  intro x hx
  have hxs : (physicalStripHeightCoordinates hv J c).symm x ∈ V := by
    obtain ⟨z, hz, rfl⟩ := hx
    simpa only [Diffeomorph.symm_apply_apply] using hz
  change physicalStripHeightCoordinates hv J c
    (H ((physicalStripHeightCoordinates hv J c).symm x)) = _
  rw [hH _ hxs, physicalStripHeightCoordinates_apply, physicalStripHeightCoordinates_symm]
  dsimp only
  rw [show c + (inner Real v x - c) = inner Real v x by ring]

end Poincare.Manifold.Schoenflies.SaddleLevel
