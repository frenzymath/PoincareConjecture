import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.UpperLevel.Circle
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

def upperProjection (p : E3) : E2 := WithLp.toLp 2 ![p 0, p 1]

theorem upperProjection_contDiff : ContDiff Real ∞ upperProjection := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> change ContDiff Real ∞ (fun p : E3 => p _) <;> fun_prop

theorem upperReconstruction_projection {p : S2} (hp : height p = 13 / 10) :
    upperReconstruction (upperProjection p) = (p : E3) := by
  rw [height_apply] at hp
  ext i
  fin_cases i
  · rfl
  · rfl
  · change 13 / 10 - ((p : E3) 0)^2 - ((p : E3) 1)^2 -
      (3 / 10) * (p : E3) 0 = (p : E3) 2
    linarith

theorem upperProjection_sphereMap {q : E2} (hq : q ∈ upperLevelSet) :
    upperProjection (upperSphereMap q) = q := by
  rw [upperSphereMap_coe hq]
  ext i
  fin_cases i <;> rfl

theorem upperProjection_image :
    (fun p : S2 => upperProjection p) '' (height ⁻¹' {(13 / 10 : Real)}) =
      upperLevelSet := by
  rw [← upperSphereMap_image, image_image]
  apply Subset.antisymm
  · rintro q ⟨x, hx, rfl⟩
    change upperProjection (upperSphereMap x) ∈ upperLevelSet
    rwa [upperProjection_sphereMap hx]
  · intro q hq
    exact ⟨q, hq, upperProjection_sphereMap hq⟩


theorem exists_smooth_circle_upper_level :
    ∃ γ : S1 → E2,
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ γ ∧
      range γ = upperLevelSet := by
  obtain ⟨γ, hγ, hinj, hder, hrange⟩ := exists_smooth_circle_upper_height_level
  let g : S1 → E2 := fun p => upperProjection (γ p)
  have hc := contMDiff_coe_sphere (n := 2) (m := ∞) (E := E3)
  have hg : ContMDiff (𝓡 1) (𝓡 2) ∞ g :=
    upperProjection_contDiff.contMDiff.comp (hc.comp hγ)
  have hheight (p : S1) : height (γ p) = 13 / 10 := by
    have hp : γ p ∈ range γ := mem_range_self p
    rwa [hrange] at hp
  have heq : upperReconstruction ∘ g = (fun p => (γ p : E3)) :=
    funext (fun p => upperReconstruction_projection (hheight p))
  have hgi : Injective g := by
    intro p q hpq
    apply hinj
    apply Subtype.val_injective
    change (fun p => (γ p : E3)) p = (fun p => (γ p : E3)) q
    rw [← heq]
    exact congrArg upperReconstruction hpq
  have hgd : ∀ p, Injective (mfderiv (𝓡 1) (𝓡 2) g p) := by
    intro p
    have hcoeder : Injective (mfderiv (𝓡 1) (𝓡 3) (fun p => (γ p : E3)) p) := by
      change Injective (mfderiv (𝓡 1) 𝓘(Real, E3) ((Subtype.val : S2 → E3) ∘ γ) p)
      rw [mfderiv_comp p ((hc (γ p)).mdifferentiableAt (by simp))
        ((hγ p).mdifferentiableAt (by simp))]
      apply Function.Injective.comp _ (hder p)
      convert! injective_mvfderiv_subtypeVal_sphere (γ p)
    have hcomp :
        (mfderiv (𝓡 2) (𝓡 3) upperReconstruction (g p)).comp
          (mfderiv (𝓡 1) (𝓡 2) g p) =
        mfderiv (𝓡 1) (𝓡 3) (fun p => (γ p : E3)) p := by
      rw [← mfderiv_comp p
        ((upperReconstruction_contDiff.contMDiff (g p)).mdifferentiableAt (by simp))
        ((hg p).mdifferentiableAt (by simp)), heq]
    have hci : Injective ((mfderiv (𝓡 2) (𝓡 3) upperReconstruction (g p)).comp
        (mfderiv (𝓡 1) (𝓡 2) g p)) := by rwa [hcomp]
    intro u v huv
    exact hci (congrArg (mfderiv (𝓡 2) (𝓡 3) upperReconstruction (g p)) huv)
  refine ⟨g, Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv hg hgi hgd, ?_⟩
  change range ((fun p : S2 => upperProjection p) ∘ γ) = _
  rw [range_comp, hrange, upperProjection_image]

end Poincare.Manifold.Schoenflies.Saddle.Nested
