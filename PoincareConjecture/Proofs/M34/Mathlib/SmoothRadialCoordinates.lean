import PoincareConjecture.Proofs.M34.Mathlib.OpenDomainCoordinates
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def radialUnitPoint (x : ({0}ᶜ : Set E)) : sphere (0 : E) 1 :=
  ⟨‖(x : E)‖⁻¹ • (x : E), by
    have hx : (x : E) ≠ 0 := x.property
    simp [norm_smul, norm_ne_zero_iff.mpr hx]⟩

noncomputable def radialSphereCoordinates (x : ({0}ᶜ : Set E)) :
    sphere (0 : E) 1 × ℝ :=
  (radialUnitPoint x, ‖(x : E)‖ - 1)

def radialSphereReconstruct (p : sphere (0 : E) 1 × ℝ) : E :=
  (p.2 + 1) • (p.1 : E)

theorem radialSphereReconstruct_coordinates (x : ({0}ᶜ : Set E)) :
    radialSphereReconstruct (radialSphereCoordinates x) = (x : E) := by
  have hx : (x : E) ≠ 0 := x.property
  simp [radialSphereReconstruct, radialSphereCoordinates, radialUnitPoint,
    smul_smul, norm_ne_zero_iff.mpr hx]

end Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
  [Nonempty ({0}ᶜ : Set E)]

local instance : ChartedSpace E ({0}ᶜ : Set E) :=
  isOpen_compl_singleton.isOpenEmbedding_subtypeVal.singletonChartedSpace

local instance : IsManifold 𝓘(ℝ, E) ω ({0}ᶜ : Set E) :=
  isOpen_compl_singleton.isOpenEmbedding_subtypeVal.isManifold_singleton

variable {m : ℕ∞ω}

theorem contMDiff_radialNorm :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) m (fun x : ({0}ᶜ : Set E) => ‖(x : E)‖) := by
  have hcoe : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) m
      (Subtype.val : ({0}ᶜ : Set E) → E) :=
    contMDiff_isOpenEmbedding isOpen_compl_singleton.isOpenEmbedding_subtypeVal
  intro x
  exact (contDiffAt_norm ℝ (show (x : E) ≠ 0 from x.property)).contMDiffAt.comp x (hcoe x)

theorem contMDiff_radialUnitPoint :
    ContMDiff 𝓘(ℝ, E) (𝓡 n) m (radialUnitPoint (E := E)) := by
  have hcoe : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) m
      (Subtype.val : ({0}ᶜ : Set E) → E) :=
    contMDiff_isOpenEmbedding isOpen_compl_singleton.isOpenEmbedding_subtypeVal
  have hn := contMDiff_radialNorm (E := E) (m := m)
  have hi := hn.inv₀ (fun x => norm_ne_zero_iff.mpr (show (x : E) ≠ 0 from x.property))
  exact (hi.smul hcoe).codRestrict_sphere (fun x => (radialUnitPoint x).property)

theorem contMDiff_radialSphereCoordinates :
    ContMDiff 𝓘(ℝ, E) ((𝓡 n).prod 𝓘(ℝ, ℝ)) m
      (radialSphereCoordinates (E := E)) :=
  contMDiff_radialUnitPoint.prodMk (contMDiff_radialNorm.sub contMDiff_const)

omit [Nonempty ({0}ᶜ : Set E)] in

theorem contMDiff_radialSphereReconstruct :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) m
      (radialSphereReconstruct (E := E)) :=
  (contMDiff_snd.add contMDiff_const).smul (contMDiff_coe_sphere.comp contMDiff_fst)

theorem radialSphereCoordinates_mfderiv_injective (x : ({0}ᶜ : Set E)) :
    Function.Injective
      (mfderiv 𝓘(ℝ, E) ((𝓡 n).prod 𝓘(ℝ, ℝ)) radialSphereCoordinates x) := by
  have hcomp := mfderiv_comp x
    ((contMDiff_radialSphereReconstruct (n := n) (m := ∞)).mdifferentiable (by simp)
      (radialSphereCoordinates x))
    ((contMDiff_radialSphereCoordinates (n := n) (m := ∞)).mdifferentiable (by simp) x)
  have hid : radialSphereReconstruct ∘ radialSphereCoordinates =
      (Subtype.val : ({0}ᶜ : Set E) → E) :=
    funext radialSphereReconstruct_coordinates
  rw [hid, mfderiv_subtypeVal_singleton isOpen_compl_singleton] at hcomp
  intro v w hvw
  have h := congrArg
    (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
      radialSphereReconstruct (radialSphereCoordinates x)) hvw
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, ← hcomp] at h
  exact h

end PoincareConjecture.M34
