import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Coordinates.OpenDomainCoordinates
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth radial coordinates away from zero

Normalize the nonzero vector and retain its radius minus one. The
reconstruction map is a smooth left inverse, so the radial differential
is injective in the actual sphere atlas. This is the radial step of the
RP2 product exclusion in Morgan-Tian Theorem 12.28, pp. 323-324;
see the M34 RP2 product exclusion derivation, section 5.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The normalized vector on the punctured space, with its actual
unit-sphere membership (Theorem 12.28). -/
noncomputable def radialUnitPoint (x : ({0}ᶜ : Set E)) : sphere (0 : E) 1 :=
  ⟨‖(x : E)‖⁻¹ • (x : E), by
    have hx : (x : E) ≠ 0 := x.property
    simp [norm_smul, norm_ne_zero_iff.mpr hx]⟩

/-- Sphere coordinate and radius minus one on the punctured space
(Theorem 12.28). -/
noncomputable def radialSphereCoordinates (x : ({0}ᶜ : Set E)) :
    sphere (0 : E) 1 × ℝ :=
  (radialUnitPoint x, ‖(x : E)‖ - 1)

/-- The actual reconstruction map for the centered radial coordinate
(Theorem 12.28). -/
def radialSphereReconstruct (p : sphere (0 : E) 1 × ℝ) : E :=
  (p.2 + 1) • (p.1 : E)

/-- Reconstruction gives the original included vector (Theorem 12.28). -/
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

/-- The radius is smooth on the actual open nonzero subtype
(Theorem 12.28). -/
theorem contMDiff_radialNorm :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) m (fun x : ({0}ᶜ : Set E) => ‖(x : E)‖) := by
  have hcoe : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) m
      (Subtype.val : ({0}ᶜ : Set E) → E) :=
    contMDiff_isOpenEmbedding isOpen_compl_singleton.isOpenEmbedding_subtypeVal
  intro x
  exact (contDiffAt_norm ℝ (show (x : E) ≠ 0 from x.property)).contMDiffAt.comp x (hcoe x)

/-- Normalization is smooth for the actual sphere charts (Theorem 12.28). -/
theorem contMDiff_radialUnitPoint :
    ContMDiff 𝓘(ℝ, E) (𝓡 n) m (radialUnitPoint (E := E)) := by
  have hcoe : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) m
      (Subtype.val : ({0}ᶜ : Set E) → E) :=
    contMDiff_isOpenEmbedding isOpen_compl_singleton.isOpenEmbedding_subtypeVal
  have hn := contMDiff_radialNorm (E := E) (m := m)
  have hi := hn.inv₀ (fun x => norm_ne_zero_iff.mpr (show (x : E) ≠ 0 from x.property))
  exact (hi.smul hcoe).codRestrict_sphere (fun x => (radialUnitPoint x).property)

/-- Smooth radial sphere and axial coordinates (Theorem 12.28). -/
theorem contMDiff_radialSphereCoordinates :
    ContMDiff 𝓘(ℝ, E) ((𝓡 n).prod 𝓘(ℝ, ℝ)) m
      (radialSphereCoordinates (E := E)) :=
  contMDiff_radialUnitPoint.prodMk (contMDiff_radialNorm.sub contMDiff_const)

omit [Nonempty ({0}ᶜ : Set E)] in
/-- Reconstruction is smooth even beyond the radial coordinate image
(Theorem 12.28). -/
theorem contMDiff_radialSphereReconstruct :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) m
      (radialSphereReconstruct (E := E)) :=
  (contMDiff_snd.add contMDiff_const).smul (contMDiff_coe_sphere.comp contMDiff_fst)

/-- Differentiate the exact left inverse in inclusion coordinates:
the radial differential is injective (Theorem 12.28). -/
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

end PoincareMT.M34
