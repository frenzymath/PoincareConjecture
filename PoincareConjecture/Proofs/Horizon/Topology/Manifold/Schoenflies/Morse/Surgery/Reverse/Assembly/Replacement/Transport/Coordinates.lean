import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Belt
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.PlaneLift



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Reverse

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

def modelCapCoordinates {v : E3} (hv : ‖v‖ = 1) :
    Diffeomorph 𝓘(Real, Hemisphere.Plane v × Real) (𝓡 3)
      (Hemisphere.Plane v × Real) E3 ∞ :=
  ((ContinuousLinearEquiv.prodComm Real (Hemisphere.Plane v) Real).trans
    (heightCoordinates hv)).toDiffeomorph

@[simp] theorem modelCapCoordinates_apply {v : E3} (hv : ‖v‖ = 1)
    (p : Hemisphere.Plane v × Real) :
    modelCapCoordinates hv p = p.2 • v + (p.1 : E3) := rfl

@[simp] theorem inner_modelCapCoordinates {v : E3} (hv : ‖v‖ = 1)
    (p : Hemisphere.Plane v × Real) : inner Real v (modelCapCoordinates hv p) = p.2 :=
  inner_heightCoordinates hv _

@[simp] theorem projection_modelCapCoordinates {v : E3} (hv : ‖v‖ = 1)
    (p : Hemisphere.Plane v × Real) :
    (Hemisphere.Plane v).orthogonalProjectionOnto (modelCapCoordinates hv p) = p.1 := by
  rw [modelCapCoordinates_apply]
  simp

def normalizedModelCap {v : E3} (hv : ‖v‖ = 1) : Set (Hemisphere.Plane v × Real) :=
  modelCapCoordinates hv ⁻¹' boundedCylinderNorthernCap v

theorem isCompact_normalizedModelCap {v : E3} (hv : ‖v‖ = 1) :
    IsCompact (normalizedModelCap hv) := by
  have hN : IsCompact (boundedCylinderNorthernCap v) := by
    apply IsCompact.image
      ((isClosed_le continuous_const ((innerSL Real v).continuous.comp continuous_subtype_val)).isCompact)
    exact (contMDiff_boundedCylinderRadius v).continuous.smul continuous_subtype_val
  have heq : normalizedModelCap hv = (modelCapCoordinates hv).symm '' boundedCylinderNorthernCap v :=
    ((modelCapCoordinates hv).toEquiv.image_symm_eq_preimage _).symm
  rw [heq]
  exact hN.image (modelCapCoordinates hv).symm.continuous

theorem normalizedModelCap_bounds {v : E3} (hv : ‖v‖ = 1)
    {p : Hemisphere.Plane v × Real} (hp : p ∈ normalizedModelCap hv) :
    0 ≤ p.2 ∧ p.2 ≤ 2 ∧ ‖p.1‖ ≤ 1 := by
  have hmem : modelCapCoordinates hv p ∈ boundedCylinderNorthernCap v := hp
  have hnonneg := height_nonneg_of_mem_boundedCylinderNorthernCap hmem
  rw [inner_modelCapCoordinates] at hnonneg
  obtain ⟨q, _, hq⟩ := hmem
  dsimp only at hq
  have hheight := abs_boundedCylinder_height_le v hv q
  rw [hq, inner_modelCapCoordinates] at hheight
  have hproj := norm_boundedCylinder_projection_le v hv q
  rw [hq, projection_modelCapCoordinates] at hproj
  exact ⟨hnonneg, (abs_le.mp hheight).2, hproj⟩

theorem mem_normalizedModelCap_belt {v : E3} (hv : ‖v‖ = 1)
    (x : Hemisphere.Plane v) {z : Real} (hz : z ∈ Icc (0 : Real) (1 / 4)) :
    (x, z) ∈ normalizedModelCap hv ↔ x ∈ sphere (0 : Hemisphere.Plane v) 1 := by
  change modelCapCoordinates hv (x, z) ∈ boundedCylinderNorthernCap v ↔ _
  rw [mem_boundedCylinderNorthernCap_iff_of_height_lt_one hv
    (by rw [inner_modelCapCoordinates]; linarith [hz.2]),
    inner_modelCapCoordinates, projection_modelCapCoordinates, mem_sphere_zero_iff_norm]
  exact and_iff_right hz.1

def scaledCapCoordinates {v : E3} (hv : ‖v‖ = 1) (b s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) :=
  (modelCapCoordinates hv).trans (liftPlaneDiffeomorph hv b s hs A)

@[simp] theorem scaledCapCoordinates_apply {v : E3} (hv : ‖v‖ = 1) (b s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) (p : Hemisphere.Plane v × Real) :
    scaledCapCoordinates hv b s hs A p = (b + s * p.2) • v + (A p.1 : E3) := by
  change liftPlaneDiffeomorph hv b s hs A (modelCapCoordinates hv p) = _
  rw [liftPlaneDiffeomorph_apply, inner_modelCapCoordinates, projection_modelCapCoordinates]

@[simp] theorem inner_scaledCapCoordinates {v : E3} (hv : ‖v‖ = 1) (b s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) (p : Hemisphere.Plane v × Real) :
    inner Real v (scaledCapCoordinates hv b s hs A p) = b + s * p.2 := by
  change inner Real v (liftPlaneDiffeomorph hv b s hs A (modelCapCoordinates hv p)) = _
  rw [inner_liftPlaneDiffeomorph, inner_modelCapCoordinates]

@[simp] theorem projection_scaledCapCoordinates {v : E3} (hv : ‖v‖ = 1)
    (b s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) (p : Hemisphere.Plane v × Real) :
    (Hemisphere.Plane v).orthogonalProjectionOnto (scaledCapCoordinates hv b s hs A p) = A p.1 := by
  change (Hemisphere.Plane v).orthogonalProjectionOnto
    (liftPlaneDiffeomorph hv b s hs A (modelCapCoordinates hv p)) = _
  rw [projection_liftPlaneDiffeomorph, projection_modelCapCoordinates]

theorem image_normalizedModelCap {v : E3} (hv : ‖v‖ = 1) (b s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) :
    scaledCapCoordinates hv b s hs A '' normalizedModelCap hv =
      liftPlaneDiffeomorph hv b s hs A '' boundedCylinderNorthernCap v := by
  change (liftPlaneDiffeomorph hv b s hs A ∘ modelCapCoordinates hv) ''
    (modelCapCoordinates hv ⁻¹' boundedCylinderNorthernCap v) = _
  have hsurj : Surjective (modelCapCoordinates hv : Hemisphere.Plane v × Real -> E3) :=
    (modelCapCoordinates hv).surjective
  rw [image_comp, hsurj.image_preimage]

end Poincare.Manifold.Schoenflies.Reverse
