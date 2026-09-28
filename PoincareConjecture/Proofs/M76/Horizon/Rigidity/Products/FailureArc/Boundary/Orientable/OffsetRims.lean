import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Boundary.Orientable.SurfaceGeometry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Boundary.OffsetEssentiality
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricNeighborhoodCarrier



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn

open Poincare.Topology.Orientation.ProjectivePlane

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 1 (1 / 8 : ℝ)

variable {X ι : Type} [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V3}
  {S : SimplicialComplex ℝ (V1 × V2)} {g : (V1 × V2) → X}
  {r : X → ℝ} {C R : Set X} {st : Stage e S g r C} {F : Bool → Set X}

theorem MarkedBoundaryPair.offset_rim_not_disk_generic
    (P : MarkedBoundaryPair st R F) [Fintype P.model.boundary.faces]
    (b side : Bool)
    (c : Ann ≃ₜ (P.model.boundary.barycentricNeighborhood (P.rims b)).space)
    (hcore : ∀ x : Ann, (c x : P.model.sample → ℝ × V3) ∈ (P.rims b).space ↔
      depth 1 x = 0)
    {B : Set (P.model.sample → ℝ × V3)}
    (hBN : B ⊆ (P.model.boundary.barycentricNeighborhood (P.rims b)).space)
    (hlevel : ∀ x : Ann, (c x : P.model.sample → ℝ × V3) ∈ B ↔
      depth 1 x = if side then (1 / 8 : ℝ) else -(1 / 8 : ℝ))
    {T : Set (P.model.sample → ℝ × V3)} (hTW : T ⊆ P.model.boundary.space) :
    ¬ IsFinitePLBallPair (ℝ × ℝ) T B := by
  intro hdisk
  let : Fintype (P.rims b).faces :=
    (P.model.finite.subset ((P.rim_le b).trans P.model.boundary_le)).fintype
  have hSN := P.model.boundary.space_subset_barycentricNeighborhood (P.rim_le b)
  have hNW : (P.model.boundary.barycentricNeighborhood (P.rims b)).space ⊆
      P.model.boundary.space := by
    intro x hx
    exact P.model.boundary.barycentricSubdivision_isSubdivision.space_eq.subset
      (SimplicialComplex.space_subset_of_le
        (P.model.boundary.barycentricNeighborhood_le (P.rims b)) hx)
  exact Annuli.offset_rim_not_contained_in_disk_of_essential c (P.parametrization b)
    hSN hNW hcore side hBN hlevel P.model.originalProjection (P.essential b) hTW hdisk.1 hdisk

end Geometry.OriginalPLTower

