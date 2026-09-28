import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.PairedRimRetraction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Boundary.CoherentBoundarySigns

set_option autoImplicit false
open Set Metric Geometry AbstractSimplicialComplex

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable {L : Submodule ℤ V2} {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  {retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h}
  {d : ProtectedAnnulusTerminalData L retained}

theorem PairedMarkedBoundary.surface_incidence (P : PairedMarkedBoundary L retained d) :
    (∀ s ∈ P.model.boundary.faces,
      ∃ t ∈ P.model.boundary.faces, s ⊆ t ∧ t.card = 3) ∧
    (∀ s ∈ P.model.boundary.faces, s.card = 2 →
      (P.model.boundary.faceLink s).vertices.ncard = 2) ∧
    ∀ p ∈ P.model.boundary.vertices, IsConnected (P.model.boundary.faceLink {p}).space := by
  classical
  let N := P.model
  apply original_boundary_surface_incidence N.complex N.boundary N.finite N.boundary_le
    N.compact.isClosed.frontier_subset N.homeomorph N.inverse N.inverse_value ?_ ?_
  · intro z hz
    rw [N.boundary_image]
    exact original_model_mem_image_iff N.homeomorph N.graph N.inverse
      N.homeomorph_value N.inverse_value N.compact.isClosed.frontier_subset ⟨z, hz⟩
  · intro p hp
    obtain ⟨B, hB, _, hPL, hregion⟩ := N.stars p hp
    exact ⟨B, hB, hPL, hregion⟩

theorem PairedMarkedBoundary.exists_boundary_signs (P : PairedMarkedBoundary L retained d) :
    ∃ (number : (P.model.sample → ℝ × V3) → ℕ)
      (sign : Finset (P.model.sample → ℝ × V3) → ZMod 2),
      InjOn number P.model.boundary.vertices ∧
      ∀ t ∈ P.model.boundary.faces, t.card = 3 →
        ∀ u ∈ P.model.boundary.faces, u.card = 3 → t ≠ u →
          ∀ s : Finset (P.model.sample → ℝ × V3), s.card = 2 → s ⊆ t → s ⊆ u →
            (sign t + boundaryFaceParity number t s) +
              (sign u + boundaryFaceParity number u s) = 1 := by
  classical
  let N := P.model
  apply d.stage.exists_standard_region_boundary_signs _ N.compact.isClosed
    N.complex N.boundary N.boundary_le (N.finite.subset N.boundary_le)
    N.homeomorph N.graph N.inverse N.homeomorph_value N.inverse_value N.boundary_image ?_
  intro p hp
  obtain ⟨B, hB, hcompat, hPL, hregion⟩ := N.stars p hp
  exact ⟨B, hB, hPL, hcompat, hregion⟩

noncomputable def PairedMarkedBoundary.boundaryRim (P : PairedMarkedBoundary L retained d)
    (b : Bool) : C(Q2, P.model.boundary.space) where
  toFun u := ⟨P.parametrization b u,
    SimplicialComplex.space_subset_of_le (P.rim_le b) (P.parametrization b u).property⟩
  continuous_toFun := (continuous_subtype_val.comp (P.parametrization b).continuous).subtype_mk _

theorem PairedMarkedBoundary.boundary_rim_class_ne_one
    (P : PairedMarkedBoundary L retained d) (b : Bool) :
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map (P.boundaryRim b).continuous)) ≠ 1 := by
  let r : C(P.model.boundary.space, Q2) :=
    ⟨fun z ↦ P.radial ⟨z, SimplicialComplex.space_subset_of_le P.model.boundary_le z.property⟩,
      P.radial.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  exact squareRimLoop_map_class_ne_one_of_retraction (P.boundaryRim b) r
    (P.radial_parametrization b)

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
