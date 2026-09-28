import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.PairedBoundaryGeometry
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.CommonEssentialComponent

set_option autoImplicit false
open Set Metric Geometry

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

open Classical in
theorem PairedMarkedBoundary.exists_common_rim_component
    (P : PairedMarkedBoundary L retained d) :
    ∃ C : P.model.boundary.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (∀ b, P.rims b ≤ P.model.boundary.edgeComponentComplex C) ∧
      (P.model.boundary.edgeComponentComplex C).surfaceEulerCount = 0 := by
  classical
  let K := P.model.boundary
  have hK : K.faces.Finite := P.model.finite.subset P.model.boundary_le
  obtain ⟨hpure, hcofaces, hlinks⟩ := P.surface_incidence
  obtain ⟨number, sign, hnumber, hsign⟩ := P.exists_boundary_signs
  let radial : C(K.space, Q2) :=
    ⟨fun x ↦ P.radial ⟨x,
      SimplicialComplex.space_subset_of_le P.model.boundary_le x.property⟩,
      P.radial.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  obtain ⟨C, hC, hcount⟩ := K.exists_common_essential_rim_component hK
    (fun s hs ↦ by obtain ⟨t, ht, hst, hc⟩ := hpure s hs; exact ⟨t, ht, hc, hst⟩)
    (by intro v hv; simpa only [← K.faceLink_singleton_eq_link] using hlinks v hv)
    (by intro s hs hc
        have h := hcofaces s hs hc
        rw [K.ncard_faceLink_vertices_eq_cofaces, hc] at h
        exact h)
    number hnumber sign hsign P.boundaryRim radial
    P.radial_parametrization P.model.boundary_rank.1
  refine ⟨C, ?_, hcount⟩
  intro b
  apply K.le_of_common_subcomplex_space_subset (P.rims b) (K.edgeComponentComplex C)
    (P.rim_le b) (K.edgeComponentComplex_le C)
  intro x hx
  obtain ⟨u, hu⟩ := (P.parametrization b).surjective ⟨x, hx⟩
  have hv := hC b u
  change (P.parametrization b u : P.model.sample → ℝ × V3) ∈ _ at hv
  simpa only [hu] using hv

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
