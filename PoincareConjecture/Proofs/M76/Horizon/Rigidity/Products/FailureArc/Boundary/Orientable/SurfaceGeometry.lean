import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Boundary.PairedModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Boundary.Orientable.OrientationTransport



set_option autoImplicit false
open Set Metric Geometry AbstractSimplicialComplex
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn

open Poincare.Topology.Orientation.ProjectivePlane

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable {X ι : Type} [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V3}
  {S : SimplicialComplex ℝ (V1 × V2)} {g : (V1 × V2) → X}
  {r : X → ℝ} {C R : Set X} {st : Stage e S g r C} {F : Bool → Set X}

theorem MarkedBoundaryPair.surface_incidence_generic (P : MarkedBoundaryPair st R F) :
    (∀ s ∈ P.model.boundary.faces,
      ∃ t ∈ P.model.boundary.faces, s ⊆ t ∧ t.card = 3) ∧
    (∀ s ∈ P.model.boundary.faces, s.card = 2 →
      (P.model.boundary.faceLink s).vertices.ncard = 2) ∧
    ∀ p ∈ P.model.boundary.vertices, IsConnected (P.model.boundary.faceLink {p}).space :=
  P.model.original_surface_incidence

theorem MarkedBoundaryPair.exists_boundary_signs_of_localOrientation (P : MarkedBoundaryPair st R F) (O : LocalOrientation st.Carrier) :
    ∃ (number : (P.model.sample → ℝ × V3) → ℕ)
      (sign : Finset (P.model.sample → ℝ × V3) → ZMod 2),
      InjOn number P.model.boundary.vertices ∧
      ∀ t ∈ P.model.boundary.faces, t.card = 3 →
        ∀ u ∈ P.model.boundary.faces, u.card = 3 → t ≠ u →
          ∀ s : Finset (P.model.sample → ℝ × V3), s.card = 2 → s ⊆ t → s ⊆ u →
            (sign t + boundaryFaceParity number t s) +
              (sign u + boundaryFaceParity number u s) = 1 :=
  P.model.exists_boundary_signs_of_localOrientation O

noncomputable def MarkedBoundaryPair.boundaryRim_generic (P : MarkedBoundaryPair st R F)
    (b : Bool) : C(Q2, P.model.boundary.space) :=
  (ContinuousMap.inclusion (SimplicialComplex.space_subset_of_le (P.rim_le b))).comp
    (P.parametrization b : C(Q2, (P.rims b).space))

theorem MarkedBoundaryPair.boundaryRim_not_nullhomotopic_generic (P : MarkedBoundaryPair st R F)
    (b : Bool) : ¬ (P.boundaryRim_generic b).Nullhomotopic := by
  intro hn
  exact P.essential b (hn.comp_right P.model.originalProjection)

theorem MarkedBoundaryPair.exists_common_rim_component_of_localOrientation
    (P : MarkedBoundaryPair st R F) (O : LocalOrientation st.Carrier) :
    ∃ C : P.model.boundary.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (∀ b, P.rims b ≤ P.model.boundary.edgeComponentComplex C) ∧
      (P.model.boundary.edgeComponentComplex C).surfaceEulerCount = 0 := by
  classical
  let K := P.model.boundary
  have hK : K.faces.Finite := P.model.finite.subset P.model.boundary_le
  obtain ⟨hpure, hcofaces, hlinks⟩ := P.surface_incidence_generic
  obtain ⟨number, sign, hnumber, hsign⟩ := P.exists_boundary_signs_of_localOrientation O
  obtain ⟨C, hC, hcount⟩ := K.exists_common_component_of_essential_rims hK
    (fun s hs ↦ by obtain ⟨t, ht, hst, hc⟩ := hpure s hs; exact ⟨t, ht, hc, hst⟩)
    (by intro v hv; simpa only [← K.faceLink_singleton_eq_link] using hlinks v hv)
    (by intro s hs hc
        have h := hcofaces s hs hc
        rw [K.ncard_faceLink_vertices_eq_cofaces, hc] at h
        exact h)
    number hnumber sign hsign P.boundaryRim_generic
    P.boundaryRim_not_nullhomotopic_generic P.model.boundary_rank.1
  refine ⟨C, ?_, hcount⟩
  intro b
  apply K.le_of_common_subcomplex_space_subset (P.rims b) (K.edgeComponentComplex C)
    (P.rim_le b) (K.edgeComponentComplex_le C)
  intro x hx
  obtain ⟨u, hu⟩ := (P.parametrization b).surjective ⟨x, hx⟩
  have hv := hC b u
  change (P.parametrization b u : P.model.sample → ℝ × V3) ∈ _ at hv
  simpa only [hu] using hv

end Geometry.OriginalPLTower

