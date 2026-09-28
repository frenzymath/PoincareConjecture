import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.EssentialAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.TerminalRegion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.EssentialBoundaryComponent

set_option autoImplicit false

open Set Metric Geometry
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower.MarkedTerminalRegion

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ (V1 × V2)} {g : (V1 × V2) → M}
  {r : M → ℝ} {C R : Set M} {st : Stage e S g r C}

def originalProjection (P : MarkedTerminalRegion st R) : C(P.boundary.space, R) where
  toFun z := ⟨st.projection (P.homeomorph.symm
    ⟨z, SimplicialComplex.space_subset_of_le P.boundary_le z.property⟩),
    P.projection_subset (P.homeomorph.symm _).property⟩
  continuous_toFun :=
    (st.projection.continuous.comp (continuous_subtype_val.comp
      (P.homeomorph.symm.continuous.comp (continuous_subtype_val.subtype_mk _)))).subtype_mk _

theorem graph_annulusRim_mem_boundary (P : MarkedTerminalRegion st R)
    (hS : S.space = ProtectedAnnulus.source)
    (hfront : ∀ (b : Bool) (u : Q2), g (ProtectedAnnulus.endpoint b, u) ∈ frontier R)
    (b : Bool) (u : Q2) : P.graph (st.annulusRim hS b u) ∈ P.boundary.space := by
  rw [P.boundary_image]
  refine ⟨st.annulusRim hS b u, ?_, rfl⟩
  exact P.source_frontier (ProtectedAnnulus.endpoint b, u)
    (hS.symm.subset ⟨sphere_subset_closedBall (ProtectedAnnulus.endpoint_mem_sphere b),
      u.property⟩) (hfront b u)

noncomputable def singularBoundaryRim (P : MarkedTerminalRegion st R)
    (hS : S.space = ProtectedAnnulus.source)
    (hfront : ∀ (b : Bool) (u : Q2), g (ProtectedAnnulus.endpoint b, u) ∈ frontier R)
    (b : Bool) : C(Q2, P.boundary.space) where
  toFun u := ⟨P.graph (st.annulusRim hS b u), P.graph_annulusRim_mem_boundary hS hfront b u⟩
  continuous_toFun := (P.graph_continuous.comp (st.annulusRim hS b).continuous).subtype_mk _

theorem originalProjection_singularBoundaryRim (P : MarkedTerminalRegion st R)
    (hS : S.space = ProtectedAnnulus.source)
    (hfront : ∀ (b : Bool) (u : Q2), g (ProtectedAnnulus.endpoint b, u) ∈ frontier R)
    (b : Bool) (u : Q2) :
    (P.originalProjection (P.singularBoundaryRim hS hfront b u) : M) =
      g (ProtectedAnnulus.endpoint b, u) := by
  let x : P.region := ⟨st.annulusRim hS b u,
    P.source_subset (st.annulusRim_range_subset hS b (mem_range_self u))⟩
  have heq : (⟨P.singularBoundaryRim hS hfront b u,
      SimplicialComplex.space_subset_of_le P.boundary_le
        (P.singularBoundaryRim hS hfront b u).property⟩ : P.complex.space) =
      P.homeomorph x := Subtype.ext (P.homeomorph_value x).symm
  change st.projection (P.homeomorph.symm _) = _
  rw [heq, P.homeomorph.symm_apply_apply]
  exact st.annulusRim_projection hS b u

theorem singularBoundaryRim_not_nullhomotopic (P : MarkedTerminalRegion st R)
    (hS : S.space = ProtectedAnnulus.source)
    (hfront : ∀ (b : Bool) (u : Q2), g (ProtectedAnnulus.endpoint b, u) ∈ frontier R)
    (f : C(ProtectedAnnulus.source, R))
    (hgf : ∀ x : ProtectedAnnulus.source, g x = (f x : M))
    (hessential : ∀ b, ¬ (sourceAnnulusRim f b).Nullhomotopic) (b : Bool) :
    ¬ (P.singularBoundaryRim hS hfront b).Nullhomotopic := by
  intro hn
  have heq : P.originalProjection.comp (P.singularBoundaryRim hS hfront b) =
      sourceAnnulusRim f b := by
    apply ContinuousMap.ext
    intro u
    apply Subtype.ext
    exact (P.originalProjection_singularBoundaryRim hS hfront b u).trans
      (hgf ⟨(ProtectedAnnulus.endpoint b, u),
        sphere_subset_closedBall (ProtectedAnnulus.endpoint_mem_sphere b), u.property⟩)
  exact hessential b (heq ▸ hn.comp_right P.originalProjection)

theorem singularBoundaryRim_ranges_disjoint (P : MarkedTerminalRegion st R)
    (hS : S.space = ProtectedAnnulus.source)
    (hfront : ∀ (b : Bool) (u : Q2), g (ProtectedAnnulus.endpoint b, u) ∈ frontier R)
    (F : Bool → Set M) (hF : Disjoint (F false) (F true))
    (hmark : ∀ (b : Bool) (u : Q2), g (ProtectedAnnulus.endpoint b, u) ∈ F b) :
    Disjoint (range (P.singularBoundaryRim hS hfront false))
      (range (P.singularBoundaryRim hS hfront true)) := by
  apply disjoint_left.mpr
  rintro x ⟨u, rfl⟩ ⟨v, hv⟩
  have hp := congrArg (fun z => (P.originalProjection z : M)) hv
  rw [P.originalProjection_singularBoundaryRim,
    P.originalProjection_singularBoundaryRim] at hp
  exact disjoint_left.mp hF (hmark false u) (hp ▸ hmark true v)

theorem original_surface_incidence (P : MarkedTerminalRegion st R) :
    (∀ s ∈ P.boundary.faces, ∃ t ∈ P.boundary.faces, s ⊆ t ∧ t.card = 3) ∧
    (∀ s ∈ P.boundary.faces, s.card = 2 → (P.boundary.faceLink s).vertices.ncard = 2) ∧
    ∀ p ∈ P.boundary.vertices, IsConnected (P.boundary.faceLink {p}).space := by
  classical
  apply original_boundary_surface_incidence P.complex P.boundary P.finite P.boundary_le
    P.compact.isClosed.frontier_subset P.homeomorph P.inverse P.inverse_value ?_ ?_
  · intro z hz
    rw [P.boundary_image]
    exact original_model_mem_image_iff P.homeomorph P.graph P.inverse
      P.homeomorph_value P.inverse_value P.compact.isClosed.frontier_subset ⟨z, hz⟩
  · intro p hp
    obtain ⟨B, hB, _, hPL, hregion⟩ := P.stars p hp
    exact ⟨B, hB, hPL, hregion⟩

end Geometry.OriginalPLTower.MarkedTerminalRegion
