import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.TerminalRims
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.EssentialImagePolygon

set_option autoImplicit false

open Set Metric Geometry
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower.MarkedTerminalRegion

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

theorem exists_essential_rim_polygon
    {M ι : Type*} [TopologicalSpace M]
    {e : ι → OpenPartialHomeomorph M V3}
    {S : SimplicialComplex ℝ (V1 × V2)} {g : (V1 × V2) → M}
    {r : M → ℝ} {C R : Set M} {st : Stage e S g r C}
    (N : MarkedTerminalRegion st R) (hS : S.space = ProtectedAnnulus.source)
    (hfront : ∀ (b : Bool) (u : Q2), g (ProtectedAnnulus.endpoint b, u) ∈ frontier R)
    (f : C(ProtectedAnnulus.source, R))
    (hgf : ∀ x : ProtectedAnnulus.source, g x = (f x : M))
    (hessential : ∀ b, ¬ (sourceAnnulusRim f b).Nullhomotopic) (b : Bool) :
    ∃ (n : ℕ) (P : Polygon (N.sample → ℝ × V3) (n + 3))
      (hPB : P.boundary ℝ ⊆ N.boundary.space),
      Function.Injective P ∧ P.HasSimplicialEdges ∧
      P.boundary ℝ ⊆ range (fun u =>
        (N.singularBoundaryRim hS hfront b u : N.sample → ℝ × V3)) ∧
      ¬ (N.originalProjection.comp (ContinuousMap.inclusion hPB)).Nullhomotopic := by
  classical
  let a := N.graph ∘ st.annulusRimMap b
  let Q := squareRimPolygon.simplicialComplex hasSimplicialEdges_squareRimPolygon
  have hQ := squareRimPolygon.finite_simplicialComplex_faces hasSimplicialEdges_squareRimPolygon
  have hQs : Q.space = Q2 :=
    (squareRimPolygon.simplicialComplex_space hasSimplicialEdges_squareRimPolygon).trans
      boundary_squareRimPolygon
  have ha : FinitePiecewiseAffineOn a Q2 := by
    have h := st.annulusRim_polyhedral hS b
    rw [← hQs] at h
    simpa only [hQs] using h.finitePiecewiseAffineOn_comp Q hQ N.graph_PL
  have hAB : a '' Q2 ⊆ N.boundary.space := by
    rintro _ ⟨u, hu, rfl⟩
    exact N.graph_annulusRim_mem_boundary hS hfront b ⟨u, hu⟩
  let j : C(a '' Q2, R) := N.originalProjection.comp (ContinuousMap.inclusion hAB)
  have hj (u : Q2) : j ⟨a u, mem_image_of_mem a u.property⟩ = sourceAnnulusRim f b u := by
    apply Subtype.ext
    exact (N.originalProjection_singularBoundaryRim hS hfront b u).trans
      (hgf ⟨(ProtectedAnnulus.endpoint b, u),
        sphere_subset_closedBall (ProtectedAnnulus.endpoint_mem_sphere b), u.property⟩)
  obtain ⟨n, P, hPA, hinj, hP, hnon⟩ :=
    exists_essential_polygon_in_marked_rim ha (sourceAnnulusRim f b) (hessential b) j hj
  refine ⟨n, P, hPA.trans hAB, hinj, hP, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := hPA hx
    exact ⟨⟨u, hu⟩, rfl⟩
  · have heq : j.comp (ContinuousMap.inclusion hPA) =
        N.originalProjection.comp (ContinuousMap.inclusion (hPA.trans hAB)) := by
      ext x
      rfl
    exact heq ▸ hnon

end Geometry.OriginalPLTower.MarkedTerminalRegion
