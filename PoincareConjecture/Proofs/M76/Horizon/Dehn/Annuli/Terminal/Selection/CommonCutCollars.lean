import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.Selection.EssentialComponent
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.Selection.DerivedCutCollars
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.ComponentRestriction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.DerivedCutSurface

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {L : Submodule ℤ V2} {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  {retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h}
  {d : ProtectedAnnulusTerminalData L retained}

open Classical in
set_option maxHeartbeats 1200000 in

theorem PairedMarkedBoundary.exists_common_component_cut_collars
    (P : PairedMarkedBoundary L retained d) :
    letI : Fintype P.model.boundary.faces := (P.model.finite.subset P.model.boundary_le).fintype
    ∃ C₀ : P.model.boundary.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      let A := P.model.boundary.edgeComponentComplex C₀
      letI : Fintype A.faces :=
        (P.model.finite.subset ((P.model.boundary.edgeComponentComplex_le C₀).trans
          P.model.boundary_le)).fintype
      let N := A.barycentricNeighborhood P.mark
      let C := A.barycentricSubdivision.closedFaceComplement N
      A.surfaceEulerCount = 0 ∧ (∀ b, P.rims b ≤ A) ∧
      C.faces.Finite ∧
      (∀ s ∈ C.faces, ∃ t ∈ C.faces, t.card = 3 ∧ s ⊆ t) ∧
      (∀ v ∈ C.vertices, IsConnected (C.link v).space) ∧
      (∀ s ∈ C.faces, s.card = 2 →
        {t | t ∈ C.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = if s ∈ N.faces then 1 else 2) ∧
      IsPreconnected (C.space ∪ ⋃ b,
        (P.model.boundary.barycentricNeighborhood (P.rims b)).space) ∧
      ∃ c : ∀ b : Bool, squareAnnulus 1 (1 / 8) ≃ₜ
          (P.model.boundary.barycentricNeighborhood (P.rims b)).space,
        (∀ b, (c b).IsFinitePL) ∧
        (∀ b x, (c b x : P.model.sample → ℝ × V3) ∈ (P.rims b).space ↔ depth 1 x = 0) ∧
        ∀ b x, (c b x : P.model.sample → ℝ × V3) ∈ C.space ↔
          depth 1 x = -(1 / 8 : ℝ) ∨ depth 1 x = 1 / 8 := by
  classical
  let : Fintype P.model.boundary.faces := (P.model.finite.subset P.model.boundary_le).fintype
  obtain ⟨C₀, hrim, hzero⟩ := P.exists_common_rim_component
  let A := P.model.boundary.edgeComponentComplex C₀
  let : Fintype A.faces :=
    (P.model.finite.subset ((P.model.boundary.edgeComponentComplex_le C₀).trans
      P.model.boundary_le)).fintype
  let N := A.barycentricNeighborhood P.mark
  let C := A.barycentricSubdivision.closedFaceComplement N
  have hmark : P.mark ≤ A := by
    intro s hs
    change s ∈ P.mark.faces at hs
    rw [P.mark_faces] at hs
    exact hs.elim (fun hs ↦ hrim false hs) (fun hs ↦ hrim true hs)
  have hN : N = P.model.boundary.barycentricNeighborhood P.mark :=
    P.model.boundary.barycentricNeighborhood_edgeComponent C₀ P.mark hmark
  have hNb (b : Bool) : A.barycentricNeighborhood (P.rims b) =
      P.model.boundary.barycentricNeighborhood (P.rims b) :=
    P.model.boundary.barycentricNeighborhood_edgeComponent C₀ (P.rims b) (hrim b)
  obtain ⟨hpure, hcofaces, hlinks⟩ := P.surface_incidence
  have hpureA : ∀ s ∈ A.faces, ∃ t ∈ A.faces, t.card = 3 ∧ s ⊆ t := by
    intro s hs
    obtain ⟨t, ht, hst, hc⟩ := hpure s hs.1
    exact ⟨t, P.model.boundary.edgeComponentComplex_coface C₀ hs ht hst, hc, hst⟩
  have hcofacesA : ∀ s ∈ A.faces, s.card = 2 →
      {t | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2 := by
    intro s hs hsc
    rw [P.model.boundary.edgeComponentComplex_cofaces C₀ hs 3]
    simpa only [SimplicialComplex.ncard_faceLink_vertices_eq_cofaces, hsc] using
      hcofaces s hs.1 hsc
  have hlinksA : ∀ v ∈ A.vertices, IsConnected (A.link v).space := by
    intro v hv
    rw [← A.faceLink_singleton_eq_link,
      P.model.boundary.edgeComponentComplex_vertex_link C₀ hv]
    exact hlinks v hv.1
  obtain ⟨hfinite, hpureC, hlinksC, hcofacesC⟩ :=
    A.derived_closed_cut_surface_incidence P.mark hmark hpureA hcofacesA hlinksA
  have hcover : C.space ∪ (⋃ b,
      (P.model.boundary.barycentricNeighborhood (P.rims b)).space) = A.space := by
    have hc := A.barycentricSubdivision.closedFaceComplement_space_cover N
      (A.barycentricNeighborhood_le P.mark)
    rw [A.barycentricSubdivision_isSubdivision.space_eq] at hc
    rw [hN, (P.model.boundary.barycentricNeighborhood P.mark).space_eq_union_of_faces_eq_union
      _ _ P.derived_collar_union_faces] at hc
    have hu : (⋃ b, (P.model.boundary.barycentricNeighborhood (P.rims b)).space) =
        (P.model.boundary.barycentricNeighborhood (P.rims false)).space ∪
          (P.model.boundary.barycentricNeighborhood (P.rims true)).space := by
      ext x
      simp only [mem_iUnion, Bool.exists_bool, mem_union]
    rw [hu, union_comm]
    simpa only [C, hN] using hc
  obtain ⟨c, hc, _, hcore, hcut⟩ := P.exists_derived_annuli_with_cut_rims
  refine ⟨C₀, hzero, hrim, hfinite, hpureC, hlinksC, hcofacesC, ?_, c, hc, hcore, ?_⟩
  · rw [hcover]
    exact (P.model.boundary.edgeComponentComplex_isPathConnected C₀).isConnected.isPreconnected
  · intro b x
    have hxA : (c b x : P.model.sample → ℝ × V3) ∈ A.space := by
      have hxN : (c b x : P.model.sample → ℝ × V3) ∈
          (A.barycentricNeighborhood (P.rims b)).space := by
        rw [hNb b]
        exact (c b x).property
      have hx := SimplicialComplex.space_subset_of_le (A.barycentricNeighborhood_le (P.rims b)) hxN
      exact A.barycentricSubdivision_isSubdivision.space_eq ▸ hx
    change (c b x : P.model.sample → ℝ × V3) ∈ C.space ↔ _
    rw [P.model.boundary.closed_cut_edgeComponent_space C₀ N, hN, mem_inter_iff]
    exact (and_iff_left hxA).trans (hcut b x)

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
