import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.Selection.DerivedCollars
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.ClosedComplementUnion
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Boundary.WholeCollarRims

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

theorem PairedMarkedBoundary.derived_collar_union_faces (P : PairedMarkedBoundary L retained d) :
    letI : Fintype P.model.boundary.faces := (P.model.finite.subset P.model.boundary_le).fintype
    (P.model.boundary.barycentricNeighborhood P.mark).faces =
      (P.model.boundary.barycentricNeighborhood (P.rims false)).faces ∪
      (P.model.boundary.barycentricNeighborhood (P.rims true)).faces := by
  classical
  let : Fintype P.model.boundary.faces := (P.model.finite.subset P.model.boundary_le).fintype
  apply P.model.boundary.barycentricNeighborhood_union_faces
    (P.rims false) (P.rims true) P.mark P.mark_vertices ?_ P.disjoint
  intro s hs hv
  exact P.mark_faces.subset (P.mark_full s (P.model.boundary_le hs)
    (fun v hvs ↦ P.mark_vertices.symm.subset (hv v hvs)))

set_option maxHeartbeats 800000 in

theorem PairedMarkedBoundary.exists_derived_annuli_with_cut_rims
    (P : PairedMarkedBoundary L retained d) :
    letI : Fintype P.model.boundary.faces := (P.model.finite.subset P.model.boundary_le).fintype
    ∃ c : ∀ b : Bool, squareAnnulus 1 (1 / 8) ≃ₜ
        (P.model.boundary.barycentricNeighborhood (P.rims b)).space,
      (∀ b, (c b).IsFinitePL) ∧ (∀ b, (c b).symm.IsFinitePL) ∧
      (∀ b x, (c b x : P.model.sample → ℝ × V3) ∈ (P.rims b).space ↔ depth 1 x = 0) ∧
      ∀ b x, (c b x : P.model.sample → ℝ × V3) ∈
          (P.model.boundary.barycentricSubdivision.closedFaceComplement
            (P.model.boundary.barycentricNeighborhood P.mark)).space ↔
        depth 1 x = -(1 / 8 : ℝ) ∨ depth 1 x = 1 / 8 := by
  classical
  let : Fintype P.model.boundary.faces := (P.model.finite.subset P.model.boundary_le).fintype
  obtain ⟨n, p, hpi, hpv, hpf, hD⟩ := P.exists_derived_circle_blocks
  let D := fun b ↦ Classical.choice (hD b)
  obtain ⟨hpure, hcofaces, hlinks⟩ := P.surface_incidence
  have hpure' : ∀ s ∈ P.model.boundary.faces,
      ∃ t ∈ P.model.boundary.faces, t.card = 3 ∧ s ⊆ t := by
    intro s hs
    obtain ⟨t, ht, hst, htc⟩ := hpure s hs
    exact ⟨t, ht, htc, hst⟩
  have hcofaces' : ∀ s ∈ P.model.boundary.faces, s.card = 2 →
      {t | t ∈ P.model.boundary.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2 := by
    intro s hs hsc
    simpa only [SimplicialComplex.ncard_faceLink_vertices_eq_cofaces, hsc] using hcofaces s hs hsc
  have hcard (b : Bool) : ∀ s ∈ (P.rims b).faces, s.card ≤ 2 := by
    intro s hs
    obtain ⟨_, j, hsj⟩ := (hpf b s).mp hs
    exact (Finset.card_le_card hsj).trans Finset.card_le_two
  have hlinks' (b : Bool) : ∀ v ∈ (P.rims b).vertices,
      IsConnected (P.model.boundary.link v).space := by
    intro v hv
    simpa only [SimplicialComplex.faceLink_singleton_eq_link] using hlinks v (P.rim_le b hv)
  have H := fun b ↦ BoundaryCircleBlockData.exists_annulus_with_cut_rims
    (P.rim_le b) hpure' hcofaces' (P.rim_full b) (hcard b)
    (hpi b) (hpv b) (hpf b) (hlinks' b) (D b)
  choose c hc hci hcore hcut using H
  refine ⟨c, hc, hci, hcore, ?_⟩
  intro b x
  rw [← hcut b x]
  cases b
  · exact P.model.boundary.barycentricSubdivision.mem_closedFaceComplement_union_iff
      _ _ _ P.derived_collar_union_faces P.derived_collars_disjoint (c false x).property
  · apply P.model.boundary.barycentricSubdivision.mem_closedFaceComplement_union_iff
      _ _ _ ?_ P.derived_collars_disjoint.symm (c true x).property
    rw [P.derived_collar_union_faces, union_comm]

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
