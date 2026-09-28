import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.Selection.CommonCutRims
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.Selection.ComponentCutCount
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.Selection.OffsetRims
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.SelectedOverlap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.PairedSurfaceRealization

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1

variable {L : Submodule ℤ V2} {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  {retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h}
  {d : ProtectedAnnulusTerminalData L retained}

set_option maxHeartbeats 1600000 in

theorem PairedMarkedBoundary.exists_boundary_annulus
    (P : PairedMarkedBoundary L retained d) :
    ∃ (T : Set (P.model.sample → ℝ × V3)) (F : Ann ≃ₜ T),
      T ⊆ P.model.boundary.space ∧ F.IsFinitePL ∧
      (∀ b, (P.rims b).space ⊆ T) ∧
      ∀ (b : Bool) (x : Ann),
        depth 8 x = (if b then 1 else -1) ↔
          (F x : P.model.sample → ℝ × V3) ∈ (P.rims b).space := by
  classical
  let : Fintype P.model.boundary.faces := (P.model.finite.subset P.model.boundary_le).fintype
  obtain ⟨C₀, hzero, hrim, hC, hpure, hlinks, hconn, c, B, gamma,
    hc, hcore, hcut, hBK, hgamma, hdis, hfaces, hcofaces, hBN, hlevel⟩ :=
    P.exists_common_component_cut_rims
  let A := P.model.boundary.edgeComponentComplex C₀
  let : Fintype A.faces :=
    (P.model.finite.subset ((P.model.boundary.edgeComponentComplex_le C₀).trans
      P.model.boundary_le)).fintype
  let N := A.barycentricNeighborhood P.mark
  let C := A.barycentricSubdivision.closedFaceComplement N
  let collars := fun b ↦ (P.model.boundary.barycentricNeighborhood (P.rims b)).space
  have hcount : C.surfaceEulerCount = 0 :=
    (P.common_component_cut_surfaceEulerCount C₀ hrim c hc B gamma hgamma hdis hfaces).trans hzero
  have hCboundary : C.space ⊆ P.model.boundary.space := by
    intro x hx
    exact SimplicialComplex.space_subset_of_le (P.model.boundary.edgeComponentComplex_le C₀)
      (A.barycentricSubdivision_isSubdivision.space_eq.subset
        (SimplicialComplex.space_subset_of_le (A.barycentricSubdivision.closedFaceComplement_le N) hx))
  have hNboundary (b : Bool) : collars b ⊆ P.model.boundary.space := by
    intro x hx
    exact P.model.boundary.barycentricSubdivision_isSubdivision.space_eq.subset
      (SimplicialComplex.space_subset_of_le (P.model.boundary.barycentricNeighborhood_le (P.rims b)) hx)
  have hclosed (b : Bool) : IsClosed (collars b) :=
    ((P.model.boundary.barycentricNeighborhood (P.rims b)).isCompact_space_of_finite
      (P.model.boundary.barycentricNeighborhood_finite (P.rims b))).isClosed
  have hnoDisk (i : Bool × Bool) (T : Set (P.model.sample → ℝ × V3))
      (hT : T ⊆ C.space) : ¬ IsFinitePLBallPair (ℝ × ℝ) T (B i).space :=
    P.offset_rim_not_disk i.1 i.2 (c i.1) (hcore i.1) (hBN i) (hlevel i)
      (hT.trans (hCboundary.trans (SimplicialComplex.space_subset_of_le P.model.boundary_le)))
  have hdec : (fun a b : P.model.sample → ℝ × V3 ↦ Fintype.decidablePiFintype a b) =
      (fun a b ↦ Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  change ∀ v ∈ C.vertices, IsConnected (C.link v).space at hlinks
  rw [hdec] at hlinks
  obtain ⟨r, D, s, t, H, hr, hselected, hH, hH0, hH1⟩ :=
    Annuli.exists_selected_cut_annulus C hC hpure hlinks collars hclosed
      P.derived_collars_disjoint hconn c hcut B hBK gamma hgamma hdis hcofaces hlevel
      (by rw [hcount]) hnoDisk
  have hMN (b : Bool) : (P.rims b).space ⊆ collars b := by
    let : Fintype (P.rims b).faces :=
      (P.model.finite.subset ((P.rim_le b).trans P.model.boundary_le)).fintype
    exact P.model.boundary.space_subset_barycentricNeighborhood (P.rim_le b)
  obtain ⟨T, F, hF, hT, hT0, hT1, hF0, hF1⟩ := Annuli.exists_attached_selected_cut_annulus
    C collars (fun b ↦ (P.rims b).space) c hc P.derived_collars_disjoint hMN hcore hcut
    B hBN hlevel r D s t hr hselected H hH hH0 hH1
  refine ⟨T, F, hT.trans ?_, hF, ?_, ?_⟩
  · exact union_subset (union_subset (hNboundary false) hCboundary) (hNboundary true)
  · intro b
    cases b
    · exact hT0
    · exact hT1
  · intro b x
    cases b
    · exact (hF0 x).symm
    · exact (hF1 x).symm

theorem PairedMarkedBoundary.exists_constructed_proper_stage_annulus
    (P : PairedMarkedBoundary L retained d) :
    ∃ k : (V1 × V2) → d.stage.Carrier,
      PolyhedralPLInCharts d.stage.charts k source ∧
      Topology.IsEmbedding (fun x : source ↦ k x) ∧
      MapsTo k source (d.stage.projection ⁻¹' chartDomain L retained) ∧
      (∀ (b : Bool) (u : Q2), k (endpoint b, u) = d.stage.annulusRim d.source_space b u) ∧
      ∀ x : source,
        k x ∈ frontier (d.stage.projection ⁻¹' chartDomain L retained) ↔
          (x : V1 × V2).1 ∈ sphere (0 : V1) 1 := by
  obtain ⟨T, F, hT, hF, hBT, hboundary⟩ := P.exists_boundary_annulus
  exact P.exists_proper_stage_annulus hT hBT F hF hboundary

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
