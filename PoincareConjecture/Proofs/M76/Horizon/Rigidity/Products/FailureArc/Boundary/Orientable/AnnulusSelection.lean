import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Boundary.Orientable.CommonCutRims
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Boundary.Orientable.ComponentCutCount
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Boundary.Orientable.OffsetRims
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.SelectedOverlap



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

open PoincareConjecture.M76 PoincareConjecture.M76.Dehn

open Poincare.Topology.Orientation.ProjectivePlane

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1


variable {X ι : Type} [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V3}
  {S : SimplicialComplex ℝ (V1 × V2)} {g : (V1 × V2) → X}
  {r : X → ℝ} {C R : Set X} {st : Stage e S g r C} {F : Bool → Set X}

set_option maxHeartbeats 1600000 in



theorem MarkedBoundaryPair.exists_boundary_annulus_of_localOrientation
    (P : MarkedBoundaryPair st R F) (O : LocalOrientation st.Carrier) :
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
    P.exists_common_component_cut_rims_of_localOrientation O
  let A := P.model.boundary.edgeComponentComplex C₀
  let : Fintype A.faces :=
    (P.model.finite.subset ((P.model.boundary.edgeComponentComplex_le C₀).trans
      P.model.boundary_le)).fintype
  let N := A.barycentricNeighborhood P.mark
  let C := A.barycentricSubdivision.closedFaceComplement N
  let collars := fun b ↦ (P.model.boundary.barycentricNeighborhood (P.rims b)).space
  have hcount : C.surfaceEulerCount = 0 :=
    (P.common_component_cut_surfaceEulerCount_generic C₀ hrim c hc B gamma hgamma hdis hfaces).trans hzero
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
    P.offset_rim_not_disk_generic i.1 i.2 (c i.1) (hcore i.1) (hBN i) (hlevel i)
      (hT.trans hCboundary)
  have hdec : (fun a b : P.model.sample → ℝ × V3 ↦ Fintype.decidablePiFintype a b) =
      (fun a b ↦ Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  change ∀ v ∈ C.vertices, IsConnected (C.link v).space at hlinks
  rw [hdec] at hlinks
  obtain ⟨r, D, s, t, H, hr, hselected, hH, hH0, hH1⟩ :=
    Annuli.exists_selected_cut_annulus C hC hpure hlinks collars hclosed
      P.derived_collars_disjoint_generic hconn c hcut B hBK gamma hgamma hdis hcofaces hlevel
      (by rw [hcount]) hnoDisk
  have hMN (b : Bool) : (P.rims b).space ⊆ collars b := by
    let : Fintype (P.rims b).faces :=
      (P.model.finite.subset ((P.rim_le b).trans P.model.boundary_le)).fintype
    exact P.model.boundary.space_subset_barycentricNeighborhood (P.rim_le b)
  obtain ⟨T, F, hF, hT, hT0, hT1, hF0, hF1⟩ := Annuli.exists_attached_selected_cut_annulus
    C collars (fun b ↦ (P.rims b).space) c hc P.derived_collars_disjoint_generic hMN hcore hcut
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

end Geometry.OriginalPLTower

