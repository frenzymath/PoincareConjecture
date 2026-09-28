import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Boundary.Orientable.CommonCutCollars
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.FourCollarRims



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

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

open Classical in
set_option maxHeartbeats 1200000 in



theorem MarkedBoundaryPair.exists_common_component_cut_rims_of_localOrientation
    (P : MarkedBoundaryPair st R F) (O : LocalOrientation st.Carrier) :
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
      IsPreconnected (C.space ∪ ⋃ b,
        (P.model.boundary.barycentricNeighborhood (P.rims b)).space) ∧
      ∃ (c : ∀ b : Bool, squareAnnulus 1 (1 / 8) ≃ₜ
          (P.model.boundary.barycentricNeighborhood (P.rims b)).space)
        (B : Bool × Bool → SimplicialComplex ℝ (P.model.sample → ℝ × V3))
        (gamma : ∀ i, Q2 ≃ₜ (B i).space),
        (∀ b, (c b).IsFinitePL) ∧
        (∀ b x, (c b x : P.model.sample → ℝ × V3) ∈ (P.rims b).space ↔ depth 1 x = 0) ∧
        (∀ b x, (c b x : P.model.sample → ℝ × V3) ∈ C.space ↔
          depth 1 x = -(1 / 8 : ℝ) ∨ depth 1 x = 1 / 8) ∧
        (∀ i, B i ≤ C) ∧ (∀ i, (gamma i).IsFinitePL) ∧
        Pairwise (fun i j ↦ Disjoint (B i).space (B j).space) ∧
        (∀ s, s ∈ (N ⊓ C).faces ↔ ∃ i, s ∈ (B i).faces) ∧
        (∀ s ∈ C.faces, s.card = 2 →
          {t | t ∈ C.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
            if ∃ i, s ∈ (B i).faces then 1 else 2) ∧
        (∀ i, (B i).space ⊆
          (P.model.boundary.barycentricNeighborhood (P.rims i.1)).space) ∧
        ∀ i x, (c i.1 x : P.model.sample → ℝ × V3) ∈ (B i).space ↔
          depth 1 x = if i.2 then (1 / 8 : ℝ) else -(1 / 8 : ℝ) := by
  classical
  let : Fintype P.model.boundary.faces := (P.model.finite.subset P.model.boundary_le).fintype
  obtain ⟨C₀, hzero, hrim, hC, hpure, hlinks, hcofaces, hconn, c, hc, hcore, hcut⟩ :=
    P.exists_common_component_cut_collars_of_localOrientation O
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
  have hboundary : (N ⊓ C).space =
      ((P.model.boundary.barycentricNeighborhood (P.rims false)).space ∪
        (P.model.boundary.barycentricNeighborhood (P.rims true)).space) ∩ C.space := by
    rw [A.derived_cut_boundary_space P.mark]
    change N.space ∩ C.space = _
    rw [hN, (P.model.boundary.barycentricNeighborhood P.mark).space_eq_union_of_faces_eq_union
      _ _ P.derived_collar_union_faces_generic]
  have hfinite : (N ⊓ C).faces.Finite := hC.subset (fun _ hs ↦ hs.2)
  obtain ⟨B, gamma, hBK, hgamma, hdis, hfaces, hBN, hlevel⟩ :=
    Annuli.exists_four_collar_rim_subcomplexes (N ⊓ C) hfinite
      (fun b ↦ (P.model.boundary.barycentricNeighborhood (P.rims b)).space) C.space
      P.derived_collars_disjoint_generic hboundary c hc hcut
  refine ⟨C₀, hzero, hrim, hC, hpure, hlinks, hconn, c, B, gamma,
    hc, hcore, hcut, ?_, hgamma, hdis, hfaces, ?_, hBN, hlevel⟩
  · intro i s hs
    exact (hBK i hs).2
  · intro s hs hsc
    have hm : s ∈ N.faces ↔ ∃ i, s ∈ (B i).faces := by
      rw [← hfaces]
      exact ⟨fun h ↦ ⟨h, hs⟩, fun h ↦ h.1⟩
    rw [hcofaces s hs hsc, hm]
    split_ifs <;> rfl

end Geometry.OriginalPLTower

