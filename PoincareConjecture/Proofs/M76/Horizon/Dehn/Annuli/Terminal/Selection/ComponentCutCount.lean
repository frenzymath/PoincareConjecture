import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.Selection.CommonCutCollars
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.Euler.CollarCutCount



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
theorem PairedMarkedBoundary.common_component_cut_surfaceEulerCount
    (P : PairedMarkedBoundary L retained d)
    (C₀ : P.model.boundary.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hrim : ∀ b, P.rims b ≤ P.model.boundary.edgeComponentComplex C₀) :
    letI : Fintype P.model.boundary.faces := (P.model.finite.subset P.model.boundary_le).fintype
    let A := P.model.boundary.edgeComponentComplex C₀
    letI : Fintype A.faces :=
      (P.model.finite.subset ((P.model.boundary.edgeComponentComplex_le C₀).trans
        P.model.boundary_le)).fintype
    let N := A.barycentricNeighborhood P.mark
    let C := A.barycentricSubdivision.closedFaceComplement N
    ∀ (c : ∀ b : Bool, squareAnnulus 1 (1 / 8) ≃ₜ
          (P.model.boundary.barycentricNeighborhood (P.rims b)).space)
      (_ : ∀ b, (c b).IsFinitePL)
      (B : Bool × Bool → SimplicialComplex ℝ (P.model.sample → ℝ × V3))
      (gamma : ∀ i, sphere (0 : V2) 1 ≃ₜ (B i).space)
      (_ : ∀ i, (gamma i).IsFinitePL)
      (_ : Pairwise (fun i j ↦ Disjoint (B i).space (B j).space))
      (_ : ∀ s, s ∈ (N ⊓ C).faces ↔ ∃ i, s ∈ (B i).faces),
      C.surfaceEulerCount = A.surfaceEulerCount := by
  classical
  let : Fintype P.model.boundary.faces := (P.model.finite.subset P.model.boundary_le).fintype
  let A := P.model.boundary.edgeComponentComplex C₀
  let : Fintype A.faces :=
    (P.model.finite.subset ((P.model.boundary.edgeComponentComplex_le C₀).trans
      P.model.boundary_le)).fintype
  let N := A.barycentricNeighborhood P.mark
  dsimp only
  intro c hc B gamma hgamma hBdis hfaces
  have hmark : P.mark ≤ A := by
    intro s hs
    change s ∈ P.mark.faces at hs
    rw [P.mark_faces] at hs
    exact hs.elim (fun hs ↦ hrim false hs) (fun hs ↦ hrim true hs)
  have hN : N = P.model.boundary.barycentricNeighborhood P.mark :=
    P.model.boundary.barycentricNeighborhood_edgeComponent C₀ P.mark hmark
  have hunion : N.faces = ⋃ b : Bool,
      (P.model.boundary.barycentricNeighborhood (P.rims b)).faces := by
    rw [hN, P.derived_collar_union_faces]
    ext s
    simp only [mem_union, mem_iUnion, Bool.exists_bool]
  obtain ⟨hpure, _, _⟩ := P.surface_incidence
  have hdim : ∀ s ∈ A.faces, s.card ≤ 3 := by
    intro s hs
    obtain ⟨t, _, hst, htc⟩ := hpure s hs.1
    exact (Finset.card_le_card hst).trans_eq htc
  have hB : (N ⊓ A.barycentricSubdivision.closedFaceComplement N).faces =
      ⋃ i, (B i).faces := by
    ext s
    rw [hfaces]
    exact mem_iUnion.symm
  exact Annuli.barycentric_collar_cut_surfaceEulerCount A hdim N
    (A.barycentricNeighborhood_le P.mark)
    (fun b ↦ P.model.boundary.barycentricNeighborhood (P.rims b)) hunion
    P.derived_collars_disjoint c hc B hB hBdis gamma hgamma

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
