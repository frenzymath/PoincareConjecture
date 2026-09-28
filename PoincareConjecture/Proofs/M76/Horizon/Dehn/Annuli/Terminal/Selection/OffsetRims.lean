import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.PairedRimRetraction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.OffsetRimEssentiality
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricNeighborhoodCarrier

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 1 (1 / 8 : ℝ)

variable {L : Submodule ℤ V2} {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  {retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h}
  {d : ProtectedAnnulusTerminalData L retained}

theorem PairedMarkedBoundary.offset_rim_not_disk
    (P : PairedMarkedBoundary L retained d) [Fintype P.model.boundary.faces]
    (b side : Bool)
    (c : Ann ≃ₜ (P.model.boundary.barycentricNeighborhood (P.rims b)).space)
    (hcore : ∀ x : Ann, (c x : P.model.sample → ℝ × V3) ∈ (P.rims b).space ↔
      depth 1 x = 0)
    {B : Set (P.model.sample → ℝ × V3)}
    (hBN : B ⊆ (P.model.boundary.barycentricNeighborhood (P.rims b)).space)
    (hlevel : ∀ x : Ann, (c x : P.model.sample → ℝ × V3) ∈ B ↔
      depth 1 x = if side then (1 / 8 : ℝ) else -(1 / 8 : ℝ))
    {T : Set (P.model.sample → ℝ × V3)} (hTW : T ⊆ P.model.complex.space) :
    ¬ IsFinitePLBallPair (ℝ × ℝ) T B := by
  intro hdisk
  let : Fintype (P.rims b).faces :=
    (P.model.finite.subset ((P.rim_le b).trans P.model.boundary_le)).fintype
  have hSN := P.model.boundary.space_subset_barycentricNeighborhood (P.rim_le b)
  have hNW : (P.model.boundary.barycentricNeighborhood (P.rims b)).space ⊆
      P.model.complex.space := by
    intro x hx
    apply SimplicialComplex.space_subset_of_le P.model.boundary_le
    exact P.model.boundary.barycentricSubdivision_isSubdivision.space_eq.subset
      (SimplicialComplex.space_subset_of_le
        (P.model.boundary.barycentricNeighborhood_le (P.rims b)) hx)
  exact Annuli.offset_rim_not_contained_in_disk c (P.parametrization b) hSN hNW hcore
    side hBN hlevel P.radial (P.radial_parametrization b) hTW hdisk.1 hdisk

open Classical in

theorem PairedMarkedBoundary.offset_rim_count_ne_one
    (P : PairedMarkedBoundary L retained d) [Fintype P.model.boundary.faces]
    (b side : Bool)
    (c : Ann ≃ₜ (P.model.boundary.barycentricNeighborhood (P.rims b)).space)
    (hcore : ∀ x : Ann, (c x : P.model.sample → ℝ × V3) ∈ (P.rims b).space ↔
      depth 1 x = 0)
    (K B : SimplicialComplex ℝ (P.model.sample → ℝ × V3))
    (hBN : B.space ⊆ (P.model.boundary.barycentricNeighborhood (P.rims b)).space)
    (hlevel : ∀ x : Ann, (c x : P.model.sample → ℝ × V3) ∈ B.space ↔
      depth 1 x = if side then (1 / 8 : ℝ) else -(1 / 8 : ℝ))
    (hKW : K.space ⊆ P.model.complex.space) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hconn : IsConnected K.space) (hBK : B ≤ K)
    (gamma : Q2 ≃ₜ B.space) (hgamma : gamma.IsFinitePL)
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset (P.model.sample → ℝ × V3) |
        t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = if s ∈ B.faces then 1 else 2) :
    K.surfaceEulerCount ≠ 1 := by
  have hdec : (fun a b : P.model.sample → ℝ × V3 ↦ Fintype.decidablePiFintype a b) =
      (fun a b ↦ Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  rw [hdec] at hlinks
  intro hcount
  exact P.offset_rim_not_disk b side c hcore hBN hlevel hKW
    (Annuli.isFinitePLBallPair_of_one_boundary_count_one
      K B hK hpure hlinks
      hconn hcount hBK gamma hgamma hboundary)

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
