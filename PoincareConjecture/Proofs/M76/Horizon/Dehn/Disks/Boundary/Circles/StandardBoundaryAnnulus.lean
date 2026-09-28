import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.StandardBoundaryBlocks
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.BoundaryCircleAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.OpenMarkedBand

set_option autoImplicit false
open Set Metric Geometry Geometry.SimplicialComplex PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 1 (1 / 8 : ℝ)





theorem exists_standard_boundary_circle_annulus
    {R S : Set V3} (hR : IsCompact R)
    (he : PLDomain (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph) R)
    (hS : S ⊆ frontier R) (gamma : sphere (0 : V2) 1 ≃ₜ S) (hgamma : gamma.IsFinitePL) :
    ∃ (T : Set V3) (c : Ann ≃ₜ T),
      IsCompact T ∧ T ⊆ frontier R ∧ S ⊆ T ∧
      c.IsFinitePL ∧ c.symm.IsFinitePL ∧
      (∀ p : Ann, (c p : V3) ∈ S ↔ depth 1 p = 0) ∧
      ∃ F O U : Set V3, IsOpen U ∧ S ⊆ U ∧ U ∩ frontier R ⊆ T ∧
        IsOpen O ∧ F = frontier R ∩ O ∧ S ⊆ F ∧ F ⊆ T ∧ F ⊆ frontier R ∧
        IsOpen ((Subtype.val : frontier R → V3) ⁻¹' F) ∧
        F = U ∩ ((fun p : Ann => (c p : V3)) ''
          {p | depth 1 p ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8 : ℝ)}) ∧
        ∀ x : T, (x : V3) ∈ F →
          depth 1 (c.symm x) ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8 : ℝ) := by
  classical
  obtain ⟨A, L, hA, hL, n, P, hAs, hLs, hLA, hfull, hPi, _, hPv, _, hPf, hblocks⟩ :=
    exists_standard_boundary_circle_blocks hR he hS gamma hgamma
  let : Fintype A.faces := hA.fintype
  let : Fintype L.faces := hL.fintype
  obtain ⟨⟨D⟩, U, hU, hSU, hUT⟩ := hblocks
  obtain ⟨c, hc, hci, hcore, _⟩ :=
    BoundaryCircleBlockData.exists_annulus hLA hfull hPi hPv hPf D
  let T := (A.barycentricNeighborhood L).space
  have hTc : IsCompact T := (A.barycentricNeighborhood L).isCompact_space_of_finite
    (A.barycentricNeighborhood_finite L)
  have hTB : T ⊆ frontier R := by
    intro x hx
    apply hAs.subset
    exact A.barycentricSubdivision_isSubdivision.space_eq.subset
      (space_subset_of_le (A.barycentricNeighborhood_le L) hx)
  have hST : S ⊆ T := hLs ▸ A.space_subset_barycentricNeighborhood hLA
  have hcore' (p : Ann) : (c p : V3) ∈ S ↔ depth 1 p = 0 := by
    rw [← hLs]
    exact hcore p
  obtain ⟨F, O, hO, hFO, hSF, hFT, hFB, hFopen, hFband, hdepth⟩ :=
    exists_open_marked_annulus_band (by norm_num : (0 : ℝ) < 1 / 8)
      c hTB hST hcore' hU hSU hUT
  exact ⟨T, c, hTc, hTB, hST, hc, hci, hcore', F, O, U, hU, hSU, hUT,
    hO, hFO, hSF, hFT, hFB, hFopen, hFband, hdepth⟩

end PoincareConjecture.M76.Dehn
