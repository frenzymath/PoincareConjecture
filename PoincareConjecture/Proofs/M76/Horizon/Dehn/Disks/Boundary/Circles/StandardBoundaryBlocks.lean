import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.CyclicStripBlocks
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.StandardCircleOrder
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.StandardSurfaceGeometry
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.GeometricCofaceSigns

set_option autoImplicit false
open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

open Classical in

theorem exists_standard_boundary_circle_blocks
    {R S : Set V3} (hR : IsCompact R)
    (he : PLDomain (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph) R)
    (hS : S ⊆ frontier R) (gamma : sphere (0 : V2) 1 ≃ₜ S) (hgamma : gamma.IsFinitePL) :
    ∃ (A L : SimplicialComplex ℝ V3) (hA : A.faces.Finite) (_hL : L.faces.Finite)
      (n : ℕ) (P : Polygon V3 (n + 3)),
      A.space = frontier R ∧ L.space = S ∧ L ≤ A ∧
      (∀ t ∈ A.faces, (∀ v ∈ t, v ∈ L.vertices) → t ∈ L.faces) ∧
      Function.Injective P ∧ P.HasSimplicialEdges ∧ range P = L.vertices ∧
      P.boundary ℝ = L.space ∧
      (∀ s : Finset V3, s ∈ L.faces ↔ s.Nonempty ∧
        ∃ j : Fin (n + 3), s ⊆ {P j, P (finRotate (n + 3) j)}) ∧
      (letI : Fintype A.faces := hA.fintype
       Nonempty (BoundaryCircleBlockData A L P) ∧
         ∃ U : Set V3, IsOpen U ∧ S ⊆ U ∧
           U ∩ frontier R ⊆ (A.barycentricNeighborhood L).space) := by
  classical
  obtain ⟨K, A, L, hK, hAK, hLA, _, hAs, hLs, _, hfull, hstars, _, hpure, hedge, hlinks⟩ :=
    exists_standard_boundary_circle_surface hR he hS gamma hgamma
  have hA : A.faces.Finite := hK.subset hAK
  have hL : L.faces.Finite := hA.subset hLA
  let : Fintype A.faces := hA.fintype
  let : Fintype L.faces := hL.fintype
  obtain ⟨number, sign, hnumber, hcancel⟩ := exists_standard_frontier_geometric_coface_signs
    K A hAK hA R hAs.subset hstars
  obtain ⟨hLcard, n, P, hPi, hP, hPv, hPs, hPf, _⟩ :=
    exists_original_boundary_circle_order gamma hgamma L hL hLs
  have hpure' (s : Finset V3) (hs : s ∈ A.faces) :
      ∃ t ∈ A.faces, t.card = 3 ∧ s ⊆ t := by
    obtain ⟨t, ht, hst, htc⟩ := hpure s hs
    exact ⟨t, ht, htc, hst⟩
  have hcofaces (s : Finset V3) (hs : s ∈ A.faces) (hsc : s.card = 2) :
      {t : Finset V3 | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2 := by
    have h := hedge s hs hsc
    simpa only [A.ncard_faceLink_vertices_eq_cofaces, hsc] using h
  have hfull' (t : Finset V3) (ht : t ∈ A.faces) (hv : ∀ v ∈ t, v ∈ L.vertices) :
      t ∈ L.faces := hfull t (hAK ht) hv
  have hlinks' (v : V3) (hv : v ∈ L.vertices) : IsConnected (A.link v).space := by
    simpa only [A.faceLink_singleton_eq_link] using hlinks v (hLA hv)
  refine ⟨A, L, hA, hL, n, P, hAs, hLs, hLA, hfull', hPi, hP, hPv, hPs, hPf,
    exists_boundary_circle_blocks A L hLA hpure' hcofaces hfull' hLcard hlinks'
      number sign hnumber hcancel P hPi hPv hPf, ?_⟩
  obtain ⟨U, hU, hLU, hUA⟩ := A.exists_open_barycentricNeighborhood hLA
  exact ⟨U, hU, hLs ▸ hLU, hAs ▸ hUA⟩

end PoincareConjecture.M76.Dehn
