import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.StandardCircleTriangulation
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimLoop
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryLinks

set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

open Classical in

theorem exists_standard_boundary_circle_surface
    {R S : Set V3} (hR : IsCompact R)
    (he : PLDomain (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph) R)
    (hS : S ⊆ frontier R) (gamma : Q2 ≃ₜ S) (hgamma : gamma.IsFinitePL) :
    ∃ K A L : SimplicialComplex ℝ V3,
      K.faces.Finite ∧ A ≤ K ∧ L ≤ A ∧
      K.space = R ∧ A.space = frontier R ∧ L.space = S ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ A.vertices) → t ∈ A.faces) ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ L.vertices) → t ∈ L.faces) ∧
      (∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph V3 V3,
        B ∈ piecewiseAffineGroupoid V3 ∧ (K.closedStar p).space ⊆ B.source ∧
        (K.closedStar p).AffineOnFaces B ∧
        (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
          ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y))) ∧
      (∀ p ∈ A.vertices, ∃ u : V3 → V2,
        (A.closedFaceStar {p}).AffineOnFaces u ∧
        InjOn u (A.closedFaceStar {p}).space ∧
        u p ∈ interior (u '' (A.closedFaceStar {p}).space)) ∧
      (∀ t ∈ A.faces, ∃ u ∈ A.faces, t ⊆ u ∧ u.card = 3) ∧
      (∀ t ∈ A.faces, t.card = 2 → (A.faceLink t).vertices.ncard = 2) ∧
      ∀ p ∈ A.vertices, IsConnected (A.faceLink {p}).space := by
  classical
  obtain ⟨K, A, L, hK, hAK, hLA, hKs, hAs, hLs, hAfull, hLfull, hstars⟩ :=
    exists_standard_boundary_circle_triangulation hR he hS gamma hgamma
  let base : R := ⟨gamma squareRimBase, he.closed.frontier_subset (hS (gamma squareRimBase).property)⟩
  let g : V3 → R := fun z => if hz : z ∈ R then ⟨z, hz⟩ else base
  have hgv {z : V3} (hz : z ∈ K.space) : (g z : V3) = z := by
    have hzR := hKs ▸ hz
    simp only [g, dif_pos hzR]
  let H : R ≃ₜ K.space := Homeomorph.setCongr hKs.symm
  let HB : A.space ≃ₜ frontier R := Homeomorph.setCongr hAs
  have hg (z : K.space) : (g z : V3) = (H.symm z : V3) := hgv z.property
  have hHB (z : A.space) : (HB z : V3) = (g z : V3) :=
    (hgv (space_subset_of_le hAK z.property)).symm
  have hboundary (z : V3) (hz : z ∈ K.space) :
      (g z : V3) ∈ frontier R ↔ z ∈ A.space := by rw [hgv hz, hAs]
  have hcharts : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph V3 V3,
      MapsTo (fun z => (g z : V3)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) := by
    intro p hp
    obtain ⟨B, _, hsource, hface, hregion⟩ := hstars p hp
    have hstar : (K.closedStar p).space ⊆ K.space := space_subset_of_le
      (fun _ ht => ht.1)
    refine ⟨B, ?_, ?_, hregion⟩
    · intro z hz
      change (g z : V3) ∈ B.source
      rw [hgv (hstar hz)]
      exact hsource hz
    · apply hface.congr
      intro z hz
      change B z = B (g z)
      rw [hgv (hstar hz)]
  have hplanar := original_boundary_faceAffine_vertex_stars K A (hK.subset hAK) hAK g HB hHB hcharts
  obtain ⟨hpure, hedge, hlink⟩ := original_boundary_surface_incidence K A hK hAK
    he.closed.frontier_subset H g hg hboundary hcharts
  exact ⟨K, A, L, hK, hAK, hLA, hKs, hAs, hLs, hAfull, hLfull,
    hstars, hplanar, hpure, hedge, hlink⟩

end PoincareConjecture.M76.Dehn
