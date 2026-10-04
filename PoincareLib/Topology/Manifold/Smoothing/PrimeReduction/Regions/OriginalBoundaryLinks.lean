import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Coordinates.OriginalBoundaryCharts
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineStarPurity
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.AffineStarFacetLinks
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineStarConnectedLinks

/-!
# Surface incidence of the unchanged original boundary

The actual original halfspace charts construct planar chart stars.
Their full images give triangular purity, two triangular cofaces
at every edge and connected vertex links. See PrimeReduction006.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- All local surface incidence is derived on the unchanged
original boundary mark. No surface-chart, purity or link supplier
is assumed. See PrimeReduction006, section3. -/
theorem original_boundary_surface_incidence
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hAK : A ≤ K)
    {R : Set X} (hFR : frontier R ⊆ R) (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hboundary : ∀ z ∈ K.space, (g z : X) ∈ frontier R ↔ z ∈ A.space)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y))) :
    (∀ s ∈ A.faces, ∃ t ∈ A.faces, s ⊆ t ∧ t.card = 3) ∧
      (∀ s ∈ A.faces, s.card = 2 → (A.faceLink s).vertices.ncard = 2) ∧
      ∀ p ∈ A.vertices, IsConnected (A.faceLink {p}).space := by
  obtain ⟨HB, hHB, _⟩ := exists_original_boundary_homeomorph
    (SimplicialComplex.space_subset_of_le hAK) hFR H g hg hboundary
  have hA : A.faces.Finite := hK.subset hAK
  have hplanar := original_boundary_faceAffine_vertex_stars K A hA hAK g HB hHB hstars
  refine ⟨?_, ?_, ?_⟩
  · simpa using A.exists_full_coface_of_faceAffine_vertex_stars hA hplanar
  · intro s hs hscard
    apply A.faceLink_ncard_eq_two_of_faceAffine_vertex_stars hA hplanar s hs
    simpa using hscard
  · intro p hp
    apply A.isConnected_faceLink_of_faceAffine_vertex_stars hA hplanar {p} hp
    simp

end PoincareMT.M76
