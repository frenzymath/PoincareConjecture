import PoincareConjecture.Proofs.M76.Dehn.OriginalBoundaryLinkContraction
import PoincareConjecture.Proofs.M76.Dehn.OriginalInteriorLinkSphere









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]




theorem original_chart_stars_vertex_link_models
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (A : SimplicialComplex ℝ E)
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hboundary : ∀ z ∈ K.space, (g z : X) ∈ frontier R ↔ z ∈ A.space)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y))) :
    ∀ p ∈ K.vertices,
      (p ∈ A.space → ContractibleSpace (K.faceLink {p}).space) ∧
      (p ∉ A.space →
        Nonempty ((K.faceLink {p}).space ≃ₜ Metric.sphere (0 : V3) 1)) := by
  intro p hp
  obtain ⟨B, hsource, hface, hregion⟩ := hstars p hp
  constructor
  · intro hpA
    exact contractibleSpace_faceLink_of_original_boundary_chart K hK H g hg hp
      ((hboundary p (K.vertices_subset_space hp)).mpr hpA) B hsource hface hregion
  · intro hpA
    exact exists_faceLink_sphere_homeomorph_of_original_interior_chart K hK H g hg hp
      (fun h => hpA ((hboundary p (K.vertices_subset_space hp)).mp h)) B hsource hface hregion

end PoincareConjecture.M76
