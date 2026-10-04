import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.OriginalVertexLinkModels
import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.CocycleExactnessOfContractions

/-!
# Exact original edge incidence on every complete vertex link

The actual original chart-star models produce the contraction or
sphere needed to trivialize the constructed cocycle obstruction. All
cochains keep the original link vertices and actual edge/triangle
incidence. See Hatcher pp. 60, 68--70, 105 and Dehn derivation 015.
-/

set_option autoImplicit false

open Set Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]

/-- Every original vertex link has literal degree-one cochain
exactness, derived from the unchanged original model and chart stars.
The finite enumeration is of its actual retained vertices.
See Dehn derivation 015. -/
theorem original_chart_stars_vertex_link_edge_exact
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (A : SimplicialComplex ℝ E)
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hboundary : ∀ z ∈ K.space, (g z : X) ∈ frontier R ↔ z ∈ A.space)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)))
    {p : E} (hp : p ∈ K.vertices) [Fintype (K.faceLink {p}).vertices] :
    LinearMap.ker
        (edgeCoboundary (K.faceLink {p}).vertexAbstractComplex.toPreAbstractSimplicialComplex) =
      LinearMap.range
        (vertexCoboundary
          (K.faceLink {p}).vertexAbstractComplex.toPreAbstractSimplicialComplex) := by
  classical
  have hmodels := original_chart_stars_vertex_link_models K hK A H g hg hboundary hstars p hp
  by_cases hpA : p ∈ A.space
  · let : ContractibleSpace (K.faceLink {p}).space := hmodels.1 hpA
    exact (K.faceLink {p}).edge_exact_of_contractible
  · obtain ⟨hmodel⟩ := hmodels.2 hpA
    let : SimplyConnectedSpace (Metric.sphere (0 : V3) 1) :=
      unitThreeSphere_lifting_properties.1
    let : LocallyPathConnectedSpace (Metric.sphere (0 : V3) 1) :=
      unitThreeSphere_lifting_properties.2
    let : SimplyConnectedSpace (K.faceLink {p}).space :=
      hmodel.toHomotopyEquiv.simplyConnectedSpace
    let : LocallyPathConnectedSpace (K.faceLink {p}).space :=
      hmodel.isOpenEmbedding.locallyPathConnectedSpace
    exact (K.faceLink {p}).edge_exact_of_simplyConnected

end PoincareMT.M76
