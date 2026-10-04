import PoincareLib.Topology.Manifold.Smoothing.Dehn.Graphs.Mathlib.BoundaryTopCycleEquiv
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Regions.OriginalBoundaryLinks
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.FaceLinkCofaceCount

/-!
# Top cycles of the entire original frontier

The same original halfspace charts construct every purity, incidence
and full-link hypothesis of the explicit kernel equivalence. No
boundary connectedness or surface supplier is assumed. See Dehn
derivation 018 and PrimeReduction006.
-/

set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]

/-- The literal original frontier charts give the entire top-cycle
and vertex-potential equivalence, including all boundary components.
See Dehn derivation 018. -/
noncomputable def original_boundary_topCycleEquiv
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hAK : A ≤ K)
    [Fintype A.vertices]
    {R : Set X} (hFR : frontier R ⊆ R) (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hboundary : ∀ z ∈ K.space, (g z : X) ∈ frontier R ↔ z ∈ A.space)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y))) :
    LinearMap.ker (vertexCoboundary A.vertexAbstractComplex.toPreAbstractSimplicialComplex)
      ≃ₗ[ZMod 2] LinearMap.ker
        (edgeCoboundary A.vertexAbstractComplex.toPreAbstractSimplicialComplex).dualMap := by
  classical
  have hA : A.faces.Finite := hK.subset hAK
  obtain ⟨hpure, hcounts, hlinks⟩ := original_boundary_surface_incidence
    K A hK hAK hFR H g hg hboundary hstars
  apply A.boundaryTopCycleEquiv hpure
  · intro e
    rw [A.triangleCofaces_card_eq_original e]
    let s : Finset E := e.val.map (Function.Embedding.subtype _)
    have hs : s ∈ A.faces := e.property.1
    have hsc : s.card = 2 := by
      simpa only [s, Finset.card_map] using e.property.2
    have hlink : (A.faceLink s).vertices.ncard =
        {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard := by
      simpa only [hsc] using A.ncard_faceLink_vertices_eq_cofaces s
    exact hlink.symm.trans (hcounts s hs hsc)
  · intro p
    exact ((A.faceLink {p.val}).connected_edgeGraph_of_isConnected
      (SimplicialComplex.finite_faceLink_faces hA _) (hlinks p.val p.property)).preconnected

end PoincareMT.M76
