import PoincareLib.Topology.Manifold.Smoothing.SmoothAtlas.General.FiniteComplexBridge
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.IndependentVertexRealization
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.EmbeddedManifoldConditions
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.EmbeddedStarCharts

/-!+# Smoothing a finite geometric Brouwer triangulation

The original geometric realization need not have globally
independent vertices. Transfer the triangulation to basis vertices,
preserving its stars and links, then apply the checked Cairns
construction. See Cairns 1940, pp. 798--800, 806--807, Hamilton
1976, p. 69 and M76 derivations 78--79.
-/

set_option autoImplicit false

open Set Geometry
open scoped Manifold ContDiff

universe u v

namespace PoincareMT.M76

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- Any finite geometric triangulation with purity, closed link
conditions and affine Brouwer vertex stars supplies the frozen
smoothing conclusion. The original vertex set need not be globally
independent. See Cairns pp. 798--800, 806--807, Hamilton p. 69 and
M76 derivations 78--79. -/
theorem smoothingConclusion_of_finite_geometric_triangulation
    (P : SmoothingBridgeInput (M := M)) (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (hedges : ∀ t ∈ K.faces, t.card = 2 → IsConnected (K.faceLink t).space)
    (htriangles : ∀ t ∈ K.faces, t.card = 3 → (K.faceLink t).vertices.ncard = 2)
    (hbrouwer : ∀ p : E, {p} ∈ K.faces →
      ∃ f : E → EuclideanSpace ℝ (Fin 3),
        (K.closedFaceStar {p}).AffineOnFaces f ∧
        InjOn f (K.closedFaceStar {p}).space ∧
        (interior (f '' (K.closedFaceStar {p}).space)).Nonempty)
    (e : M ≃ₜ K.space) : M76SmoothingConclusion P := by
  classical
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hfinite).fintype
  obtain ⟨f, hf, hinj, hind, _⟩ := K.exists_independent_euclidean_realization
  refine smoothingConclusion_of_finite_brouwer_triangulation P
    (hf.embeddedImage hinj) hind (hf.embeddedImage_finite hinj hfinite)
    (hf.embeddedImage_pure hinj hpure) ?_ ?_ ?_
    (e.trans (hf.embeddedHomeomorph hinj hfinite))
  · intro t ht hcard
    rw [hf.embeddedImage_faces hinj] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    have hc : s.card = 2 :=
      (Finset.card_image_iff.mpr (hinj.mono (K.subset_space hs))).symm.trans hcard
    exact hf.isConnected_embeddedImage_faceLink hinj hfinite hs (hedges s hs hc)
  · intro t ht hcard
    rw [hf.embeddedImage_faces hinj] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    have hc : s.card = 3 :=
      (Finset.card_image_iff.mpr (hinj.mono (K.subset_space hs))).symm.trans hcard
    rw [hf.ncard_embeddedImage_faceLink hinj hs]
    exact htriangles s hs hc
  · intro p hp
    have hp' : p ∈ (hf.embeddedImage hinj).vertices := hp
    rw [hf.embeddedImage_vertices hinj] at hp'
    obtain ⟨q, hq, rfl⟩ := hp'
    obtain ⟨h, hh, hhi, hint⟩ := hbrouwer q hq
    obtain ⟨k, hk, hki, himage⟩ :=
      hf.exists_embeddedImage_closedFaceStar_chart hinj hq hh hhi
    refine ⟨k, ?_, ?_, ?_⟩
    · simpa only [Finset.image_singleton] using hk
    · simpa only [Finset.image_singleton] using hki
    · simp only [Finset.image_singleton] at himage
      rwa [himage]

end PoincareMT.M76
