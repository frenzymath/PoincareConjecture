import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.HamiltonPLGraphEmbedding
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Topology.CompactLocallyPLImage
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The actual finite image of Hamilton's compact PL atlas

The supported overlap supplier produces a finite compatible
atlas, its graph embedding, and an actual finite geometric image
homeomorphic to the original manifold. See Hamilton 1976, p. 69,
Hudson 1969, pp. 12--19 and M76 derivation 258.
-/

set_option autoImplicit false

open Set Geometry Topology

namespace ChartedSpace

variable {M E : Type*} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- Hamilton's local supported straightening supplier gives
an actual finite image complex. Its embedding and chartwise
PL formulas are retained for subsequent local refinement.
See Hamilton p. 69, Hudson pp. 12--19 and derivation 258. -/
theorem exists_finite_geometric_PL_image
    (hlocal : OpenPartialHomeomorph.HasSupportedPLOverlapStraightening
      (M := M) (E := E)) :
    ∃ (s : Finset (OpenPartialHomeomorph M E))
      (F : M → (s → ℝ × E)) (K : SimplicialComplex ℝ (s → ℝ × E)),
      IsClosedEmbedding F ∧ K.faces.Finite ∧ K.space = range F ∧
      (∀ i : s, LocallyPiecewiseAffineOn
        (F ∘ (i : OpenPartialHomeomorph M E).symm)
        (i : OpenPartialHomeomorph M E).target) ∧
      (∀ x : M, ∃ i : s, x ∈ (i : OpenPartialHomeomorph M E).source) ∧
      Nonempty (M ≃ₜ K.space) := by
  classical
  obtain ⟨s, F, hF, hFPL, hcover⟩ := exists_finite_locallyPL_embedding hlocal
  obtain ⟨K, hK, hKs⟩ :=
    OpenPartialHomeomorph.exists_finite_triangulation_range_of_locallyPL
      (fun i : s => (i : OpenPartialHomeomorph M E)) F hF.injective hcover hFPL
  exact ⟨s, F, K, hF, hK, hKs, hFPL, hcover,
    ⟨hF.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hKs.symm)⟩⟩

end ChartedSpace
