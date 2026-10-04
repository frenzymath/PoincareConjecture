import PoincareLib.Topology.Manifold.Smoothing.Assembly
import PoincareLib.Topology.Manifold.Smoothing.SmoothAtlas.LeafFields.SmoothAtlasOfNormalPosition

/-!
# The smoothing bridge from a finite Brouwer triangulation

Pull the checked smooth carrier atlas back to the original manifold.
This preserves the original topology and universe. The triangulation
and Brouwer-star existence remain explicit hypotheses. See Hamilton
1976, Theorem 2(1), p. 69, Cairns 1940, pp. 806--807 and M76
derivations 02, 72.
-/

set_option autoImplicit false

open Set Geometry
open scoped Manifold ContDiff

universe u v

namespace PoincareMT.M76

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- A finite independent triangulation with the closed-manifold
link conditions and simplexwise affine Brouwer stars supplies the
frozen compatible smoothing conclusion. See Hamilton p. 69, Cairns
pp. 806--807 and M76 derivations 02, 72. -/
theorem smoothingConclusion_of_finite_brouwer_triangulation
    (P : SmoothingBridgeInput (M := M)) (K : SimplicialComplex ℝ E)
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E)) (hfinite : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (hedges : ∀ t ∈ K.faces, t.card = 2 → IsConnected (K.faceLink t).space)
    (htriangles : ∀ t ∈ K.faces, t.card = 3 → (K.faceLink t).vertices.ncard = 2)
    (hbrouwer : ∀ p : E, {p} ∈ K.faces →
      ∃ f : E → EuclideanSpace ℝ (Fin 3),
        (K.closedFaceStar {p}).AffineOnFaces f ∧
        InjOn f (K.closedFaceStar {p}).space ∧
        (interior (f '' (K.closedFaceStar {p}).space)).Nonempty)
    (e : M ≃ₜ K.space) : M76SmoothingConclusion P := by
  obtain ⟨atlas, hatlas⟩ := Smoothing.exists_smooth_atlas_of_brouwerStars
    K hK hfinite hpure hedges htriangles hbrouwer
  let := atlas
  let := hatlas
  apply (smoothingConclusion_iff_exists_atlas P).mpr
  exact ⟨e.pullbackChartedSpace, e.isManifold_pullbackChartedSpace (𝓡 3) ∞⟩

end PoincareMT.M76
