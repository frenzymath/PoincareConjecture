import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AlexanderBaseConeAffine
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.AlexanderBaseExtremeLevels

/-!
# A three-ball filling of the original extreme surface cap

Cone the actual planar section disk to the original extreme
vertex. The boundary is that disk and the complete original
surface sublevel, as identified from its original triangles.
See Alexander 1924, p. 7 and M76 derivation 248.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An actual planar disk filling the first regular section
cones to a finite PL three-ball whose boundary is exactly the
disk and the original entire low surface cap. All ball data is
constructed from the disk. See Alexander p. 7 and derivation
248. -/
theorem extreme_vertex_cap_ball (K : SimplicialComplex ℝ E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hqK : q ∈ K.vertices) (hAq : A q = 0)
    {β : ℝ} (hβ : 0 < β) (hgap : ∀ v ∈ K.vertices, v ≠ q → β < A v)
    {d : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d (K.space ∩ {x | A x = β}))
    (hAd : ∀ x ∈ d, A x = β) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (convexJoin ℝ {q} d)
      (d ∪ (K.space ∩ {x | A x ≤ β})) := by
  have h := hd.convexJoin_of_affine_level A q (by rw [hAq]; exact hβ.ne) hAd
  rwa [← K.extreme_vertex_sublevel_eq_convexJoin hpure A hqK hAq hβ hgap] at h

end Geometry.SimplicialComplex
