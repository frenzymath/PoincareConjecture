import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeAffine
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseExtremeLevels

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

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
