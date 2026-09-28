import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem EpsilonNeck.isConnected_region (N : EpsilonNeck g) {a b : ℝ}
    (ha : -N.epsilon⁻¹ ≤ a) (hb : b ≤ N.epsilon⁻¹) (hab : a < b) :
    IsConnected (N.region a b) := by
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num))
  have hsub : (univ : Set UnitTwoSphere) ×ˢ Ioo a b ⊆
      univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    rintro ⟨q, t⟩ ⟨hq, ht⟩
    exact ⟨hq, ha.trans_lt ht.1, ht.2.trans_le hb⟩
  have heq : N.coordinate_map '' (univ ×ˢ Ioo a b) = N.region a b := by
    apply Subset.antisymm
    · rintro x ⟨⟨q, t⟩, ht, rfl⟩
      let z : NeckDomain N.epsilon := (q, ⟨t, (hsub ht).2⟩)
      have hz : (N.coordinate z : M) = N.coordinate_map (q, t) := N.coordinate_map_eq z
      have hi := N.coordinate_inverse_left z
      rw [hz] at hi
      exact ⟨hz ▸ (N.coordinate z).property, by simpa [hi] using ht.2⟩
    · intro x hx
      refine ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2⟩, ?_⟩
      have hi := congrArg Subtype.val (N.coordinate_inverse_right x hx.1)
      rwa [N.coordinate_map_eq] at hi
  rw [← heq]
  exact (isConnected_univ.prod (isConnected_Ioo hab)).image _
    (N.coordinate_map_smooth.continuousOn.mono hsub)

end PoincareConjecture
