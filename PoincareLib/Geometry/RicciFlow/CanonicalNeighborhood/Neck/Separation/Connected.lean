import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Connected sets in the two halves of a neck

The coordinate central sphere is connected, and any connected subset of the
neck which avoids that sphere stays on one side. These assertions concern
the actual cylinder carrier; they do not assert ambient separation.

Reference: Morgan--Tian, Lemma 2.20, pp. 31--32.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

private instance : ConnectedSpace UnitTwoSphere := by
  apply isConnected_iff_connectedSpace.mp
  exact isConnected_sphere
    (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)

/-- The central sphere of an actual neck is connected. -/
theorem isConnected_central_sphere : IsConnected N.central_sphere := by
  rw [N.central_sphere_eq]
  apply (isConnected_univ.prod (isConnected_singleton : IsConnected ({0} : Set ℝ))).image
  apply N.coordinate_map_smooth.continuousOn.mono
  rintro ⟨q, s⟩ ⟨_, hs⟩
  have hs0 : s = 0 := hs
  subst s
  exact ⟨Set.mem_univ _, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos),
    inv_pos.mpr N.epsilon_pos⟩

/-- The whole open neck carrier is connected. -/
theorem isConnected_carrier : IsConnected N.carrier := by
  have heq : N.coordinate_map ''
      (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) = N.carrier := by
    apply Subset.antisymm
    · rintro x ⟨⟨q, t⟩, ht, rfl⟩
      have h := (N.coordinate (q, ⟨t, ht.2⟩)).property
      rwa [N.coordinate_map_eq] at h
    · intro x hx
      refine ⟨N.coordinate_inverse x, N.coordinate_inverse_mem x hx, ?_⟩
      have h := congrArg Subtype.val (N.coordinate_inverse_right x hx)
      rwa [N.coordinate_map_eq] at h
  rw [← heq]
  apply (isConnected_univ.prod
    (isConnected_Ioo (show -N.epsilon⁻¹ < N.epsilon⁻¹ by
      have h := inv_pos.mpr N.epsilon_pos
      linarith))).image
  exact N.coordinate_map_smooth.continuousOn

/-- A connected set contained in the neck and avoiding its central sphere is
contained wholly in one of the two coordinate halves. -/
theorem subset_one_side_of_isPreconnected {S : Set M} (hS : IsPreconnected S)
    (hcarrier : S ⊆ N.carrier) (havoid : Disjoint S N.central_sphere) :
    S ⊆ N.region (-N.epsilon⁻¹) 0 ∨ S ⊆ N.region 0 N.epsilon⁻¹ := by
  apply hS.subset_or_subset (N.isOpen_region _ _) (N.isOpen_region _ _)
    (N.region_disjoint_of_le le_rfl)
  intro x hx
  rcases N.carrier_subset_region_union_central_union_region (hcarrier hx) with
    (hneg | hzero) | hpos
  · exact Or.inl hneg
  · exact False.elim ((Set.disjoint_left.mp havoid) hx hzero)
  · exact Or.inr hpos

end PoincareMT.EpsilonNeck
