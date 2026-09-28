import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Source.Trim



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

theorem returning_disk_negative_half_contact
    {E : Type*} {D B : Set E} {c : P2 → E}
    (hcommon : D ∩ B = c '' arm 0) (hhalf : c '' halfSource false ⊆ B) :
    D ∩ (c '' halfSource false) = c '' arm 0 := by
  apply Subset.antisymm
  · exact fun _ hx ↦ hcommon.subset ⟨hx.1, hhalf hx.2⟩
  · exact fun _ hx ↦ ⟨(hcommon.superset hx).1,
      image_mono (arm_zero_subset_halfSource false) hx⟩

theorem exists_enlarged_returning_disk
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {T Q D B S H : Set E} {c : P2 → E}
    (hT : IsFinitePLBallPair P2 T Q)
    (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hcS : MapsTo c source S) (hST : S ⊆ T) (hDS : D ⊆ S)
    (hcQ : ∀ p ∈ source, c p ∈ Q ↔ p.1 = 0 ∨ p.1 = 1)
    (hB : IsFinitePLBallPair P2 B ((B ∩ Q) ∪ c '' arm 0))
    (hcover : D ∪ B = T) (hcommon : D ∩ B = c '' arm 0)
    (hhalf : c '' halfSource false ⊆ B)
    (hDH : Disjoint D H) (hcH : Disjoint (c '' source) H) :
    ∃ N C U V : Set E,
      IsFinitePLBallPair P2 N (U ∪ c '' arm (-1)) ∧
      IsFinitePLBallPair P2 C ((c '' arm (-1)) ∪ V) ∧
      IsFinitePLBallPair ℝ U {c (0, -1), c (1, -1)} ∧
      U ∩ (c '' arm (-1)) = {c (0, -1), c (1, -1)} ∧
      N ∪ C = T ∧ N ∩ C = c '' arm (-1) ∧ N ∩ Q = U ∧
      N = D ∪ c '' halfSource false ∧ C = B \ ((c '' halfSource false) \ c '' arm (-1)) ∧
      N ⊆ S ∧ Disjoint N H ∧
      c '' arm 0 ⊆ N \ C ∧ Disjoint C (c '' arm 0) := by
  obtain ⟨N, C, U, V, hN, hC, hU, _, hNC, hcommon', hNU, _,
    _, _, _, hnoCenter, _, hcenter, hNeq, hCeq⟩ :=
    exists_cut_disk_enlargement_across_half_strip hT c false hc hci
      (fun _ hp ↦ hST (hcS hp)) hcQ hB hcover hcommon hhalf
  have hfarN : c '' arm (-1) ⊆ N := subset_union_left.trans hN.1
  have hUf : U ∩ (c '' arm (-1)) = {c (0, -1), c (1, -1)} := by
    rw [← hNU, inter_assoc, inter_eq_right.mpr (inter_subset_right.trans hfarN)]
    exact proper_strip_arm_rim_contact (by norm_num) hcQ
  refine ⟨N, C, U, V, ?_, hC, hU, hUf, hNC, hcommon', hNU, hNeq, hCeq, ?_, ?_,
    hcenter, hnoCenter⟩
  · simpa only [farArmParameter, Bool.false_eq_true, if_false, union_comm] using hN
  · rw [hNeq]
    exact union_subset hDS ((image_mono (halfSource_subset_source false)).trans hcS.image_subset)
  · rw [hNeq]
    exact disjoint_union_left.mpr ⟨hDH, hcH.mono_left (image_mono (halfSource_subset_source false))⟩

end PoincareConjecture.M76.Dehn.Annuli
