import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckSlabClosure
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SeparatingNeckComponents










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}





theorem recut_positive_component (N : EpsilonNeck g) {P : Set M}
    (hPo : IsOpen P) (hPc : IsConnected P)
    (hPcl : closure P = P ∪ N.central_sphere)
    (habove : N.aboveGraph_m28 (fun _ => 0) ⊆ P)
    (hbelow : Disjoint (N.belowGraph_m28 (fun _ => 0)) P)
    {a b : ℝ} (ha : -N.epsilon⁻¹ < a) (ha0 : a < 0)
    (hb0 : 0 < b) (hb : b < N.epsilon⁻¹) :
    let W := P ∪ N.region a b
    let S := N.coordinate_map '' (univ ×ˢ ({a} : Set ℝ))
    IsOpen W ∧ IsConnected W ∧ N.central_sphere ⊆ W ∧
      frontier W = S ∧ closure W = W ∪ S ∧
      (∀ x ∈ W, connectedComponentIn Sᶜ x = W) ∧
      W \ P ⊆ N.coordinate_map '' (univ ×ˢ Icc a 0) := by
  let W := P ∪ N.region a b
  let S := N.coordinate_map '' (univ ×ˢ ({a} : Set ℝ))
  have hWo : IsOpen W := hPo.union (N.region_open a b)
  have hSW : N.central_sphere ⊆ W :=
    (N.central_sphere_subset_region ha0 hb0).trans subset_union_right
  let q : UnitTwoSphere := (N.coordinate_inverse N.center).1
  let w := N.coordinate_map (q, b / 2)
  have hwstrip : b / 2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    constructor <;> linarith
  have hwN : w ∈ N.carrier := N.coordinate_map_mem_of_axial (q, b / 2) hwstrip
  have hwheight : (N.coordinate_inverse w).2 = b / 2 :=
    congrArg Prod.snd (N.coordinate_inverse_coordinate_map_of_axial (q, b / 2) hwstrip)
  have hwR : w ∈ N.region a b := ⟨hwN, by rw [hwheight]; constructor <;> linarith⟩
  have hwP : w ∈ P := by
    apply habove
    refine ⟨hwN, ?_⟩
    change 0 < (N.coordinate_inverse w).2
    rw [hwheight]
    linarith
  have hWc : IsConnected W := IsConnected.union ⟨w, hwP, hwR⟩ hPc
    ⟨⟨w, hwR⟩, N.isPreconnected_region ha.le hb.le⟩
  have hfront : frontier W = S := by
    rw [hWo.frontier_eq]
    ext x
    constructor
    · rintro ⟨hxcl, hxnot⟩
      change x ∈ closure (P ∪ N.region a b) at hxcl
      rw [closure_union, hPcl, N.closure_region_eq_coordinate_slab ha (ha0.trans hb0) hb]
        at hxcl
      rcases hxcl with (hxP | hxS) | hxslab
      · exact False.elim (hxnot (Or.inl hxP))
      · exact False.elim (hxnot (hSW hxS))
      · obtain ⟨z, hz, rfl⟩ := hxslab
        have hzstrip : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
          ⟨ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩
        have hzN := N.coordinate_map_mem_of_axial z hzstrip
        have hheight := N.coordinate_inverse_coordinate_map_of_axial z hzstrip
        have hza : z.2 = a := by
          by_contra hne
          have haz : a < z.2 := lt_of_le_of_ne hz.2.1 (Ne.symm hne)
          by_cases hzb : z.2 < b
          · exact hxnot (Or.inr ⟨hzN, by rw [hheight]; exact ⟨haz, hzb⟩⟩)
          · apply hxnot
            apply Or.inl
            apply habove
            refine ⟨hzN, ?_⟩
            change 0 < (N.coordinate_inverse (N.coordinate_map z)).2
            rw [hheight]
            exact hb0.trans_le (le_of_not_gt hzb)
        exact ⟨z, ⟨mem_univ _, hza⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      have hza : z.2 = a := hz.2
      have hzstrip : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
        rw [hza]
        exact ⟨ha, ha0.trans (hb0.trans hb)⟩
      have hzN := N.coordinate_map_mem_of_axial z hzstrip
      have hheight := N.coordinate_inverse_coordinate_map_of_axial z hzstrip
      have hxcl : N.coordinate_map z ∈ closure (N.region a b) := by
        rw [N.closure_region_eq_coordinate_slab ha (ha0.trans hb0) hb]
        exact ⟨z, ⟨mem_univ _, by rw [hza]; exact ⟨le_rfl, (ha0.trans hb0).le⟩⟩, rfl⟩
      refine ⟨closure_mono subset_union_right hxcl, ?_⟩
      rintro (hxP | hxR)
      · apply disjoint_left.mp hbelow _ hxP
        refine ⟨hzN, ?_⟩
        change (N.coordinate_inverse (N.coordinate_map z)).2 < 0
        rw [hheight, hza]
        exact ha0
      · have hh := hxR.2.1
        rw [hheight, hza] at hh
        exact (lt_irrefl a) hh
  have hclosure : closure W = W ∪ S :=
    (closure_eq_self_union_frontier W).trans (congrArg (W ∪ ·) hfront)
  have hWS : W ⊆ Sᶜ := by
    intro x hx hxS
    have hf : x ∈ frontier W := hfront.symm ▸ hxS
    exact (hWo.frontier_eq ▸ hf).2 hx
  refine ⟨hWo, hWc, hSW, hfront, hclosure, ?_, ?_⟩
  · intro x hx
    apply Subset.antisymm
    · apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hWo
        ⟨x, mem_connectedComponentIn (hWS hx), hx⟩
      rintro y ⟨hycl, hyC⟩
      rcases hclosure ▸ hycl with hyW | hyS
      · exact hyW
      · exact False.elim (connectedComponentIn_subset Sᶜ x hyC hyS)
    · exact hWc.isPreconnected.subset_connectedComponentIn hx hWS
  · rintro x ⟨hxW, hxP⟩
    have hxR : x ∈ N.region a b := hxW.resolve_left hxP
    have hheight : (N.coordinate_inverse x).2 ≤ 0 := by
      by_contra hnot
      exact hxP (habove ⟨hxR.1, lt_of_not_ge hnot⟩)
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hxR.2.1.le, hheight⟩,
      N.coordinate_map_coordinate_inverse hxR.1⟩

end PoincareConjecture.EpsilonNeck
