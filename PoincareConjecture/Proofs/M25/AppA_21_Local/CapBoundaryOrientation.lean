import PoincareConjecture.Proofs.M25.AppA_21_Local.CapBasics
import PoincareConjecture.Proofs.M25.AppA_1_Necks.Coordinates
import PoincareConjecture.Proofs.M25.AppA_1_Necks.Reversal

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem CapCertificate.exists_outward_boundary_neck
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : CapCertificate g) :
    ∃ R : EpsilonNeck g,
      (R = C.boundary_neck ∨ R = C.boundary_neck.reverse) ∧
      R.epsilon = C.epsilon ∧ R.carrier = C.boundary_neck.carrier ∧
      R.central_sphere = C.boundary_sphere ∧
      R.carrier ∩ C.core = R.region (-C.epsilon⁻¹) 0 ∧
      R.carrier ∩ C.end_neck.carrier = R.region 0 C.epsilon⁻¹ := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let B := C.boundary_neck
  let N := C.end_neck
  let L := C.epsilon⁻¹
  let Bm := B.region (-L) 0
  let Bp := B.region 0 L
  have hL : 0 < L := inv_pos.mpr C.epsilon_pos
  have hB : B.epsilon = C.epsilon := C.boundary_neck_epsilon
  have hKclosed : IsClosed C.closed_core := C.closed_core_compact.isClosed
  have hSK : C.boundary_sphere ⊆ C.closed_core := by
    rw [← C.core_frontier_eq_boundary]
    exact hKclosed.frontier_subset
  have hKN : Disjoint C.closed_core N.carrier := by
    apply disjoint_left.mpr
    intro x hx hxN
    rw [C.closed_core_eq_complement_end] at hx
    exact hx.2 hxN
  have hcoreK : C.core ⊆ C.closed_core := by
    rw [C.core_eq_interior_closed_core]
    exact interior_subset
  have hcoreOpen : IsOpen C.core := by
    rw [C.core_eq_interior_closed_core]
    exact isOpen_interior
  have hcoreN : Disjoint C.core N.carrier := hKN.mono_left hcoreK
  have hSN : Disjoint C.boundary_sphere N.carrier := hKN.mono_left hSK
  have hScore : Disjoint C.boundary_sphere C.core := by
    apply disjoint_left.mpr
    intro x hxS hxc
    have hxi : x ∈ interior C.closed_core := by
      rwa [C.core_eq_interior_closed_core] at hxc
    rw [← C.core_frontier_eq_boundary] at hxS
    exact hxS.2 hxi
  have hconnected (D : EpsilonNeck g) {a b : ℝ}
      (ha : -D.epsilon⁻¹ ≤ a) (hb : b ≤ D.epsilon⁻¹) (hab : a < b) :
      IsConnected (D.region a b) := by
    have heq : D.region a b = D.coordinate_map '' (univ ×ˢ Ioo a b) := by
      apply Subset.antisymm
      · intro x hx
        exact ⟨D.coordinate_inverse x, ⟨mem_univ _, hx.2⟩,
          D.coordinate_map_inverse hx.1⟩
      · rintro x ⟨z, hz, rfl⟩
        have hzs : z.2 ∈ Ioo (-D.epsilon⁻¹) D.epsilon⁻¹ :=
          ⟨ha.trans_lt hz.2.1, hz.2.2.trans_le hb⟩
        refine ⟨D.coordinate_map_mem ⟨mem_univ _, hzs⟩, ?_⟩
        rw [D.coordinate_inverse_map z hzs]
        exact hz.2
    rw [heq]
    apply (isConnected_univ.prod (isConnected_Ioo hab)).image
    exact D.coordinate_map_smooth.continuousOn.mono
      (fun _ hz => ⟨mem_univ _, ha.trans_lt hz.2.1, hz.2.2.trans_le hb⟩)
  have hBm : IsConnected Bm := by
    apply hconnected B ?_ ?_ (neg_lt_zero.mpr hL)
    · simpa only [hB] using (le_rfl : -L ≤ -L)
    · simpa only [hB] using hL.le
  have hBp : IsConnected Bp := by
    apply hconnected B ?_ ?_ hL
    · simpa only [hB] using (neg_nonpos.mpr hL.le : -L ≤ 0)
    · simpa only [hB] using (le_rfl : L ≤ L)
  have hBmS : Disjoint Bm C.boundary_sphere := by
    rw [C.boundary_eq_neck_sphere]
    exact (B.central_sphere_disjoint_region (-L) 0 (Or.inl le_rfl)).symm
  have hBpS : Disjoint Bp C.boundary_sphere := by
    rw [C.boundary_eq_neck_sphere]
    exact (B.central_sphere_disjoint_region 0 L (Or.inr le_rfl)).symm
  have hBcover : B.carrier ⊆ Bm ∪ C.boundary_sphere ∪ Bp := by
    simpa only [Bm, Bp, L, hB, C.boundary_eq_neck_sphere] using
      B.carrier_subset_region_union_central_union_region
  have hside {T : Set M} (hT : IsPreconnected T) (hTB : T ⊆ B.carrier)
      (hTS : Disjoint T C.boundary_sphere) : T ⊆ C.core ∨ T ⊆ N.carrier := by
    apply hT.subset_or_subset hcoreOpen N.carrier_open hcoreN
    intro x hx
    by_cases hxN : x ∈ N.carrier
    · exact Or.inr hxN
    · have hxK : x ∈ C.closed_core := by
        rw [C.closed_core_eq_complement_end]
        exact ⟨C.boundary_neck_subset (hTB hx), hxN⟩
      apply Or.inl
      rw [C.core_eq_interior_closed_core]
      by_contra hxi
      apply disjoint_left.mp hTS hx
      rw [← C.core_frontier_eq_boundary]
      exact ⟨subset_closure hxK, hxi⟩
  have hpS : B.center ∈ C.boundary_sphere := by
    rw [C.boundary_eq_neck_sphere]
    exact B.center_on_central_sphere
  have hpB : B.center ∈ B.carrier :=
    B.central_sphere_subset B.center_on_central_sphere
  have hmeetCore : (B.carrier ∩ C.core).Nonempty := by
    have hp : B.center ∈ closure C.core := by
      rw [C.m25_closure_core_eq_closed_core]
      exact hSK hpS
    exact mem_closure_iff.mp hp B.carrier B.carrier_open hpB
  have hmeetEnd : (B.carrier ∩ N.carrier).Nonempty := by
    obtain ⟨x, hxB, hxR⟩ := mem_closure_iff.mp
      (C.boundary_subset_negative_end_closure hpS) B.carrier B.carrier_open hpB
    exact ⟨x, hxB, hxR.1⟩
  have hchoices : (Bm ⊆ C.core ∧ Bp ⊆ N.carrier) ∨
      (Bm ⊆ N.carrier ∧ Bp ⊆ C.core) := by
    rcases hside hBm.isPreconnected (fun _ hx => hx.1) hBmS with hm | hm <;>
      rcases hside hBp.isPreconnected (fun _ hx => hx.1) hBpS with hp | hp
    · obtain ⟨x, hxB, hxN⟩ := hmeetEnd
      rcases hBcover hxB with (hxm | hxS) | hxp
      · exact False.elim (disjoint_left.mp hcoreN (hm hxm) hxN)
      · exact False.elim (disjoint_left.mp hSN hxS hxN)
      · exact False.elim (disjoint_left.mp hcoreN (hp hxp) hxN)
    · exact Or.inl ⟨hm, hp⟩
    · exact Or.inr ⟨hm, hp⟩
    · obtain ⟨x, hxB, hxc⟩ := hmeetCore
      rcases hBcover hxB with (hxm | hxS) | hxp
      · exact False.elim (disjoint_left.mp hcoreN hxc (hm hxm))
      · exact False.elim (disjoint_left.mp hScore hxS hxc)
      · exact False.elim (disjoint_left.mp hcoreN hxc (hp hxp))
  obtain ⟨R, hR, hRepsilon, hRcarrier, hRsphere, hneg, hpos⟩ :
      ∃ R : EpsilonNeck g,
        (R = B ∨ R = B.reverse) ∧ R.epsilon = C.epsilon ∧
        R.carrier = B.carrier ∧ R.central_sphere = C.boundary_sphere ∧
        R.region (-L) 0 ⊆ C.core ∧ R.region 0 L ⊆ N.carrier := by
    rcases hchoices with ⟨hm, hp⟩ | ⟨hm, hp⟩
    · exact ⟨B, Or.inl rfl, hB, rfl, C.boundary_eq_neck_sphere.symm, hm, hp⟩
    · refine ⟨B.reverse, Or.inr rfl, hB, rfl,
        C.boundary_eq_neck_sphere.symm, ?_, ?_⟩
      · simpa only [EpsilonNeck.reverse_region, neg_zero, neg_neg] using
          (hp : B.region 0 L ⊆ C.core)
      · simpa only [EpsilonNeck.reverse_region, neg_zero] using
          (hm : B.region (-L) 0 ⊆ N.carrier)
  have hRcover : R.carrier ⊆
      R.region (-L) 0 ∪ C.boundary_sphere ∪ R.region 0 L := by
    simpa only [hRepsilon, hRsphere] using
      R.carrier_subset_region_union_central_union_region
  refine ⟨R, hR, hRepsilon, hRcarrier, hRsphere, ?_, ?_⟩
  · apply Subset.antisymm
    · intro x hx
      rcases hRcover hx.1 with (hxm | hxS) | hxp
      · exact hxm
      · exact False.elim (disjoint_left.mp hScore hxS hx.2)
      · exact False.elim (disjoint_left.mp hcoreN hx.2 (hpos hxp))
    · intro x hx
      exact ⟨hx.1, hneg hx⟩
  · apply Subset.antisymm
    · intro x hx
      rcases hRcover hx.1 with (hxm | hxS) | hxp
      · exact False.elim (disjoint_left.mp hcoreN (hneg hxm) hx.2)
      · exact False.elim (disjoint_left.mp hSN hxS hx.2)
      · exact hxp
    · intro x hx
      exact ⟨hx.1, hpos hx⟩

end PoincareConjecture
