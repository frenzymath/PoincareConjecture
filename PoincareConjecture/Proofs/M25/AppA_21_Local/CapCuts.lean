import PoincareConjecture.Proofs.M25.AppA_21_Local.CapBasics
import PoincareConjecture.Proofs.M25.AppA_1_Necks.Coordinates
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem CapCertificate.boundary_subset_closure_end_region
    (C : CapCertificate g) {t : ℝ}
    (ht : t ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹) :
    C.boundary_sphere ⊆ closure (C.end_neck.region (-C.epsilon⁻¹) t) := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  have hK : IsClosed C.closed_core := C.closed_core_compact.isClosed
  have hSK : C.boundary_sphere ⊆ C.closed_core := by
    rw [← C.core_frontier_eq_boundary]
    exact hK.frontier_subset
  have havoid : Disjoint C.boundary_sphere C.end_neck.carrier := by
    apply disjoint_left.mpr
    intro x hx hxN
    have hxK := hSK hx
    rw [C.closed_core_eq_complement_end] at hxK
    exact hxK.2 hxN
  by_cases hcut : -C.epsilon⁻¹ / 2 ≤ t
  · apply C.boundary_subset_negative_end_closure.trans (closure_mono ?_)
    intro x hx
    exact ⟨hx.1, hx.2.1, hx.2.2.trans_le hcut⟩
  · let D := C.end_neck.coordinate_map '' (univ ×ˢ Icc t (-C.epsilon⁻¹ / 2))
    have hupper : -C.epsilon⁻¹ / 2 < C.end_neck.epsilon⁻¹ := by
      rw [C.end_neck_epsilon]
      have hpos := inv_pos.mpr C.epsilon_pos
      linarith
    have hlower : -C.end_neck.epsilon⁻¹ < t := by
      rw [C.end_neck_epsilon]
      exact ht.1
    have hD : IsCompact D := C.end_neck.isCompact_coordinate_slab hlower hupper
    have hDN : D ⊆ C.end_neck.carrier := by
      rintro x ⟨z, hz, rfl⟩
      exact C.end_neck.coordinate_map_mem
        ⟨mem_univ _, hlower.trans_le hz.2.1, hz.2.2.trans_lt hupper⟩
    have hcover : C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2) ⊆
        C.end_neck.region (-C.epsilon⁻¹) t ∪ D := by
      intro x hx
      by_cases hxt : (C.end_neck.coordinate_inverse x).2 < t
      · exact Or.inl ⟨hx.1, hx.2.1, hxt⟩
      · exact Or.inr ⟨C.end_neck.coordinate_inverse x,
          ⟨mem_univ _, le_of_not_gt hxt, hx.2.2.le⟩,
          C.end_neck.coordinate_map_inverse hx.1⟩
    intro x hx
    have hcl := closure_mono hcover (C.boundary_subset_negative_end_closure hx)
    rw [closure_union, hD.isClosed.closure_eq] at hcl
    exact hcl.resolve_right (fun hxD => disjoint_left.mp havoid hx (hDN hxD))

theorem CapCertificate.isCompact_end_neck_lower_cut
    (C : CapCertificate g) {t : ℝ}
    (ht : t ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹) :
    IsCompact (C.carrier \ C.end_neck.region t C.epsilon⁻¹) := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let N := C.end_neck
  let L := C.epsilon⁻¹
  change t ∈ Ioo (-L) L at ht
  have hN : N.epsilon = C.epsilon := C.end_neck_epsilon
  have hKclosed : IsClosed C.closed_core := C.closed_core_compact.isClosed
  have hKsub : C.closed_core ⊆ C.carrier := by
    rw [C.closed_core_eq_complement_end]
    exact sdiff_subset
  have hSK : C.boundary_sphere ⊆ C.closed_core := by
    rw [← C.core_frontier_eq_boundary]
    exact hKclosed.frontier_subset
  obtain ⟨V, hV, hKV, hVU⟩ :=
    exists_compact_between C.closed_core_compact C.carrier_open hKsub
  have hVc : IsClosed V := hV.isClosed
  have hfront : IsCompact (frontier V) :=
    hV.of_isClosed_subset isClosed_frontier hVc.frontier_subset
  have hfrontN : frontier V ⊆ N.carrier := by
    intro x hx
    by_contra hxN
    have hxK : x ∈ C.closed_core := by
      rw [C.closed_core_eq_complement_end]
      exact ⟨hVU (hVc.frontier_subset hx), hxN⟩
    exact hx.2 (hKV hxK)
  obtain ⟨d, hd, hdh⟩ := hfront.exists_forall_le'
    (N.coordinate_inverse_smooth.continuousOn.snd.mono hfrontN)
    (a := -L) (fun x hx => by
      have hh := (N.coordinate_inverse_mem x (hfrontN hx)).2.1
      simpa only [hN] using hh)
  obtain ⟨a, ha, hatd⟩ := exists_between (lt_min ht.1 hd)
  have hat : a < t := hatd.trans_le (min_le_left _ _)
  have had : a < d := hatd.trans_le (min_le_right _ _)
  have haL : a < L := hat.trans ht.2
  have hTa_image : N.region (-L) a = N.coordinate_map '' (univ ×ˢ Ioo (-L) a) := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2⟩, N.coordinate_map_inverse hx.1⟩
    · rintro x ⟨z, hz, rfl⟩
      have hzs : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
        rw [hN]
        exact ⟨hz.2.1, hz.2.2.trans haL⟩
      refine ⟨N.coordinate_map_mem ⟨mem_univ _, hzs⟩, ?_⟩
      rw [N.coordinate_inverse_map z hzs]
      exact hz.2
  have hTa : IsConnected (N.region (-L) a) := by
    rw [hTa_image]
    apply (isConnected_univ.prod (isConnected_Ioo ha)).image
    apply N.coordinate_map_smooth.continuousOn.mono
    intro z hz
    rw [hN]
    exact ⟨mem_univ _, hz.2.1, hz.2.2.trans haL⟩
  have havoid : Disjoint (N.region (-L) a) (frontier V) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge (hdh x hy)) (hx.2.2.trans had)
  have hcover : N.region (-L) a ⊆ interior V ∪ Vᶜ := by
    intro x hx
    by_cases hxi : x ∈ interior V
    · exact Or.inl hxi
    · exact Or.inr fun hxV => disjoint_left.mp havoid hx ⟨subset_closure hxV, hxi⟩
  have hmeet : (N.region (-L) a ∩ interior V).Nonempty := by
    have hxS : C.boundary_neck.center ∈ C.boundary_sphere := by
      rw [C.boundary_eq_neck_sphere]
      exact C.boundary_neck.center_on_central_sphere
    have hxcl := C.boundary_subset_closure_end_region ⟨ha, haL⟩ hxS
    obtain ⟨y, hyV, hyT⟩ := mem_closure_iff.mp hxcl
      (interior V) isOpen_interior (hKV (hSK hxS))
    exact ⟨y, hyT, hyV⟩
  have hTin : N.region (-L) a ⊆ interior V := by
    rcases hTa.isPreconnected.subset_or_subset isOpen_interior hVc.isOpen_compl
        (disjoint_left.mpr (fun _ hx hy => hy (interior_subset hx))) hcover with h | h
    · exact h
    · obtain ⟨x, hxT, hxV⟩ := hmeet
      exact False.elim ((h hxT) (interior_subset hxV))
  let D := N.coordinate_map '' (univ ×ˢ Icc a t)
  have hD : IsCompact D := N.isCompact_coordinate_slab
    (by simpa only [hN] using ha) (by simpa only [hN] using ht.2)
  have hDN : D ⊆ N.carrier := by
    rintro x ⟨z, hz, rfl⟩
    apply N.coordinate_map_mem
    rw [EpsilonNeck.cylinderDomain, hN]
    exact ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt ht.2⟩
  have heq : C.carrier \ N.region t L = (V ∪ D) \ N.region t L := by
    apply Subset.antisymm
    · intro x hx
      refine ⟨?_, hx.2⟩
      by_cases hxN : x ∈ N.carrier
      · have hxL : (N.coordinate_inverse x).2 < L := by
          simpa only [hN] using (N.coordinate_inverse_mem x hxN).2.2
        have hxt : (N.coordinate_inverse x).2 ≤ t :=
          le_of_not_gt fun h => hx.2 ⟨hxN, h, hxL⟩
        by_cases hxa : (N.coordinate_inverse x).2 < a
        · apply Or.inl
          apply interior_subset (hTin ?_)
          refine ⟨hxN, ?_, hxa⟩
          simpa only [hN] using (N.coordinate_inverse_mem x hxN).2.1
        · exact Or.inr ⟨N.coordinate_inverse x,
            ⟨mem_univ _, le_of_not_gt hxa, hxt⟩, N.coordinate_map_inverse hxN⟩
      · apply Or.inl
        apply interior_subset (hKV ?_)
        rw [C.closed_core_eq_complement_end]
        exact ⟨hx.1, hxN⟩
    · intro x hx
      exact ⟨hx.1.elim (fun hxV => hVU hxV)
        (fun hxD => C.end_neck_subset (hDN hxD)), hx.2⟩
  change IsCompact (C.carrier \ N.region t L)
  rw [heq]
  exact (hV.union hD).diff (N.isOpen_region t L)

theorem CapCertificate.end_neck_lower_cut_topology
    (C : CapCertificate g) {t : ℝ}
    (ht : t ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹) :
    let L := C.epsilon⁻¹
    let Kt := C.carrier \ C.end_neck.region t L
    let Ut := C.closed_core ∪ C.end_neck.region (-L) t
    let St := C.end_neck.coordinate_map '' (univ ×ˢ ({t} : Set ℝ))
    Kt ⊆ C.carrier ∧ IsOpen Ut ∧ closure Ut = Kt ∧ interior Kt = Ut ∧
      frontier Ut = St ∧ frontier Kt = St ∧
      frontier C.carrier ⊆ closure (C.end_neck.region t L) := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let N := C.end_neck
  let B := C.boundary_neck
  let L := C.epsilon⁻¹
  let Kt := C.carrier \ N.region t L
  let Ut := C.closed_core ∪ N.region (-L) t
  let St := N.coordinate_map '' (univ ×ˢ ({t} : Set ℝ))
  change Kt ⊆ C.carrier ∧ IsOpen Ut ∧ closure Ut = Kt ∧ interior Kt = Ut ∧
    frontier Ut = St ∧ frontier Kt = St ∧ frontier C.carrier ⊆ closure (N.region t L)
  change t ∈ Ioo (-L) L at ht
  have hL : 0 < L := inv_pos.mpr C.epsilon_pos
  have hN : N.epsilon = C.epsilon := C.end_neck_epsilon
  have hB : B.epsilon = C.epsilon := C.boundary_neck_epsilon
  have htN : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    simpa only [hN] using ht
  have hKclosed : IsClosed C.closed_core := C.closed_core_compact.isClosed
  have hKtclosed : IsClosed Kt := (C.isCompact_end_neck_lower_cut ht).isClosed
  have hKsub : C.closed_core ⊆ C.carrier := by
    rw [C.closed_core_eq_complement_end]
    exact sdiff_subset
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
  have hSt (x : M) : x ∈ St ↔ x ∈ N.carrier ∧ (N.coordinate_inverse x).2 = t := by
    constructor
    · rintro ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
      have hs' : s = t := hs
      subst s
      refine ⟨N.coordinate_map_mem ⟨mem_univ _, htN⟩, ?_⟩
      rw [N.coordinate_inverse_map (q, t) htN]
    · rintro ⟨hxN, hxt⟩
      exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hxt⟩, N.coordinate_map_inverse hxN⟩
  have hStClosed : IsClosed St := by
    have hc : IsCompact St := by
      simpa only [St, Icc_self] using N.isCompact_coordinate_slab htN.1 htN.2
    exact hc.isClosed
  have hSSt : Disjoint C.boundary_sphere St := by
    apply disjoint_left.mpr
    intro x hx hy
    exact disjoint_left.mp hKN (hSK hx) ((hSt x).mp hy).1
  have hconnected (D : EpsilonNeck g) {a b : ℝ}
      (ha : -D.epsilon⁻¹ ≤ a) (hb : b ≤ D.epsilon⁻¹) (hab : a < b) :
      IsConnected (D.region a b) := by
    have heq : D.region a b = D.coordinate_map '' (univ ×ˢ Ioo a b) := by
      apply Subset.antisymm
      · intro x hx
        exact ⟨D.coordinate_inverse x, ⟨mem_univ _, hx.2⟩, D.coordinate_map_inverse hx.1⟩
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

  let O := (univ ×ˢ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹) ∩ B.coordinate_map ⁻¹' Stᶜ
  have hO : IsOpen O := B.coordinate_map_smooth.continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod isOpen_Ioo) hStClosed.isOpen_compl
  have hzero : univ ×ˢ ({0} : Set ℝ) ⊆ O := by
    rintro ⟨q, s⟩ ⟨_, hs⟩
    have hs' : s = 0 := hs
    subst s
    refine ⟨⟨mem_univ _, B.zero_mem_interval⟩, ?_⟩
    apply fun hx => disjoint_left.mp hSSt ?_ hx
    rw [C.boundary_eq_neck_sphere, B.central_sphere_eq]
    exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  obtain ⟨V, J, _, hJ, hV, hJ0, hprod⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hO hzero
  obtain ⟨ρ, hρ, hρJ⟩ := Metric.mem_nhds_iff.mp (hJ.mem_nhds (hJ0 rfl))
  obtain ⟨r, hr, hrmin⟩ := exists_between (lt_min hρ hL)
  have hrρ : r < ρ := hrmin.trans_le (min_le_left _ _)
  have hrL : r < L := hrmin.trans_le (min_le_right _ _)
  let Br := B.region (-r) r
  let Bm := B.region (-r) 0
  let Bp := B.region 0 r
  have hBrOpen : IsOpen Br := B.isOpen_region (-r) r
  have hSBr : C.boundary_sphere ⊆ Br := by
    intro x hx
    rw [C.boundary_eq_neck_sphere] at hx
    obtain ⟨hxB, hx0⟩ := (B.mem_central_sphere_iff x).mp hx
    refine ⟨hxB, ?_⟩
    rw [hx0]
    exact ⟨neg_lt_zero.mpr hr, hr⟩
  have hBrSt : Disjoint Br St := by
    apply disjoint_left.mpr
    intro x hx hxSt
    have hj : (B.coordinate_inverse x).2 ∈ J := by
      apply hρJ
      rw [mem_ball_zero_iff, Real.norm_eq_abs]
      exact abs_lt.mpr ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
    have hxO := hprod ⟨hV (mem_univ (B.coordinate_inverse x).1), hj⟩
    have hxnot := hxO.2
    change B.coordinate_map (B.coordinate_inverse x) ∉ St at hxnot
    rw [B.coordinate_map_inverse hx.1] at hxnot
    exact hxnot hxSt
  have hBzero : 0 < B.epsilon⁻¹ := inv_pos.mpr B.epsilon_pos
  have hBlo : -B.epsilon⁻¹ ≤ -r := by
    rw [hB]
    exact neg_le_neg hrL.le
  have hBhi : r ≤ B.epsilon⁻¹ := by
    simpa only [hB] using hrL.le
  have hBm : IsConnected Bm := hconnected B hBlo hBzero.le (neg_lt_zero.mpr hr)
  have hBp : IsConnected Bp := hconnected B (neg_nonpos.mpr hBzero.le) hBhi hr
  have hBmBr : Bm ⊆ Br := fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.trans hr⟩
  have hBpBr : Bp ⊆ Br := fun _ hx =>
    ⟨hx.1, (neg_lt_zero.mpr hr).trans hx.2.1, hx.2.2⟩
  have hBmS : Disjoint Bm C.boundary_sphere := by
    rw [C.boundary_eq_neck_sphere]
    exact (B.central_sphere_disjoint_region (-r) 0 (Or.inl le_rfl)).symm
  have hBpS : Disjoint Bp C.boundary_sphere := by
    rw [C.boundary_eq_neck_sphere]
    exact (B.central_sphere_disjoint_region 0 r (Or.inr le_rfl)).symm
  have hBrCover : Br ⊆ Bm ∪ C.boundary_sphere ∪ Bp := by
    intro x hx
    rcases lt_trichotomy (B.coordinate_inverse x).2 0 with hneg | hzero | hpos
    · exact Or.inl (Or.inl ⟨hx.1, hx.2.1, hneg⟩)
    · apply Or.inl (Or.inr ?_)
      rw [C.boundary_eq_neck_sphere]
      exact (B.mem_central_sphere_iff x).mpr ⟨hx.1, hzero⟩
    · exact Or.inr ⟨hx.1, hpos, hx.2.2⟩
  have hside {T : Set M} (hT : IsPreconnected T) (hTBr : T ⊆ Br)
      (hTS : Disjoint T C.boundary_sphere) : T ⊆ C.core ∨ T ⊆ N.carrier := by
    apply hT.subset_or_subset hcoreOpen N.carrier_open hcoreN
    intro x hx
    by_cases hxN : x ∈ N.carrier
    · exact Or.inr hxN
    · have hxK : x ∈ C.closed_core := by
        rw [C.closed_core_eq_complement_end]
        exact ⟨C.boundary_neck_subset (hTBr hx).1, hxN⟩
      apply Or.inl
      rw [C.core_eq_interior_closed_core]
      by_contra hxi
      apply disjoint_left.mp hTS hx
      rw [← C.core_frontier_eq_boundary]
      exact ⟨subset_closure hxK, hxi⟩
  have hpS : B.center ∈ C.boundary_sphere := by
    rw [C.boundary_eq_neck_sphere]
    exact B.center_on_central_sphere
  have hmeetCore : (Br ∩ C.core).Nonempty := by
    have hp : B.center ∈ closure C.core := by
      rw [C.m25_closure_core_eq_closed_core]
      exact hSK hpS
    exact mem_closure_iff.mp hp Br hBrOpen (hSBr hpS)
  have hmeetTail : (Br ∩ N.region (-L) t).Nonempty :=
    mem_closure_iff.mp (C.boundary_subset_closure_end_region ht hpS)
      Br hBrOpen (hSBr hpS)
  have hbelow {T : Set M} (hT : IsPreconnected T) (hTN : T ⊆ N.carrier)
      (hTBr : T ⊆ Br) (hmeet : (T ∩ N.region (-L) t).Nonempty) :
      T ⊆ N.region (-L) t := by
    have hcover : T ⊆ N.region (-L) t ∪ N.region t L := by
      intro x hx
      have hxN := hTN hx
      have hxint : (N.coordinate_inverse x).2 ∈ Ioo (-L) L := by
        simpa only [hN] using (N.coordinate_inverse_mem x hxN).2
      have hxne : (N.coordinate_inverse x).2 ≠ t := by
        intro heq
        exact disjoint_left.mp hBrSt (hTBr hx) ((hSt x).mpr ⟨hxN, heq⟩)
      rcases lt_or_gt_of_ne hxne with hlo | hhi
      · exact Or.inl ⟨hxN, hxint.1, hlo⟩
      · exact Or.inr ⟨hxN, hhi, hxint.2⟩
    rcases hT.subset_or_subset (N.isOpen_region (-L) t) (N.isOpen_region t L)
        (N.region_disjoint_of_le le_rfl) hcover with h | h
    · exact h
    · obtain ⟨x, hxT, hxlo⟩ := hmeet
      exact False.elim (lt_asymm hxlo.2.2 (h hxT).2.1)
  have hcoreUt : C.core ⊆ Ut := fun _ hx => Or.inl (hcoreK hx)
  have htailUt : N.region (-L) t ⊆ Ut := fun _ hx => Or.inr hx
  have hfinish (hm : Bm ⊆ Ut) (hp : Bp ⊆ Ut) : Br ⊆ Ut := by
    intro x hx
    rcases hBrCover hx with (hxm | hxS) | hxp
    · exact hm hxm
    · exact Or.inl (hSK hxS)
    · exact hp hxp
  have hBrUt : Br ⊆ Ut := by
    rcases hside hBm.isPreconnected hBmBr hBmS with hm | hm <;>
      rcases hside hBp.isPreconnected hBpBr hBpS with hp | hp
    · exact hfinish (hm.trans hcoreUt) (hp.trans hcoreUt)
    · have hmeet : (Bp ∩ N.region (-L) t).Nonempty := by
        obtain ⟨x, hxBr, hxT⟩ := hmeetTail
        rcases hBrCover hxBr with (hxm | hxS) | hxp
        · exact False.elim (disjoint_left.mp hcoreN (hm hxm) hxT.1)
        · exact False.elim (disjoint_left.mp hKN (hSK hxS) hxT.1)
        · exact ⟨x, hxp, hxT⟩
      exact hfinish (hm.trans hcoreUt)
        ((hbelow hBp.isPreconnected hp hBpBr hmeet).trans htailUt)
    · have hmeet : (Bm ∩ N.region (-L) t).Nonempty := by
        obtain ⟨x, hxBr, hxT⟩ := hmeetTail
        rcases hBrCover hxBr with (hxm | hxS) | hxp
        · exact ⟨x, hxm, hxT⟩
        · exact False.elim (disjoint_left.mp hKN (hSK hxS) hxT.1)
        · exact False.elim (disjoint_left.mp hcoreN (hp hxp) hxT.1)
      exact hfinish ((hbelow hBm.isPreconnected hm hBmBr hmeet).trans htailUt)
        (hp.trans hcoreUt)
    · obtain ⟨x, hxBr, hxcore⟩ := hmeetCore
      rcases hBrCover hxBr with (hxm | hxS) | hxp
      · exact False.elim (disjoint_left.mp hcoreN hxcore (hm hxm))
      · have hxi : x ∈ interior C.closed_core := by
          rwa [C.core_eq_interior_closed_core] at hxcore
        rw [← C.core_frontier_eq_boundary] at hxS
        exact False.elim (hxS.2 hxi)
      · exact False.elim (disjoint_left.mp hcoreN hxcore (hp hxp))
  have hUtOpen : IsOpen Ut := by
    apply isOpen_iff_forall_mem_open.mpr
    intro x hx
    rcases hx with hxK | hxT
    · by_cases hxc : x ∈ C.core
      · exact ⟨C.core, hcoreUt, hcoreOpen, hxc⟩
      · have hxS : x ∈ C.boundary_sphere := by
          rw [← C.core_frontier_eq_boundary]
          refine ⟨subset_closure hxK, ?_⟩
          simpa only [C.core_eq_interior_closed_core] using hxc
        exact ⟨Br, hBrUt, hBrOpen, hSBr hxS⟩
    · exact ⟨N.region (-L) t, htailUt, N.isOpen_region (-L) t, hxT⟩
  have hUtKt : Ut ⊆ Kt := by
    intro x hx
    rcases hx with hxK | hxT
    · exact ⟨hKsub hxK, fun hxP => disjoint_left.mp hKN hxK hxP.1⟩
    · exact ⟨C.end_neck_subset hxT.1, fun hxP => lt_asymm hxT.2.2 hxP.2.1⟩
  have hStKt : St ⊆ Kt := by
    intro x hx
    obtain ⟨hxN, hxt⟩ := (hSt x).mp hx
    exact ⟨C.end_neck_subset hxN, fun hxP => (ne_of_gt hxP.2.1) hxt⟩
  have hdecomp : Kt = Ut ∪ St := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxN : x ∈ N.carrier
      · have hxint : (N.coordinate_inverse x).2 ∈ Ioo (-L) L := by
          simpa only [hN] using (N.coordinate_inverse_mem x hxN).2
        have hxt : (N.coordinate_inverse x).2 ≤ t :=
          le_of_not_gt fun h => hx.2 ⟨hxN, h, hxint.2⟩
        rcases hxt.lt_or_eq with hlt | heq
        · exact Or.inl (Or.inr ⟨hxN, hxint.1, hlt⟩)
        · exact Or.inr ((hSt x).mpr ⟨hxN, heq⟩)
      · apply Or.inl (Or.inl ?_)
        rw [C.closed_core_eq_complement_end]
        exact ⟨hx.1, hxN⟩
    · exact union_subset hUtKt hStKt
  have hUtSt : Disjoint Ut St := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨hyN, hyt⟩ := (hSt x).mp hy
    rcases hx with hxK | hxT
    · exact disjoint_left.mp hKN hxK hyN
    · exact hxT.2.2.ne hyt
  have hdiff : Kt \ Ut = St := by
    rw [hdecomp]
    ext x
    constructor
    · rintro ⟨hxU | hxS, hxnot⟩
      · exact False.elim (hxnot hxU)
      · exact hxS
    · intro hxS
      exact ⟨Or.inr hxS, fun hxU => disjoint_left.mp hUtSt hxU hxS⟩

  have hsliceClosure {a b : ℝ} (ha : -L ≤ a) (hb : b ≤ L)
      (hab : a < b) (htab : t ∈ Icc a b) : St ⊆ closure (N.region a b) := by
    rintro x ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
    have hs' : s = t := hs
    subst s
    have hf : ContinuousAt (fun s : ℝ => N.coordinate_map (q, s)) t :=
      (N.coordinate_map_smooth.continuousOn.continuousAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, htN⟩)).comp
        (continuous_const.prodMk continuous_id).continuousAt
    have himage : (fun s : ℝ => N.coordinate_map (q, s)) '' Ioo a b ⊆
        N.region a b := by
      rintro x ⟨s, hs, rfl⟩
      have hsN : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
        rw [hN]
        exact ⟨ha.trans_lt hs.1, hs.2.trans_le hb⟩
      refine ⟨N.coordinate_map_mem ⟨mem_univ _, hsN⟩, ?_⟩
      rw [N.coordinate_inverse_map (q, s) hsN]
      exact hs
    apply closure_mono himage (mem_closure_image hf ?_)
    rw [closure_Ioo hab.ne]
    exact htab
  have hStLower : St ⊆ closure Ut :=
    (hsliceClosure le_rfl ht.2.le ht.1 ⟨ht.1.le, le_rfl⟩).trans
      (closure_mono htailUt)
  have hStUpper : St ⊆ closure (N.region t L) :=
    hsliceClosure ht.1.le le_rfl ht.2 ⟨le_rfl, ht.2.le⟩
  have hclosure : closure Ut = Kt := by
    apply Subset.antisymm (closure_minimal hUtKt hKtclosed)
    rw [hdecomp]
    exact union_subset subset_closure hStLower
  have hnotInterior : Disjoint (interior Kt) St := by
    apply disjoint_left.mpr
    intro x hxI hxS
    obtain ⟨y, hyI, hyP⟩ := mem_closure_iff.mp (hStUpper hxS)
      (interior Kt) isOpen_interior hxI
    exact (interior_subset hyI).2 hyP
  have hinterior : interior Kt = Ut := by
    apply Subset.antisymm ?_ (interior_maximal hUtKt hUtOpen)
    intro x hx
    have hxKt := interior_subset hx
    rw [hdecomp] at hxKt
    exact hxKt.resolve_right (fun hxS => disjoint_left.mp hnotInterior hx hxS)
  have hfrontUt : frontier Ut = St := by
    rw [hUtOpen.frontier_eq, hclosure, hdiff]
  have hfrontKt : frontier Kt = St := by
    rw [hKtclosed.frontier_eq, hinterior, hdiff]
  refine ⟨sdiff_subset, hUtOpen, hclosure, hinterior, hfrontUt, hfrontKt, ?_⟩
  have hcover : C.carrier = Kt ∪ N.region t L := by
    ext x
    constructor
    · intro hx
      by_cases hxP : x ∈ N.region t L
      · exact Or.inr hxP
      · exact Or.inl ⟨hx, hxP⟩
    · rintro (hx | hx)
      · exact hx.1
      · exact C.end_neck_subset hx.1
  intro x hx
  have hxcl := hx.1
  rw [hcover, closure_union, hKtclosed.closure_eq] at hxcl
  apply hxcl.resolve_left
  intro hxKt
  apply hx.2
  rw [C.carrier_open.interior_eq]
  exact hxKt.1

end PoincareConjecture
