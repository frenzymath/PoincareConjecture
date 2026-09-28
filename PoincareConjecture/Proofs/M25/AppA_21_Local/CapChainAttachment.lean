import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCuts
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SingleNeckCylinder
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem OpenCylinderModel.exists_tail_subset_of_compact_level
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {U : Set M} (T : OpenCylinderModel U) (H : M → ℝ) {c t : ℝ}
    (hct : c < t) (hH : ContinuousOn H U)
    (hlower : ∀ x ∈ U, c < H x)
    (happroach : ∀ d ∈ Set.Ioo c t, ∃ x ∈ U, H x < d)
    (hlevel : IsCompact (U ∩ H ⁻¹' ({t} : Set ℝ))) :
    ∃ side : Bool, ∃ a ∈ Set.Ioo (0 : ℝ) 1,
      T.tail side a ⊆ U ∩ H ⁻¹' Set.Iio t := by
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let h : M → ℝ := fun x => (T.inverse x).2
  have hcont : ContinuousOn h U := T.inverse_smooth.continuousOn.snd
  have hmap {z : RoundCylinderSpace} (hz : z ∈ univ ×ˢ Ioo (0 : ℝ) 1) :
      T.coordinate z ∈ U := by
    have hm := (T.homeomorph (z.1, ⟨z.2, hz.2⟩)).property
    rwa [T.coordinate_eq] at hm
  have htail (side : Bool) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (x : M) :
      x ∈ T.tail side r ↔ x ∈ U ∧ (if side then r < h x else h x < r) := by
    cases side
    · simp only [OpenCylinderModel.tail, Bool.false_eq_true, if_false]
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hzs : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
          ⟨mem_univ _, hz.2.1, hz.2.2.trans hr.2⟩
        refine ⟨hmap hzs, ?_⟩
        change (T.inverse (T.coordinate z)).2 < r
        rw [T.left_inverse hzs]
        exact hz.2.2
      · rintro ⟨hx, hxr⟩
        exact ⟨T.inverse x, ⟨mem_univ _, (T.inverse_mem x hx).2.1, hxr⟩,
          T.right_inverse hx⟩
    · simp only [OpenCylinderModel.tail, if_true]
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hzs : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
          ⟨mem_univ _, hr.1.trans hz.2.1, hz.2.2⟩
        refine ⟨hmap hzs, ?_⟩
        change r < (T.inverse (T.coordinate z)).2
        rw [T.left_inverse hzs]
        exact hz.2.1
      · rintro ⟨hx, hrx⟩
        exact ⟨T.inverse x, ⟨mem_univ _, hrx, (T.inverse_mem x hx).2.2⟩,
          T.right_inverse hx⟩
  have hbandConnected {p q : ℝ} (hp : 0 ≤ p) (hq : q ≤ 1) (hpq : p < q) :
      IsConnected (T.coordinate '' (univ ×ˢ Ioo p q)) := by
    apply (isConnected_univ.prod (isConnected_Ioo hpq)).image
    exact T.coordinate_smooth.continuousOn.mono
      (fun _ hz => ⟨mem_univ _, hp.trans_lt hz.2.1, hz.2.2.trans_le hq⟩)
  have htailConnected (side : Bool) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
      IsConnected (T.tail side r) := by
    cases side
    · exact hbandConnected le_rfl hr.2.le hr.1
    · exact hbandConnected hr.1.le le_rfl hr.2
  have hlevelCont : ContinuousOn h (U ∩ H ⁻¹' ({t} : Set ℝ)) :=
    hcont.mono inter_subset_left
  obtain ⟨l, hl, hlLevel⟩ := hlevel.exists_forall_le' hlevelCont
    (a := (0 : ℝ)) (fun x hx => (T.inverse_mem x hx.1).2.1)
  obtain ⟨v, hv, hvLevel⟩ := hlevel.exists_forall_le' hlevelCont.neg
    (a := (-1 : ℝ)) (fun x hx => by
      have hx1 := (T.inverse_mem x hx.1).2.2
      change -1 < -h x
      dsimp only [h]
      linarith)
  obtain ⟨a, ha, haMin⟩ :=
    exists_between (lt_min hl (by norm_num : (0 : ℝ) < 1 / 3))
  have hal : a < l := haMin.trans_le (min_le_left _ _)
  have haThird : a < (1 / 3 : ℝ) := haMin.trans_le (min_le_right _ _)
  have hv1 : -v < (1 : ℝ) := by linarith
  obtain ⟨b, hbMax, hb⟩ :=
    exists_between (max_lt hv1 (by norm_num : (2 / 3 : ℝ) < 1))
  have hvb : -v < b := (le_max_left _ _).trans_lt hbMax
  have hbThird : (2 / 3 : ℝ) < b := (le_max_right _ _).trans_lt hbMax
  have hab : a < b := by linarith
  have ha01 : a ∈ Ioo (0 : ℝ) 1 := ⟨ha, hab.trans hb⟩
  have hb01 : b ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans hab, hb⟩
  have hlevelBounds (y : M) (hy : y ∈ U ∩ H ⁻¹' ({t} : Set ℝ)) :
      a < h y ∧ h y < b := by
    refine ⟨hal.trans_le (hlLevel y hy), ?_⟩
    have hyNeg : v ≤ -(h y) := hvLevel y hy
    have hyUpper : h y ≤ -v := by linarith
    exact hyUpper.trans_lt hvb
  let K := T.coordinate '' (univ ×ˢ Icc a b)
  have hdom : (univ : Set UnitTwoSphere) ×ˢ Icc a b ⊆
      univ ×ˢ Ioo (0 : ℝ) 1 :=
    fun _ hz => ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩
  have hK : IsCompact K :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (T.coordinate_smooth.continuousOn.mono hdom)
  have hKU : K ⊆ U := by
    rintro y ⟨z, hz, rfl⟩
    exact hmap (hdom hz)
  obtain ⟨d0, hd0, hd0K⟩ := hK.exists_forall_le' (hH.mono hKU)
    (a := c) (fun y hy => hlower y (hKU hy))
  obtain ⟨d, hcd, hd⟩ := exists_between (lt_min hd0 hct)
  have hdt : d < t := hd.trans_le (min_le_right _ _)
  have hdd0 : d < d0 := hd.trans_le (min_le_left _ _)
  obtain ⟨x, hxU, hxd⟩ := happroach d ⟨hcd, hdt⟩
  have hxt : H x < t := hxd.trans hdt
  have hxK : x ∉ K := by
    intro hx
    exact (not_lt_of_ge (hd0K x hx)) (hxd.trans hdd0)
  have hfinish (side : Bool) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
      (hxTail : x ∈ T.tail side r)
      (hne : ∀ y ∈ T.tail side r, H y ≠ t) :
      ∃ side : Bool, ∃ a ∈ Ioo (0 : ℝ) 1,
        T.tail side a ⊆ U ∩ H ⁻¹' Iio t := by
    have htailU : T.tail side r ⊆ U :=
      fun y hy => ((htail side hr y).mp hy).1
    refine ⟨side, r, hr, ?_⟩
    intro y hy
    refine ⟨htailU hy, ?_⟩
    exact (htailConnected side hr).isPreconnected.gt_of_ne
      (hH.mono htailU) hne ⟨x, hxTail, hxt⟩ hy
  by_cases hxa : h x < a
  · apply hfinish false ha01 ((htail false ha01 x).mpr ⟨hxU, hxa⟩)
    intro y hy hyt
    obtain ⟨hyU, hya⟩ := (htail false ha01 y).mp hy
    have hay := (hlevelBounds y ⟨hyU, hyt⟩).1
    exact lt_asymm hay hya
  · have hbx : b < h x := by
      by_contra hnot
      apply hxK
      exact ⟨T.inverse x,
        ⟨mem_univ _, le_of_not_gt hxa, le_of_not_gt hnot⟩,
        T.right_inverse hxU⟩
    apply hfinish true hb01 ((htail true hb01 x).mpr ⟨hxU, hbx⟩)
    intro y hy hyt
    obtain ⟨hyU, hby⟩ := (htail true hb01 y).mp hy
    have hyb := (hlevelBounds y ⟨hyU, hyt⟩).2
    exact lt_asymm hby hyb

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}

open Classical in

theorem CapCertificate.continuous_saturated_end_height (C : CapCertificate g) :
    let L := C.epsilon⁻¹
    let H : M → ℝ := fun x =>
      if x ∈ C.end_neck.carrier then (C.end_neck.coordinate_inverse x).2
      else if x ∈ C.carrier then -L else L
    Continuous H := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let N := C.end_neck
  let L := C.epsilon⁻¹
  let H : M → ℝ := fun x => if x ∈ N.carrier then (N.coordinate_inverse x).2
    else if x ∈ C.carrier then -L else L
  change Continuous H
  have hL : 0 < L := inv_pos.mpr C.epsilon_pos
  have hcoord {x : M} (hx : x ∈ N.carrier) : (N.coordinate_inverse x).2 ∈ Ioo (-L) L := by
    simpa only [N, L, C.end_neck_epsilon] using (N.coordinate_inverse_mem x hx).2
  have hins {x : M} (hx : x ∈ N.carrier) : H x = (N.coordinate_inverse x).2 := by
    simp only [H, if_pos hx]
  have hcore {x : M} (hxN : x ∉ N.carrier) (hxC : x ∈ C.carrier) : H x = -L := by
    simp only [H, if_neg hxN, if_pos hxC]
  have hout {x : M} (hxC : x ∉ C.carrier) : H x = L := by
    have hxN : x ∉ N.carrier := fun hx => hxC (C.end_neck_subset hx)
    simp only [H, if_neg hxN, if_neg hxC]
  have hcoreiff (x : M) : x ∈ C.closed_core ↔ x ∈ C.carrier ∧ x ∉ N.carrier := by
    rw [C.closed_core_eq_complement_end]
    rfl
  have hbounds (x : M) : H x ∈ Icc (-L) L := by
    by_cases hxN : x ∈ N.carrier
    · rw [hins hxN]
      exact Ioo_subset_Icc_self (hcoord hxN)
    · by_cases hxC : x ∈ C.carrier
      · rw [hcore hxN hxC]
        exact ⟨le_rfl, by linarith⟩
      · rw [hout hxC]
        exact ⟨by linarith, le_rfl⟩
  have hltret {r : ℝ} (hr : r ∈ Ioo (-L) L) :
      H ⁻¹' Iio r = C.closed_core ∪ N.region (-L) r := by
    ext x
    change H x < r ↔ x ∈ C.closed_core ∪ N.region (-L) r
    by_cases hxN : x ∈ N.carrier
    · rw [hins hxN]
      constructor
      · intro hx
        exact Or.inr ⟨hxN, (hcoord hxN).1, hx⟩
      · rintro (hx | hx)
        · exact False.elim (((hcoreiff x).mp hx).2 hxN)
        · exact hx.2.2
    · by_cases hxC : x ∈ C.carrier
      · rw [hcore hxN hxC]
        exact ⟨fun _ => Or.inl ((hcoreiff x).mpr ⟨hxC, hxN⟩), fun _ => hr.1⟩
      · rw [hout hxC]
        constructor
        · intro hx
          exact False.elim ((not_lt_of_ge hr.2.le) hx)
        · rintro (hx | hx)
          · exact False.elim (hxC ((hcoreiff x).mp hx).1)
          · exact False.elim (hxN hx.1)
  have hgtret {r : ℝ} (hr : r ∈ Ioo (-L) L) :
      H ⁻¹' Ioi r = (C.carrier \ N.region r L)ᶜ := by
    ext x
    change r < H x ↔ ¬ (x ∈ C.carrier ∧ x ∉ N.region r L)
    by_cases hxN : x ∈ N.carrier
    · rw [hins hxN]
      constructor
      · intro hx hK
        exact hK.2 ⟨hxN, hx, (hcoord hxN).2⟩
      · intro hx
        by_contra hnot
        exact hx ⟨C.end_neck_subset hxN, fun hrx => hnot hrx.2.1⟩
    · by_cases hxC : x ∈ C.carrier
      · rw [hcore hxN hxC]
        constructor
        · intro hx
          exact False.elim ((not_lt_of_ge hr.1.le) hx)
        · intro hx
          exact False.elim (hx ⟨hxC, fun hrx => hxN hrx.1⟩)
      · rw [hout hxC]
        exact ⟨fun _ hx => hxC hx.1, fun _ => hr.2⟩
  have hbottom : H ⁻¹' Ioi (-L) = C.closed_coreᶜ := by
    ext x
    change -L < H x ↔ x ∉ C.closed_core
    by_cases hxN : x ∈ N.carrier
    · rw [hins hxN]
      exact ⟨fun _ hx => ((hcoreiff x).mp hx).2 hxN, fun _ => (hcoord hxN).1⟩
    · by_cases hxC : x ∈ C.carrier
      · rw [hcore hxN hxC]
        exact ⟨fun hx => False.elim (lt_irrefl _ hx),
          fun hx => False.elim (hx ((hcoreiff x).mpr ⟨hxC, hxN⟩))⟩
      · rw [hout hxC]
        exact ⟨fun _ hx => hxC ((hcoreiff x).mp hx).1, fun _ => by linarith⟩
  have htop : H ⁻¹' Iio L = C.carrier := by
    ext x
    change H x < L ↔ x ∈ C.carrier
    by_cases hxN : x ∈ N.carrier
    · rw [hins hxN]
      exact ⟨fun _ => C.end_neck_subset hxN, fun _ => (hcoord hxN).2⟩
    · by_cases hxC : x ∈ C.carrier
      · rw [hcore hxN hxC]
        exact ⟨fun _ => hxC, fun _ => by linarith⟩
      · rw [hout hxC]
        exact ⟨fun hx => False.elim (lt_irrefl _ hx), fun hx => False.elim (hxC hx)⟩
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_order.mpr
  constructor
  · intro r hr
    by_cases hlo : r < -L
    · exact Filter.Eventually.of_forall fun y => hlo.trans_le (hbounds y).1
    · have hrL : r < L := hr.trans_le (hbounds x).2
      have hge : -L ≤ r := le_of_not_gt hlo
      have hopen : IsOpen (H ⁻¹' Ioi r) := by
        rcases eq_or_lt_of_le hge with heq | hlt
        · rw [← heq, hbottom]
          exact C.closed_core_compact.isClosed.isOpen_compl
        · rw [hgtret ⟨hlt, hrL⟩]
          exact (C.isCompact_end_neck_lower_cut ⟨hlt, hrL⟩).isClosed.isOpen_compl
      exact hopen.mem_nhds hr
  · intro r hr
    by_cases hhi : L < r
    · exact Filter.Eventually.of_forall fun y => (hbounds y).2.trans_lt hhi
    · have hLr : -L < r := (hbounds x).1.trans_lt hr
      have hle : r ≤ L := le_of_not_gt hhi
      have hopen : IsOpen (H ⁻¹' Iio r) := by
        rcases eq_or_lt_of_le hle with heq | hlt
        · rw [heq, htop]
          exact C.carrier_open
        · rw [hltret ⟨hLr, hlt⟩]
          exact (C.end_neck_lower_cut_topology ⟨hLr, hlt⟩).2.1
      exact hopen.mem_nhds hr

theorem CapCertificate.exists_attachment_of_inter_eq_end_neck
    (C : CapCertificate g) {X : Set M} (T : EpsilonTubeCertificate g X)
    (hinter : C.carrier ∩ T.carrier = C.end_neck.carrier) :
    ∃ side : Bool, Nonempty (CapTubeAttachment C T side) := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let N := C.end_neck
  let L := C.epsilon⁻¹
  let H : M → ℝ := fun x => if x ∈ N.carrier then (N.coordinate_inverse x).2
    else if x ∈ C.carrier then -L else L
  have hL : 0 < L := inv_pos.mpr C.epsilon_pos
  have hN : N.epsilon = C.epsilon := C.end_neck_epsilon
  have hH : Continuous H := C.continuous_saturated_end_height
  have hNU : N.carrier ⊆ T.carrier := by
    intro x hx
    have hxinter : x ∈ C.carrier ∩ T.carrier := by
      rw [hinter]
      exact hx
    exact hxinter.2
  have hins {x : M} (hx : x ∈ N.carrier) : H x = (N.coordinate_inverse x).2 := by
    simp only [H, if_pos hx]
  have hout {x : M} (hxC : x ∉ C.carrier) : H x = L := by
    have hxN : x ∉ N.carrier := fun hx => hxC (C.end_neck_subset hx)
    simp only [H, if_neg hxN, if_neg hxC]
  have hlower : ∀ x ∈ T.carrier, -L < H x := by
    intro x hxU
    by_cases hxN : x ∈ N.carrier
    · rw [hins hxN]
      simpa only [hN] using (N.coordinate_inverse_mem x hxN).2.1
    · have hxC : x ∉ C.carrier := by
        intro hx
        apply hxN
        have hh : x ∈ C.carrier ∩ T.carrier := ⟨hx, hxU⟩
        rwa [hinter] at hh
      rw [hout hxC]
      linarith
  have happroach : ∀ d ∈ Ioo (-L) 0, ∃ x ∈ T.carrier, H x < d := by
    intro d hd
    obtain ⟨s, hslow, hsd⟩ := exists_between hd.1
    let q := (N.coordinate_inverse N.center).1
    have hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      rw [hN]
      exact ⟨hslow, (hsd.trans hd.2).trans hL⟩
    have hxN := N.coordinate_map_mem (show (q, s) ∈ N.cylinderDomain from ⟨mem_univ _, hs⟩)
    refine ⟨N.coordinate_map (q, s), hNU hxN, ?_⟩
    rw [hins hxN, N.coordinate_inverse_map (q, s) hs]
    exact hsd
  have hlevel : IsCompact (T.carrier ∩ H ⁻¹' ({0} : Set ℝ)) := by
    have heq : T.carrier ∩ H ⁻¹' ({0} : Set ℝ) = N.central_sphere := by
      ext x
      constructor
      · rintro ⟨hxU, hxH⟩
        have hzero : H x = 0 := hxH
        have hxN : x ∈ N.carrier := by
          by_contra hx
          by_cases hxC : x ∈ C.carrier
          · have hh : x ∈ C.carrier ∩ T.carrier := ⟨hxC, hxU⟩
            rw [hinter] at hh
            exact hx hh
          · rw [hout hxC] at hzero
            exact hL.ne' hzero
        apply (N.mem_central_sphere_iff x).mpr
        exact ⟨hxN, by rw [← hins hxN]; exact hzero⟩
      · intro hx
        have hc := (N.mem_central_sphere_iff x).mp hx
        refine ⟨hNU hc.1, ?_⟩
        change H x = 0
        rw [hins hc.1]
        exact hc.2
    rw [heq]
    exact N.isCompact_central_sphere
  obtain ⟨side, a, ha, htail⟩ :=
    T.cylinder.exists_tail_subset_of_compact_level H (neg_lt_zero.mpr hL)
      hH.continuousOn hlower happroach hlevel
  refine ⟨side, ⟨{
    overlap_model := by rw [hinter]; exact N.m25_openCylinderModel
    tube_tail := ⟨a, ha, ?_⟩
    cap_tail := ⟨L / 2, ⟨half_pos hL, by linarith⟩, fun _ hx => hNU hx.1⟩
  }⟩⟩
  intro x hx
  have hh : H x < 0 := (htail hx).2
  by_contra hxC
  rw [hout hxC] at hh
  exact (not_lt_of_ge hL.le) hh

end PoincareConjecture
