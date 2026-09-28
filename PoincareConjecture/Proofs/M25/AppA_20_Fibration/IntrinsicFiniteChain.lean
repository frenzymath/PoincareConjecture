import PoincareConjecture.Proofs.M25.AppA_1_Necks.FiniteChainFrontier
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.Basic













set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

open Classical in



theorem BalancedNeckChain.continuousOn_initial_height_of_finite
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (C : BalancedNeckChain g epsilon) {a b : ℤ}
    (hshape : C.shape = ChainShape.finite a b) :
    let L := epsilon⁻¹
    let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
    let H : M → ℝ := fun x =>
      if x ∈ (C.neck a).carrier then
        ((C.neck a).coordinate_inverse x).2 else L
    ContinuousOn H U ∧
      (∀ x ∈ U, H x ∈ Ioc (-L) L) ∧
      (∀ t ∈ Ioo (-L) L,
        U ∩ H ⁻¹' {t} =
          range (fun q : UnitTwoSphere =>
            (C.neck a).coordinate_map (q, t))) := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L := epsilon⁻¹
  let N := C.neck a
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let F : M → ℝ := fun x =>
    if x ∈ N.carrier then (N.coordinate_inverse x).2 else L
  change ContinuousOn F U ∧ (∀ x ∈ U, F x ∈ Ioc (-L) L) ∧
    (∀ t ∈ Ioo (-L) L,
      U ∩ F ⁻¹' {t} = range (fun q : UnitTwoSphere => N.coordinate_map (q, t)))
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by
    rw [hshape]
    rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact ((hactive i).mp hi).1.trans ((hactive i).mp hi).2
  have ha : a ∈ C.shape.active := (hactive a).mpr ⟨le_rfl, hab⟩
  have he : N.epsilon = epsilon := C.epsilon_eq a ha
  have hepos : 0 < epsilon := he ▸ N.epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepos
  have hFin (x : M) (hx : x ∈ N.carrier) :
      F x = (N.coordinate_inverse x).2 := by
    simp only [F, if_pos hx]
  have hFout (x : M) (hx : x ∉ N.carrier) : F x = L := by
    simp only [F, if_neg hx]
  have hbounds (x : M) : F x ∈ Ioc (-L) L := by
    by_cases hx : x ∈ N.carrier
    · rw [hFin x hx]
      have hc := (N.coordinate_inverse_mem x hx).2
      rw [he] at hc
      exact ⟨hc.1, hc.2.le⟩
    · rw [hFout x hx]
      exact ⟨by linarith, le_rfl⟩
  have hcont (x : M) (hx : x ∈ U) : ContinuousAt F x := by
    by_cases hxN : x ∈ N.carrier
    · have hc := N.coordinate_inverse_smooth.continuousOn.continuousAt
        (N.carrier_open.mem_nhds hxN)
      apply hc.snd.congr_of_eventuallyEq
      filter_upwards [N.carrier_open.mem_nhds hxN] with y hy
      exact hFin y hy
    · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
      have haj : a < j := by
        have hja : a ≤ j := ((hactive j).mp hj).1
        have hne : j ≠ a := by
          intro h
          apply hxN
          simpa only [h] using hxj
        omega
      obtain ⟨c, hc, hdisjoint⟩ :=
        C.later_disjoint_negative_end a ha j hj haj
      change Filter.Tendsto F (𝓝 x) (𝓝 (F x))
      rw [hFout x hxN]
      apply tendsto_order.mpr
      constructor
      · intro d hd
        let K := N.coordinate_map '' (univ ×ˢ Icc c d)
        have hKclosed : IsClosed K := by
          apply (N.isCompact_coordinate_slab ?_ ?_).isClosed
          · rw [he]
            exact hc.1
          · rw [he]
            exact hd
        have hKsub : K ⊆ N.carrier := by
          rintro y ⟨z, hz, rfl⟩
          apply N.coordinate_map_mem
          refine ⟨mem_univ _, ?_, ?_⟩ <;> rw [he]
          · exact hc.1.trans_le hz.2.1
          · exact hz.2.2.trans_lt hd
        have hxK : x ∉ K := fun h => hxN (hKsub h)
        filter_upwards [((C.neck j).carrier_open.inter
          hKclosed.isOpen_compl).mem_nhds ⟨hxj, hxK⟩] with y hy
        by_cases hyN : y ∈ N.carrier
        · rw [hFin y hyN]
          have hcy : c ≤ (N.coordinate_inverse y).2 := by
            by_contra h
            have hyc : (N.coordinate_inverse y).2 < c := lt_of_not_ge h
            have hycoord := (N.coordinate_inverse_mem y hyN).2
            rw [he] at hycoord
            exact (Set.disjoint_left.mp hdisjoint) hy.1 ⟨hyN, hycoord.1, hyc⟩
          by_contra h
          exact hy.2 ⟨N.coordinate_inverse y,
            ⟨mem_univ _, hcy, le_of_not_gt h⟩, N.coordinate_map_inverse hyN⟩
        · rw [hFout y hyN]
          exact hd
      · intro d hd
        exact Filter.Eventually.of_forall fun y => (hbounds y).2.trans_lt hd
  refine ⟨continuousOn_of_forall_continuousAt hcont, ?_, ?_⟩
  · intro x _
    exact hbounds x
  · intro t ht
    apply Set.Subset.antisymm
    · intro x hx
      have hFx : F x = t := hx.2
      have hxN : x ∈ N.carrier := by
        by_contra h
        rw [hFout x h] at hFx
        exact (ne_of_lt ht.2) hFx.symm
      have hheight : (N.coordinate_inverse x).2 = t := by
        rw [← hFin x hxN]
        exact hFx
      refine ⟨(N.coordinate_inverse x).1, ?_⟩
      have hz : ((N.coordinate_inverse x).1, t) = N.coordinate_inverse x := by
        apply Prod.ext
        · rfl
        · exact hheight.symm
      change N.coordinate_map ((N.coordinate_inverse x).1, t) = x
      rw [hz]
      exact N.coordinate_map_inverse hxN
    · rintro x ⟨q, rfl⟩
      have htN : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
        rw [he]
        exact ht
      have hxN := N.coordinate_map_mem (show (q, t) ∈
        univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from ⟨mem_univ _, htN⟩)
      refine ⟨mem_iUnion₂.mpr ⟨a, ha, hxN⟩, ?_⟩
      change F (N.coordinate_map (q, t)) = t
      rw [hFin _ hxN, N.coordinate_inverse_map (q, t) htN]




theorem NeckOnlyCover.exists_positive_frontier_center_on_complementary_path
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (H : NeckOnlyCover g) (hwhole : H.X = Set.univ)
    (C : BalancedNeckChain g H.epsilon) {a b : ℤ}
    (hshape : C.shape = ChainShape.finite a b)
    (hsource : C.source_necks = H.necks)
    (hquarters : ∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
      closure ((C.neck i).region (H.epsilon⁻¹ / 2) H.epsilon⁻¹) ⊆
          (C.neck (i + 1)).carrier ∧
        closure ((C.neck (i + 1)).region
          (-H.epsilon⁻¹) (-H.epsilon⁻¹ / 2)) ⊆ (C.neck i).carrier)
    (q : UnitTwoSphere)
    (γ : Path
      ((C.neck a).coordinate_map (q, -H.epsilon⁻¹ / 2))
      ((C.neck a).coordinate_map (q, H.epsilon⁻¹ / 2)))
    (hγ : ∀ t, γ t ∉ (C.neck a).central_sphere) :
    let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
    ∃ N' : EpsilonNeck g,
      N' ∈ C.source_necks ∧ N'.epsilon = H.epsilon ∧
      N'.center ∈ Set.range γ ∧ N'.center ∈ frontier U ∧
      N'.center ∉ U ∧
      N'.center ∈ closure ((C.neck b).region 0 H.epsilon⁻¹) := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L := H.epsilon⁻¹
  let N := C.neck a
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let F : M → ℝ := fun x =>
    if x ∈ N.carrier then (N.coordinate_inverse x).2 else L
  change ∃ N' : EpsilonNeck g,
    N' ∈ C.source_necks ∧ N'.epsilon = H.epsilon ∧
    N'.center ∈ range γ ∧ N'.center ∈ frontier U ∧
    N'.center ∉ U ∧ N'.center ∈ closure ((C.neck b).region 0 L)
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by
    rw [hshape]
    rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact ((hactive i).mp hi).1.trans ((hactive i).mp hi).2
  have ha : a ∈ C.shape.active := (hactive a).mpr ⟨le_rfl, hab⟩
  have he : N.epsilon = H.epsilon := C.epsilon_eq a ha
  have hL : 0 < L := inv_pos.mpr H.epsilon_pos
  have hheight := C.continuousOn_initial_height_of_finite hshape
  change ContinuousOn F U ∧ (∀ x ∈ U, F x ∈ Ioc (-L) L) ∧
    (∀ t ∈ Ioo (-L) L,
      U ∩ F ⁻¹' {t} = range (fun r : UnitTwoSphere => N.coordinate_map (r, t)))
    at hheight
  obtain ⟨hF, _, hlevel⟩ := hheight
  have hUopen : IsOpen U :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => (C.neck i).carrier_open
  have hpoint (t : ℝ) (ht : t ∈ Ioo (-L) L) :
      N.coordinate_map (q, t) ∈ U ∧ F (N.coordinate_map (q, t)) = t := by
    have htN : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      rw [he]
      exact ht
    have hc := N.coordinate_map_mem (show (q, t) ∈
      univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from ⟨mem_univ _, htN⟩)
    refine ⟨mem_iUnion₂.mpr ⟨a, ha, hc⟩, ?_⟩
    simp only [F, if_pos hc, N.coordinate_inverse_map (q, t) htN]
  have hplus := hpoint (L / 2) (by constructor <;> linarith)
  have hminus := hpoint (-L / 2) (by constructor <;> linarith)
  let V : Set M := U ∩ F ⁻¹' Ioi 0
  have hVopen : IsOpen V := hF.isOpen_inter_preimage hUopen isOpen_Ioi
  have hmeet : (range γ ∩ V).Nonempty := by
    refine ⟨N.coordinate_map (q, L / 2), γ.target_mem_range, hplus.1, ?_⟩
    change 0 < F (N.coordinate_map (q, L / 2))
    rw [hplus.2]
    linarith
  have hnot : ¬ range γ ⊆ V := by
    intro h
    have hm : 0 < F (N.coordinate_map (q, -L / 2)) := (h γ.source_mem_range).2
    rw [hminus.2] at hm
    linarith
  have hescape : ¬ closure V ∩ range γ ⊆ V := by
    intro hsub
    exact hnot ((isConnected_range γ.continuous).2.subset_of_closure_inter_subset
      hVopen hmeet hsub)
  obtain ⟨y, hy, hyV⟩ := Set.not_subset.mp hescape
  have hyout : y ∉ U := by
    intro hyU
    have hnonneg : 0 ≤ F y := by
      by_contra h
      have hneg : F y < 0 := lt_of_not_ge h
      let W : Set M := U ∩ F ⁻¹' Iio 0
      have hWopen : IsOpen W := hF.isOpen_inter_preimage hUopen isOpen_Iio
      obtain ⟨z, hzW, hzV⟩ := mem_closure_iff.mp hy.1 W hWopen ⟨hyU, hneg⟩
      have hzneg : F z < 0 := hzW.2
      have hzpos : 0 < F z := hzV.2
      exact lt_asymm hzneg hzpos
    have hne : F y ≠ 0 := by
      intro hzero
      have hz := hlevel 0 (show (0 : ℝ) ∈ Ioo (-L) L by constructor <;> linarith)
      have hymem : y ∈ range (fun r : UnitTwoSphere => N.coordinate_map (r, 0)) := by
        rw [← hz]
        exact ⟨hyU, hzero⟩
      obtain ⟨r, hr⟩ := hymem
      have h0N : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := N.zero_mem_interval
      have hc := N.coordinate_map_mem (show (r, (0 : ℝ)) ∈
        univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from ⟨mem_univ _, h0N⟩)
      have hs : N.coordinate_map (r, 0) ∈ N.central_sphere := by
        apply (N.mem_central_sphere_iff _).mpr
        refine ⟨hc, ?_⟩
        rw [N.coordinate_inverse_map (r, 0) h0N]
      obtain ⟨t, ht⟩ := hy.2
      apply hγ t
      rw [ht, ← hr]
      exact hs
    have hpos : 0 < F y := by
      rcases lt_or_eq_of_le hnonneg with h | h
      · exact h
      · exact (hne h.symm).elim
    exact hyV ⟨hyU, hpos⟩
  have hyfront : y ∈ frontier U := by
    rw [hUopen.frontier_eq]
    exact ⟨closure_mono (show V ⊆ U from inter_subset_left) hy.1, hyout⟩
  have hout (i : ℤ) (hi : i ∈ C.shape.active) : y ∉ (C.neck i).carrier := by
    intro h
    exact hyout (mem_iUnion₂.mpr ⟨i, hi, h⟩)
  have hcover : V ⊆ N.region 0 L ∪ ⋃ i ∈ Ioc a b, (C.neck i).carrier := by
    intro x hx
    by_cases hxN : x ∈ N.carrier
    · left
      have hpos : 0 < (N.coordinate_inverse x).2 := by
        have hxpos : 0 < F x := hx.2
        simpa only [F, if_pos hxN] using hxpos
      have hc := (N.coordinate_inverse_mem x hxN).2
      rw [he] at hc
      exact ⟨hxN, hpos, hc.2⟩
    · right
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx.1
      have hai := ((hactive i).mp hi).1
      have hib := ((hactive i).mp hi).2
      have hne : i ≠ a := by
        intro h
        apply hxN
        simpa only [h] using hxi
      exact mem_iUnion₂.mpr ⟨i, ⟨by omega, hib⟩, hxi⟩
  have hycover := closure_mono hcover hy.1
  rw [closure_union, (Set.finite_Ioc a b).closure_biUnion] at hycover
  have hyend : y ∈ closure ((C.neck b).region 0 L) := by
    rcases hycover with hyfirst | hylater
    · by_cases hab' : a = b
      · simpa only [N, hab'] using hyfirst
      · have hnext : a + 1 ∈ C.shape.active :=
          (hactive _).mpr (by constructor <;> omega)
        let K := N.coordinate_map '' (univ ×ˢ Icc (0 : ℝ) (L / 2))
        have hKclosed : IsClosed K := by
          apply (N.isCompact_coordinate_slab ?_ ?_).isClosed
          · rw [he]
            change -L < 0
            linarith
          · rw [he]
            change L / 2 < L
            linarith
        have hKsub : K ⊆ N.carrier := by
          rintro x ⟨z, hz, rfl⟩
          apply N.coordinate_map_mem
          refine ⟨mem_univ _, ?_, ?_⟩ <;> rw [he]
          · change -L < z.2
            linarith [hz.2.1]
          · change z.2 < L
            linarith [hz.2.2]
        have hfirstCover : N.region 0 L ⊆ K ∪ N.region (L / 2) L := by
          intro x hx
          by_cases hpos : L / 2 < (N.coordinate_inverse x).2
          · exact Or.inr ⟨hx.1, hpos, hx.2.2⟩
          · exact Or.inl ⟨N.coordinate_inverse x,
              ⟨mem_univ _, hx.2.1.le, le_of_not_gt hpos⟩,
              N.coordinate_map_inverse hx.1⟩
        have hparts := closure_mono hfirstCover hyfirst
        rw [closure_union, hKclosed.closure_eq] at hparts
        rcases hparts with hyK | hypos
        · exact (hout a ha (hKsub hyK)).elim
        · exact (hout (a + 1) hnext ((hquarters a ha hnext).1 hypos)).elim
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hylater
      have hailt : a < i := hi.1
      have hible : i ≤ b := hi.2
      have hia : i ∈ C.shape.active := (hactive i).mpr ⟨hi.1.le, hi.2⟩
      have hei : (C.neck i).epsilon = H.epsilon := C.epsilon_eq i hia
      let K := (C.neck i).coordinate_map '' (univ ×ˢ Icc (-L / 2) (L / 2))
      have hKclosed : IsClosed K := by
        apply ((C.neck i).isCompact_coordinate_slab ?_ ?_).isClosed
        · rw [hei]
          change -L < -L / 2
          linarith
        · rw [hei]
          change L / 2 < L
          linarith
      have hKsub : K ⊆ (C.neck i).carrier := by
        rintro x ⟨z, hz, rfl⟩
        apply (C.neck i).coordinate_map_mem
        refine ⟨mem_univ _, ?_, ?_⟩ <;> rw [hei]
        · change -L < z.2
          linarith [hz.2.1]
        · change z.2 < L
          linarith [hz.2.2]
      have hpieces : (C.neck i).carrier ⊆
          K ∪ (C.neck i).region (-L) (-L / 2) ∪ (C.neck i).region (L / 2) L := by
        intro x hx
        have hc := ((C.neck i).coordinate_inverse_mem x hx).2
        rw [hei] at hc
        by_cases hneg : ((C.neck i).coordinate_inverse x).2 < -L / 2
        · exact Or.inl (Or.inr ⟨hx, hc.1, hneg⟩)
        by_cases hpos : L / 2 < ((C.neck i).coordinate_inverse x).2
        · exact Or.inr ⟨hx, hpos, hc.2⟩
        exact Or.inl (Or.inl ⟨(C.neck i).coordinate_inverse x,
          ⟨mem_univ _, le_of_not_gt hneg, le_of_not_gt hpos⟩,
          (C.neck i).coordinate_map_inverse hx⟩)
      have hparts := closure_mono hpieces hyi
      rw [closure_union, closure_union, hKclosed.closure_eq] at hparts
      rcases hparts with (hyK | hyneg) | hypos
      · exact (hout i hia (hKsub hyK)).elim
      · have hprev : i - 1 ∈ C.shape.active :=
          (hactive _).mpr (by constructor <;> omega)
        have hnext : i - 1 + 1 ∈ C.shape.active := by simpa using hia
        have hsub := (hquarters (i - 1) hprev hnext).2
        exact (hout (i - 1) hprev (hsub (by simpa using hyneg))).elim
      · have hib : i = b := by
          by_contra hne
          have hnext : i + 1 ∈ C.shape.active :=
            (hactive _).mpr (by constructor <;> omega)
          exact hout (i + 1) hnext ((hquarters i hia hnext).1 hypos)
        rw [hib] at hypos
        have hsub : (C.neck b).region (L / 2) L ⊆ (C.neck b).region 0 L := by
          intro x hx
          exact ⟨hx.1, by linarith [hx.2.1], hx.2.2⟩
        exact closure_mono hsub hypos
  obtain ⟨N', hN', hcenter⟩ := H.pointwise_center_cover y (by rw [hwhole]; exact mem_univ _)
  refine ⟨N', hsource.symm ▸ hN', H.neck_epsilon N' hN', ?_, ?_, ?_, ?_⟩
  · simpa only [hcenter] using hy.2
  · simpa only [hcenter] using hyfront
  · simpa only [hcenter] using hyout
  · simpa only [hcenter] using hyend

end PoincareConjecture
