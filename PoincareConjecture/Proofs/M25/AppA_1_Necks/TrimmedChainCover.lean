import PoincareConjecture.Proofs.M25.AppA_1_Necks.LocallyFiniteChainCuts
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace PoincareConjecture.BalancedNeckChain

open Classical in

theorem exists_trimmed_cut_cover :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon), epsilon ≤ epsilon0 →
      (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
      ∀ a b : ℝ, epsilon⁻¹ / 2 < a → a < b → b < epsilon⁻¹ →
        let L := epsilon⁻¹
        let q : ℤ → UnitTwoSphere := fun i =>
          ((C.neck i).coordinate_inverse (C.neck i).center).1
        let S : ℤ → ℝ → Set M := fun i t =>
          range (fun v : UnitTwoSphere => (C.neck i).coordinate_map (v, t))
        let A : ℤ → ℝ → Set M := fun i t =>
          connectedComponentIn (S i t)ᶜ
            ((C.neck i).coordinate_map (q i, (t - L) / 2))
        let B : ℤ → ℝ → Set M := fun i t =>
          connectedComponentIn (S i t)ᶜ
            ((C.neck i).coordinate_map (q i, (t + L) / 2))
        let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
        ∃ W : ℤ → Set M,
          (∀ i, i ∉ C.shape.active → W i = ∅) ∧
          (∀ i ∈ C.shape.active,
            W i = ((C.neck i).carrier ∩
              (if i - 1 ∈ C.shape.active then B (i - 1) a else univ)) ∩
              (if i + 1 ∈ C.shape.active then A i b else univ)) ∧
          (∀ i : ℤ, IsOpen (W i)) ∧
          (∀ i ∈ C.shape.active, (W i).Nonempty) ∧
          (⋃ i : ℤ, W i) = U ∧
          (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
            W i ∩ W (i + 1) = (C.neck i).region a b) ∧
          (∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active, i + 1 < j →
            Disjoint (W i) (W j)) ∧
          LocallyFinite (fun i : {i : ℤ // i ∈ C.shape.active} =>
            {x : U | x.1 ∈ W i.1}) := by
  obtain ⟨epsilon0, he0, hecap, hfinite⟩ := exists_locallyFinite_retained_slabs.{u}
  refine ⟨epsilon0, he0, hecap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C he hsep a b ha hab hb
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let L := epsilon⁻¹
  let K : ℤ → Set M := fun i => connectedComponent (C.neck i).center
  let q : ℤ → UnitTwoSphere := fun i =>
    ((C.neck i).coordinate_inverse (C.neck i).center).1
  let S : ℤ → ℝ → Set M := fun i t =>
    range (fun v : UnitTwoSphere => (C.neck i).coordinate_map (v, t))
  let A : ℤ → ℝ → Set M := fun i t => connectedComponentIn (S i t)ᶜ
    ((C.neck i).coordinate_map (q i, (t - L) / 2))
  let B : ℤ → ℝ → Set M := fun i t => connectedComponentIn (S i t)ᶜ
    ((C.neck i).coordinate_map (q i, (t + L) / 2))
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  obtain ⟨i₀, hi₀⟩ := C.active_nonempty
  have hepos : 0 < epsilon := C.epsilon_eq i₀ hi₀ ▸ (C.neck i₀).epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepos
  have haL : a ∈ Ioo (L / 2) L := ⟨ha, hab.trans hb⟩
  have hbL : b ∈ Ioo (L / 2) L := ⟨ha.trans hab, hb⟩
  have hret {t : ℝ} (ht : t ∈ Ioo (L / 2) L) : t ∈ Ioo (-L) L :=
    ⟨by linarith [ht.1], ht.2⟩
  have hbetween {i j k : ℤ} (hi : i ∈ C.shape.active) (hj : j ∈ C.shape.active)
      (hik : i ≤ k) (hkj : k ≤ j) : k ∈ C.shape.active := by
    cases hs : C.shape <;>
      simp only [hs, ChainShape.active, mem_Icc, mem_Ici, mem_Iic, mem_univ] at * <;> omega
  obtain ⟨H, _, hH, hK, hnext, hcuts, horder⟩ := C.exists_ordered_saturated_heights hsep
  change ∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active, K i = K j at hK
  change ∀ i ∈ C.shape.active, ∀ t ∈ Ioo (-L) L,
    A i t = K i ∩ (H i) ⁻¹' Iio t ∧ B i t = K i ∩ (H i) ⁻¹' Ioi t ∧
    frontier (A i t) = S i t ∧ frontier (B i t) = S i t ∧
    A i t ∪ S i t ∪ B i t = K i at hcuts
  change ∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active, i < j →
    ∀ s ∈ Ioo (L / 2) L, ∀ t ∈ Ioo (L / 2) L,
      closure (A i s) ⊆ A j t ∧ closure (B j t) ⊆ B i s at horder
  have hdom (i : ℤ) (hi : i ∈ C.shape.active) {t : ℝ} (ht : t ∈ Ioo (-L) L) :
      t ∈ Ioo (-(C.neck i).epsilon⁻¹) (C.neck i).epsilon⁻¹ := by
    simpa only [C.epsilon_eq i hi] using ht
  have hpoint (i : ℤ) (hi : i ∈ C.shape.active) (v : UnitTwoSphere)
      {t : ℝ} (ht : t ∈ Ioo (-L) L) :
      H i ((C.neck i).coordinate_map (v, t)) = t := by
    rw [(hH i hi).2.1 _ ((C.neck i).coordinate_map_mem ⟨mem_univ _, hdom i hi ht⟩),
      (C.neck i).coordinate_inverse_map _ (hdom i hi ht)]
  have hSK (i : ℤ) (hi : i ∈ C.shape.active) {t : ℝ} (ht : t ∈ Ioo (-L) L) :
      S i t ⊆ K i := by
    rintro _ ⟨v, rfl⟩
    exact (C.neck i).m25_carrier_subset_connectedComponent
      ((C.neck i).coordinate_map_mem ⟨mem_univ _, hdom i hi ht⟩)
  have hlevel (i : ℤ) (hi : i ∈ C.shape.active) {t : ℝ} (ht : t ∈ Ioo (-L) L)
      {x : M} (hx : x ∈ K i) : H i x = t ↔ x ∈ S i t := by
    constructor
    · intro heq
      by_cases hc : x ∈ (C.neck i).carrier
      · have hcoord := (hH i hi).2.1 x hc
        refine ⟨((C.neck i).coordinate_inverse x).1, ?_⟩
        rw [heq] at hcoord
        rw [hcoord]
        exact (C.neck i).coordinate_map_inverse hc
      · rcases (hH i hi).2.2.1 x ⟨hx, hc⟩ with hn | hp <;> linarith [ht.1, ht.2]
    · rintro ⟨v, rfl⟩
      exact hpoint i hi v ht
  have hclosure (i : ℤ) (hi : i ∈ C.shape.active) (t : ℝ) (ht : t ∈ Ioo (-L) L) :
      closure (A i t) = K i ∩ (H i) ⁻¹' Iic t ∧
      closure (B i t) = K i ∩ (H i) ⁻¹' Ici t := by
    obtain ⟨ha, hb, hfa, hfb, _⟩ := hcuts i hi t ht
    constructor
    · rw [closure_eq_self_union_frontier, hfa]
      ext x
      constructor
      · rintro (hx | hx)
        · have hx' := ha ▸ hx
          exact ⟨hx'.1, (show H i x < t from hx'.2).le⟩
        · exact ⟨hSK i hi ht hx, ((hlevel i hi ht (hSK i hi ht hx)).mpr hx).le⟩
      · rintro ⟨hxK, hxH⟩
        change H i x ≤ t at hxH
        rcases hxH.eq_or_lt with heq | hlt
        · exact Or.inr ((hlevel i hi ht hxK).mp heq)
        · exact Or.inl (ha.symm ▸ ⟨hxK, hlt⟩)
    · rw [closure_eq_self_union_frontier, hfb]
      ext x
      constructor
      · rintro (hx | hx)
        · have hx' := hb ▸ hx
          exact ⟨hx'.1, (show t < H i x from hx'.2).le⟩
        · exact ⟨hSK i hi ht hx, ((hlevel i hi ht (hSK i hi ht hx)).mpr hx).ge⟩
      · rintro ⟨hxK, hxH⟩
        change t ≤ H i x at hxH
        rcases hxH.eq_or_lt with heq | hlt
        · exact Or.inr ((hlevel i hi ht hxK).mp heq.symm)
        · exact Or.inl (hb.symm ▸ ⟨hxK, hlt⟩)
  have hleft {i j : ℤ} (hi : i ∈ C.shape.active) (hj : j ∈ C.shape.active)
      (hij : i < j) {s t : ℝ} (hs : s ∈ Ioo (L / 2) L) (ht : t ∈ Ioo (L / 2) L)
      {x : M} (hxK : x ∈ K i) (hx : H i x ≤ s) : H j x < t := by
    have hc : x ∈ closure (A i s) := (hclosure i hi s (hret hs)).1.symm ▸ ⟨hxK, hx⟩
    exact (show x ∈ K j ∩ (H j) ⁻¹' Iio t from
      (hcuts j hj t (hret ht)).1 ▸ (horder i hi j hj hij s hs t ht).1 hc).2
  have hright {i j : ℤ} (hi : i ∈ C.shape.active) (hj : j ∈ C.shape.active)
      (hij : i < j) {s t : ℝ} (hs : s ∈ Ioo (L / 2) L) (ht : t ∈ Ioo (L / 2) L)
      {x : M} (hxK : x ∈ K j) (hx : t ≤ H j x) : s < H i x := by
    have hc : x ∈ closure (B j t) := (hclosure j hj t (hret ht)).2.symm ▸ ⟨hxK, hx⟩
    exact (show x ∈ K i ∩ (H i) ⁻¹' Ioi s from
      (hcuts i hi s (hret hs)).2.1 ▸ (horder i hi j hj hij s hs t ht).2 hc).2
  let W : ℤ → Set M := fun i => if i ∈ C.shape.active then
    ((C.neck i).carrier ∩ (if i - 1 ∈ C.shape.active then B (i - 1) a else univ)) ∩
      (if i + 1 ∈ C.shape.active then A i b else univ) else ∅
  have hWmem {i : ℤ} (hi : i ∈ C.shape.active) {x : M} :
      x ∈ W i ↔ x ∈ (C.neck i).carrier ∧
        (i - 1 ∈ C.shape.active → a < H (i - 1) x) ∧
        (i + 1 ∈ C.shape.active → H i x < b) := by
    rw [show W i = _ from if_pos hi]
    constructor
    · intro hx
      refine ⟨hx.1.1, ?_, ?_⟩
      · intro hp
        have hxB : x ∈ B (i - 1) a := by simpa only [if_pos hp] using hx.1.2
        exact (show x ∈ K (i - 1) ∩ (H (i - 1)) ⁻¹' Ioi a from
          (hcuts (i - 1) hp a (hret haL)).2.1 ▸ hxB).2
      · intro hn
        have hxA : x ∈ A i b := by simpa only [if_pos hn] using hx.2
        exact (show x ∈ K i ∩ (H i) ⁻¹' Iio b from
          (hcuts i hi b (hret hbL)).1 ▸ hxA).2
    · rintro ⟨hxc, hp, hn⟩
      refine ⟨⟨hxc, ?_⟩, ?_⟩
      · split_ifs with hi₁
        · rw [(hcuts (i - 1) hi₁ a (hret haL)).2.1]
          exact ⟨hK i hi (i - 1) hi₁ ▸ (C.neck i).m25_carrier_subset_connectedComponent hxc,
            hp hi₁⟩
        · exact mem_univ _
      · split_ifs with hi₁
        · rw [(hcuts i hi b (hret hbL)).1]
          exact ⟨(C.neck i).m25_carrier_subset_connectedComponent hxc, hn hi₁⟩
        · exact mem_univ _
  have hWactive {i : ℤ} {x : M} (hx : x ∈ W i) : i ∈ C.shape.active := by
    by_contra hi
    simp only [W, if_neg hi, mem_empty_iff_false] at hx
  have hWsub {i : ℤ} {x : M} (hx : x ∈ W i) : x ∈ (C.neck i).carrier :=
    ((hWmem (hWactive hx)).mp hx).1
  have hWopen (i : ℤ) : IsOpen (W i) := by
    by_cases hi : i ∈ C.shape.active
    · dsimp only [W]
      rw [if_pos hi]
      apply IsOpen.inter
      · apply (C.neck i).carrier_open.inter
        split_ifs with hp
        · rw [(hcuts (i - 1) hp a (hret haL)).2.1]
          exact isOpen_connectedComponent.inter (isOpen_Ioi.preimage (hH (i - 1) hp).1)
        · exact isOpen_univ
      · split_ifs with hn
        · rw [(hcuts i hi b (hret hbL)).1]
          exact isOpen_connectedComponent.inter (isOpen_Iio.preimage (hH i hi).1)
        · exact isOpen_univ
    · simpa only [W, if_neg hi] using isOpen_empty
  have hWnonempty (i : ℤ) (hi : i ∈ C.shape.active) : (W i).Nonempty := by
    let c := (a + b) / 2
    have hc : c ∈ Ioo (-L) L := by constructor <;> dsimp only [c] <;> linarith
    let x := (C.neck i).coordinate_map (q i, c)
    have hxc : x ∈ (C.neck i).carrier :=
      (C.neck i).coordinate_map_mem ⟨mem_univ _, hdom i hi hc⟩
    have hHx : H i x = c := hpoint i hi _ hc
    refine ⟨x, (hWmem hi).mpr ⟨hxc, ?_, ?_⟩⟩
    · intro hp
      apply hright hp hi (by omega) haL haL
        ((C.neck i).m25_carrier_subset_connectedComponent hxc)
      rw [hHx]
      dsimp only [c]
      linarith
    · intro _
      rw [hHx]
      dsimp only [c]
      linarith
  have hWadj (i : ℤ) (hi : i ∈ C.shape.active) (hn : i + 1 ∈ C.shape.active) :
      W i ∩ W (i + 1) = (C.neck i).region a b := by
    ext x
    constructor
    · rintro ⟨hxi, hxn⟩
      obtain ⟨hxc, _, hxhi⟩ := (hWmem hi).mp hxi
      have hxlo := ((hWmem hn).mp hxn).2.1 (by simpa only [add_sub_cancel_right] using hi)
      simp only [add_sub_cancel_right] at hxlo
      refine ⟨hxc, ?_⟩
      rw [← (hH i hi).2.1 _ hxc]
      exact ⟨hxlo, hxhi hn⟩
    · intro hx
      have hxH : a < H i x ∧ H i x < b := by
        rw [(hH i hi).2.1 _ hx.1]
        exact hx.2
      have hxnew := (C.overlap_contains_quarters i hi hn).1
        (show x ∈ (C.neck i).region (L / 2) L from
          ⟨hx.1, ha.trans hx.2.1, hx.2.2.trans hb⟩)
      refine ⟨(hWmem hi).mpr ⟨hx.1, ?_, fun _ => hxH.2⟩,
        (hWmem hn).mpr ⟨hxnew, ?_, ?_⟩⟩
      · intro hp
        exact hright hp hi (by omega) haL haL
          ((C.neck i).m25_carrier_subset_connectedComponent hx.1) hxH.1.le
      · intro _
        simpa only [add_sub_cancel_right] using hxH.1
      · intro _
        rw [(hH (i + 1) hn).2.1 _ hxnew]
        exact (C.overlap_within_three_quarters i hi hn ⟨hx.1, hxnew⟩).2.2.2.trans hbL.1
  have hWdisjoint (i : ℤ) (hi : i ∈ C.shape.active) (j : ℤ) (hj : j ∈ C.shape.active)
      (hij : i + 1 < j) : Disjoint (W i) (W j) := by
    apply disjoint_left.mpr
    intro x hxi hxj
    have hn : i + 1 ∈ C.shape.active := hbetween hi hj (by omega) (by omega)
    have hp : j - 1 ∈ C.shape.active := hbetween hi hj (by omega) (by omega)
    obtain ⟨hxjc, hxjlo, _⟩ := (hWmem hj).mp hxj
    have hxK : x ∈ K (j - 1) :=
      hK j hj (j - 1) hp ▸ (C.neck j).m25_carrier_subset_connectedComponent hxjc
    have hxlarge := hright hi hp (by omega) hbL haL hxK (hxjlo hp).le
    exact lt_asymm (((hWmem hi).mp hxi).2.2 hn) hxlarge
  have hcover : (⋃ i : ℤ, W i) = U := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨i, hWactive hxi, hWsub hxi⟩
    · intro x hx
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
      by_cases hforward : k + 1 ∈ C.shape.active ∧ b ≤ H k x
      · have hn := hforward.1
        have hxin := (C.neck k).coordinate_inverse_mem x hxk
        have hxnext := (C.overlap_contains_quarters k hk hn).1
          (show x ∈ (C.neck k).region (L / 2) L from ⟨hxk,
            by rw [← (hH k hk).2.1 _ hxk]; exact hbL.1.trans_le hforward.2,
            by simpa only [C.epsilon_eq k hk] using hxin.2.2⟩)
        refine mem_iUnion.mpr ⟨k + 1, (hWmem hn).mpr ⟨hxnext, ?_, ?_⟩⟩
        · intro _
          simpa only [add_sub_cancel_right] using hab.trans_le hforward.2
        · intro _
          rw [(hH (k + 1) hn).2.1 _ hxnext]
          exact (C.overlap_within_three_quarters k hk hn ⟨hxk, hxnext⟩).2.2.2.trans hbL.1
      · have houtk : k + 1 ∈ C.shape.active → H k x < b := by
          intro hn
          exact lt_of_not_ge (fun h => hforward ⟨hn, h⟩)
        let sx := ((C.neck k).coordinate_inverse x).2
        have hsx : sx ∈ Ioo (-L) L := by
          simpa only [C.epsilon_eq k hk] using ((C.neck k).coordinate_inverse_mem x hxk).2
        let P := (C.neck k).coordinate_map '' (univ ×ˢ Icc (min sx b) (max sx b))
        have hPdom : univ ×ˢ Icc (min sx b) (max sx b) ⊆ (C.neck k).cylinderDomain := by
          rintro z ⟨_, hz⟩
          refine ⟨mem_univ _, hdom k hk ⟨?_, ?_⟩⟩
          · exact (lt_min hsx.1 (hret hbL).1).trans_le hz.1
          · exact hz.2.trans_lt (max_lt hsx.2 hb)
        have hPcompact : IsCompact P := (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
          ((C.neck k).coordinate_map_smooth.continuousOn.mono hPdom)
        have hPconnected : IsConnected P :=
          (isConnected_univ.prod (isConnected_Icc min_le_max)).image _
            ((C.neck k).coordinate_map_smooth.continuousOn.mono hPdom)
        have hPsub : P ⊆ (C.neck k).carrier := by
          rintro y ⟨z, hz, rfl⟩
          exact (C.neck k).coordinate_map_mem (hPdom hz)
        have hxP : x ∈ P :=
          ⟨(C.neck k).coordinate_inverse x,
            ⟨mem_univ _, min_le_left _ _, le_max_left _ _⟩,
            (C.neck k).coordinate_map_inverse hxk⟩
        let p := (C.neck k).coordinate_map (q k, b)
        have hpP : p ∈ P :=
          ⟨(q k, b), ⟨mem_univ _, min_le_right _ _, le_max_right _ _⟩, rfl⟩
        have hpH : H k p = b := hpoint k hk _ (hret hbL)
        let F : Set ℤ := {i | i ∈ C.shape.active ∧ i < k ∧ H i x ≤ a}
        have hFfinite : F.Finite := by
          let Z := fun i : {i : ℤ // i ∈ C.shape.active} =>
            (C.neck i.1).coordinate_map '' (univ ×ˢ Icc a a)
          have hloc : LocallyFinite Z := hfinite C he hsep a a ha le_rfl haL.2
          have hfin := hloc.finite_nonempty_inter_compact hPcompact
          apply (hfin.image (fun i => i.1)).subset
          intro i hi
          refine ⟨⟨i, hi.1⟩, ?_, rfl⟩
          have hpbig : b < H i p := hright hi.1 hk hi.2.1 hbL hbL
            ((C.neck k).m25_carrier_subset_connectedComponent (hPsub hpP)) hpH.ge
          obtain ⟨y, hyP, hyH⟩ := hPconnected.isPreconnected.intermediate_value hxP hpP
            (hH i hi.1).1.continuousOn (show a ∈ Icc (H i x) (H i p) from
              ⟨hi.2.2, (hab.trans hpbig).le⟩)
          have hyK : y ∈ K i := hK k hk i hi.1 ▸
            (C.neck k).m25_carrier_subset_connectedComponent (hPsub hyP)
          obtain ⟨v, hv⟩ := (hlevel i hi.1 (hret haL) hyK).mp hyH
          refine ⟨y, ?_, hyP⟩
          exact ⟨(v, a), ⟨mem_univ _, le_rfl, le_rfl⟩, hv⟩
        let Fk : Finset ℤ := hFfinite.toFinset ∪ {k}
        have hkFk : k ∈ Fk := Finset.mem_union_right _ (Finset.mem_singleton_self _)
        let j := Fk.min' ⟨k, hkFk⟩
        have hjFk : j ∈ Fk := Finset.min'_mem _ _
        have hjle : j ≤ k := Finset.min'_le _ _ hkFk
        have hmin : ∀ r ∈ Fk, j ≤ r := fun r hr => Finset.min'_le _ _ hr
        have hjcases : j ∈ F ∨ j = k := by
          simpa only [Fk, Finset.mem_union, Set.Finite.mem_toFinset,
            Finset.mem_singleton] using hjFk
        have hj : j ∈ C.shape.active := hjcases.elim (fun h => h.1) (fun h => h ▸ hk)
        have hjH : j < k → H j x ≤ a := by
          intro hjk
          rcases hjcases with h | h
          · exact h.2.2
          · omega
        have hrH (r : ℤ) (hjr : j ≤ r) (hrk : r < k) : H r x ≤ a := by
          by_cases heq : j = r
          · subst r
            exact hjH hrk
          · have hr : r ∈ C.shape.active := hbetween hj hk hjr hrk.le
            have hxK : x ∈ K j := hK k hk j hj ▸
              (C.neck k).m25_carrier_subset_connectedComponent hxk
            exact (hleft hj hr (by omega) haL haL hxK (hjH (by omega))).le
        have hxj : x ∈ (C.neck j).carrier := by
          have hdesc : ∀ r (hrk : r ≤ k), j ≤ r → x ∈ (C.neck r).carrier := by
            refine Int.leInductionDown (m := k)
              (motive := fun r _ => j ≤ r → x ∈ (C.neck r).carrier)
              (fun _ => hxk) ?_
            intro r hrk ih hjr
            have hrc := ih (by omega)
            have hr : r ∈ C.shape.active := hbetween hj hk (by omega) hrk
            have hrprev : r - 1 ∈ C.shape.active := hbetween hj hk hjr (by omega)
            by_contra hxout
            have hex := (hnext (r - 1) hrprev (by simpa only [sub_add_cancel] using hr)).2 x
              ⟨by simpa only [sub_add_cancel] using hrc, hxout⟩
            have hlow := hrH (r - 1) hjr (by omega)
            change H (r - 1) x = L at hex
            linarith [haL.2]
          exact hdesc j hjle le_rfl
        refine mem_iUnion.mpr ⟨j, (hWmem hj).mpr ⟨hxj, ?_, ?_⟩⟩
        · intro hp
          by_contra hn
          have hm : j - 1 ∈ F := ⟨hp, by omega, le_of_not_gt hn⟩
          have hmem : j - 1 ∈ Fk := Finset.mem_union_left _ (hFfinite.mem_toFinset.mpr hm)
          have h := hmin (j - 1) hmem
          omega
        · intro hn
          by_cases heq : j = k
          · rw [heq]
            exact houtk (by simpa only [heq] using hn)
          · exact (hjH (by omega)).trans_lt hab
  have hlocal : LocallyFinite (fun i : {i : ℤ // i ∈ C.shape.active} =>
      {x : U | x.1 ∈ W i.1}) := by
    intro x
    have hxW : (x : M) ∈ ⋃ i : ℤ, W i := hcover.symm ▸ x.property
    obtain ⟨k, hxk⟩ := mem_iUnion.mp hxW
    have hk := hWactive hxk
    let V : Set U := {y | y.1 ∈ W k}
    have hV : IsOpen V := (hWopen k).preimage continuous_subtype_val
    refine ⟨V, hV.mem_nhds hxk, ?_⟩
    have hsmall : {i : {i : ℤ // i ∈ C.shape.active} |
        ({x : U | x.1 ∈ W i.1} ∩ V).Nonempty} ⊆
        (Subtype.val : {i : ℤ // i ∈ C.shape.active} → ℤ) ⁻¹' Icc (k - 1) (k + 1) := by
      intro i hi
      obtain ⟨y, hyi, hyk⟩ := hi
      change k - 1 ≤ i.1 ∧ i.1 ≤ k + 1
      constructor
      · by_contra hn
        exact (disjoint_left.mp (hWdisjoint i.1 i.2 k hk (by omega))) hyi hyk
      · by_contra hn
        exact (disjoint_left.mp (hWdisjoint k hk i.1 i.2 (by omega))) hyk hyi
    exact ((Set.finite_Icc (k - 1) (k + 1)).preimage Subtype.val_injective.injOn).subset hsmall
  exact ⟨W, fun i hi => if_neg hi, fun i hi => if_pos hi,
    hWopen, hWnonempty, hcover, hWadj, hWdisjoint, hlocal⟩

end PoincareConjecture.BalancedNeckChain
