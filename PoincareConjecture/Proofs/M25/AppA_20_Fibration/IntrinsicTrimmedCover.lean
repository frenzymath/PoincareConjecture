import PoincareConjecture.Proofs.M25.AppA_20_Fibration.IntrinsicCuts
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval










set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

open Classical in


theorem BalancedNeckChain.intrinsic_trimmed_cut_cover
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (C : BalancedNeckChain g epsilon) {a0 b0 : ℤ}
    (hshape : C.shape = ChainShape.finite a0 b0) :
    let L := epsilon⁻¹
    let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
    ∀ (F : ℤ → M → ℝ),
      (∀ i ∈ C.shape.active,
        ContinuousOn (F i) U ∧
        (∀ x ∈ (C.neck i).carrier,
          F i x = ((C.neck i).coordinate_inverse x).2) ∧
        (∀ x ∈ U, x ∉ (C.neck i).carrier →
          F i x = -L ∨ F i x = L)) →
      ∀ a b : ℝ, L / 2 < a → a < b → b < L →
        let q : ℤ → UnitTwoSphere := fun i =>
          ((C.neck i).coordinate_inverse (C.neck i).center).1
        let S : ℤ → ℝ → Set M := fun i t =>
          range (fun v : UnitTwoSphere => (C.neck i).coordinate_map (v, t))
        let A : ℤ → ℝ → Set M := fun i t =>
          connectedComponentIn (U \ S i t)
            ((C.neck i).coordinate_map (q i, (t - L) / 2))
        let B : ℤ → ℝ → Set M := fun i t =>
          connectedComponentIn (U \ S i t)
            ((C.neck i).coordinate_map (q i, (t + L) / 2))
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
  classical
  let L := epsilon⁻¹
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  dsimp only
  intro F hF a b ha hab hb
  let q : ℤ → UnitTwoSphere := fun i =>
    ((C.neck i).coordinate_inverse (C.neck i).center).1
  let S : ℤ → ℝ → Set M := fun i t =>
    range (fun v : UnitTwoSphere => (C.neck i).coordinate_map (v, t))
  let A : ℤ → ℝ → Set M := fun i t => connectedComponentIn (U \ S i t)
    ((C.neck i).coordinate_map (q i, (t - L) / 2))
  let B : ℤ → ℝ → Set M := fun i t => connectedComponentIn (U \ S i t)
    ((C.neck i).coordinate_map (q i, (t + L) / 2))
  obtain ⟨i₀, hi₀⟩ := C.active_nonempty
  have hepos : 0 < epsilon := C.epsilon_eq i₀ hi₀ ▸ (C.neck i₀).epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepos
  have haL : a ∈ Ioo (L / 2) L := ⟨ha, hab.trans hb⟩
  have hbL : b ∈ Ioo (L / 2) L := ⟨ha.trans hab, hb⟩
  have hret {t : ℝ} (ht : t ∈ Ioo (L / 2) L) : t ∈ Ioo (-L) L :=
    ⟨by linarith [ht.1], ht.2⟩
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a0 b0 := by
    rw [hshape]
    rfl
  have hbetween {i j k : ℤ} (hi : i ∈ C.shape.active) (hj : j ∈ C.shape.active)
      (hik : i ≤ k) (hkj : k ≤ j) : k ∈ C.shape.active :=
    (hactive k).mpr ⟨((hactive i).mp hi).1.trans hik,
      hkj.trans ((hactive j).mp hj).2⟩
  have hNU (i : ℤ) (hi : i ∈ C.shape.active) : (C.neck i).carrier ⊆ U :=
    fun _ hx => mem_iUnion₂.mpr ⟨i, hi, hx⟩
  obtain ⟨_, _, hnext, hcuts, horder⟩ :=
    C.intrinsic_ordered_cuts_of_relative_heights hshape F hF
  have hcut (i : ℤ) (hi : i ∈ C.shape.active) (t : ℝ) (ht : t ∈ Ioo (-L) L) :
      A i t = U ∩ (F i) ⁻¹' Iio t ∧ B i t = U ∩ (F i) ⁻¹' Ioi t ∧
      IsOpen (A i t) ∧ IsOpen (B i t) ∧
      U ∩ closure (A i t) = U ∩ (F i) ⁻¹' Iic t ∧
      U ∩ closure (B i t) = U ∩ (F i) ⁻¹' Ici t := by
    obtain ⟨_, hAi, hBi, hAo, hBo, _, _, _, hAc, hBc, _⟩ := hcuts i hi t ht
    exact ⟨hAi, hBi, hAo, hBo, hAc, hBc⟩
  change ∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active, i < j →
    ∀ s ∈ Ioo (L / 2) L, ∀ t ∈ Ioo (L / 2) L,
      U ∩ closure (A i s) ⊆ A j t ∧ U ∩ closure (B j t) ⊆ B i s at horder
  have hdom (i : ℤ) (hi : i ∈ C.shape.active) {t : ℝ} (ht : t ∈ Ioo (-L) L) :
      t ∈ Ioo (-(C.neck i).epsilon⁻¹) (C.neck i).epsilon⁻¹ := by
    simpa only [C.epsilon_eq i hi] using ht
  have hpoint (i : ℤ) (hi : i ∈ C.shape.active) (v : UnitTwoSphere)
      {t : ℝ} (ht : t ∈ Ioo (-L) L) :
      F i ((C.neck i).coordinate_map (v, t)) = t := by
    rw [(hF i hi).2.1 _ ((C.neck i).coordinate_map_mem ⟨mem_univ _, hdom i hi ht⟩),
      (C.neck i).coordinate_inverse_map (v, t) (hdom i hi ht)]
  have hleft {i j : ℤ} (hi : i ∈ C.shape.active) (hj : j ∈ C.shape.active)
      (hij : i < j) {s t : ℝ} (hs : s ∈ Ioo (L / 2) L) (ht : t ∈ Ioo (L / 2) L)
      {x : M} (hxU : x ∈ U) (hx : F i x ≤ s) : F j x < t := by
    have hc : x ∈ U ∩ closure (A i s) :=
      (hcut i hi s (hret hs)).2.2.2.2.1.symm ▸ ⟨hxU, hx⟩
    exact (show x ∈ U ∩ (F j) ⁻¹' Iio t from
      (hcut j hj t (hret ht)).1 ▸ (horder i hi j hj hij s hs t ht).1 hc).2
  have hright {i j : ℤ} (hi : i ∈ C.shape.active) (hj : j ∈ C.shape.active)
      (hij : i < j) {s t : ℝ} (hs : s ∈ Ioo (L / 2) L) (ht : t ∈ Ioo (L / 2) L)
      {x : M} (hxU : x ∈ U) (hx : t ≤ F j x) : s < F i x := by
    have hc : x ∈ U ∩ closure (B j t) :=
      (hcut j hj t (hret ht)).2.2.2.2.2.symm ▸ ⟨hxU, hx⟩
    exact (show x ∈ U ∩ (F i) ⁻¹' Ioi s from
      (hcut i hi s (hret hs)).2.1 ▸ (horder i hi j hj hij s hs t ht).2 hc).2
  let W : ℤ → Set M := fun i => if i ∈ C.shape.active then
    ((C.neck i).carrier ∩ (if i - 1 ∈ C.shape.active then B (i - 1) a else univ)) ∩
      (if i + 1 ∈ C.shape.active then A i b else univ) else ∅
  have hWmem {i : ℤ} (hi : i ∈ C.shape.active) {x : M} :
      x ∈ W i ↔ x ∈ (C.neck i).carrier ∧
        (i - 1 ∈ C.shape.active → a < F (i - 1) x) ∧
        (i + 1 ∈ C.shape.active → F i x < b) := by
    rw [show W i = _ from if_pos hi]
    constructor
    · intro hx
      refine ⟨hx.1.1, ?_, ?_⟩
      · intro hp
        have hxB : x ∈ B (i - 1) a := by simpa only [if_pos hp] using hx.1.2
        exact (show x ∈ U ∩ (F (i - 1)) ⁻¹' Ioi a from
          (hcut (i - 1) hp a (hret haL)).2.1 ▸ hxB).2
      · intro hn
        have hxA : x ∈ A i b := by simpa only [if_pos hn] using hx.2
        exact (show x ∈ U ∩ (F i) ⁻¹' Iio b from
          (hcut i hi b (hret hbL)).1 ▸ hxA).2
    · rintro ⟨hxc, hp, hn⟩
      refine ⟨⟨hxc, ?_⟩, ?_⟩
      · split_ifs with hi₁
        · rw [(hcut (i - 1) hi₁ a (hret haL)).2.1]
          exact ⟨hNU i hi hxc, hp hi₁⟩
        · exact mem_univ _
      · split_ifs with hi₁
        · rw [(hcut i hi b (hret hbL)).1]
          exact ⟨hNU i hi hxc, hn hi₁⟩
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
        · exact (hcut (i - 1) hp a (hret haL)).2.2.2.1
        · exact isOpen_univ
      · split_ifs with hn
        · exact (hcut i hi b (hret hbL)).2.2.1
        · exact isOpen_univ
    · simpa only [W, if_neg hi] using isOpen_empty
  have hWnonempty (i : ℤ) (hi : i ∈ C.shape.active) : (W i).Nonempty := by
    let c := (a + b) / 2
    have hc : c ∈ Ioo (-L) L := by constructor <;> dsimp only [c] <;> linarith
    let x := (C.neck i).coordinate_map (q i, c)
    have hxc : x ∈ (C.neck i).carrier :=
      (C.neck i).coordinate_map_mem ⟨mem_univ _, hdom i hi hc⟩
    have hFx : F i x = c := hpoint i hi _ hc
    refine ⟨x, (hWmem hi).mpr ⟨hxc, ?_, ?_⟩⟩
    · intro hp
      apply hright hp hi (by omega) haL haL (hNU i hi hxc)
      rw [hFx]
      dsimp only [c]
      linarith
    · intro _
      rw [hFx]
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
      rw [← (hF i hi).2.1 _ hxc]
      exact ⟨hxlo, hxhi hn⟩
    · intro hx
      have hxF : a < F i x ∧ F i x < b := by
        rw [(hF i hi).2.1 _ hx.1]
        exact hx.2
      have hxnew := (C.overlap_contains_quarters i hi hn).1
        (show x ∈ (C.neck i).region (L / 2) L from
          ⟨hx.1, ha.trans hx.2.1, hx.2.2.trans hb⟩)
      refine ⟨(hWmem hi).mpr ⟨hx.1, ?_, fun _ => hxF.2⟩,
        (hWmem hn).mpr ⟨hxnew, ?_, ?_⟩⟩
      · intro hp
        exact hright hp hi (by omega) haL haL (hNU i hi hx.1) hxF.1.le
      · intro _
        simpa only [add_sub_cancel_right] using hxF.1
      · intro _
        rw [(hF (i + 1) hn).2.1 _ hxnew]
        exact (C.overlap_within_three_quarters i hi hn ⟨hx.1, hxnew⟩).2.2.2.trans hbL.1
  have hWdisjoint (i : ℤ) (hi : i ∈ C.shape.active) (j : ℤ) (hj : j ∈ C.shape.active)
      (hij : i + 1 < j) : Disjoint (W i) (W j) := by
    apply disjoint_left.mpr
    intro x hxi hxj
    have hn : i + 1 ∈ C.shape.active := hbetween hi hj (by omega) (by omega)
    have hp : j - 1 ∈ C.shape.active := hbetween hi hj (by omega) (by omega)
    obtain ⟨hxjc, hxjlo, _⟩ := (hWmem hj).mp hxj
    have hxlarge := hright hi hp (by omega) hbL haL (hNU j hj hxjc) (hxjlo hp).le
    exact lt_asymm (((hWmem hi).mp hxi).2.2 hn) hxlarge
  have hcover : (⋃ i : ℤ, W i) = U := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨i, hWactive hxi, hWsub hxi⟩
    · intro x hx
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
      have hxU : x ∈ U := hNU k hk hxk
      by_cases hforward : k + 1 ∈ C.shape.active ∧ b ≤ F k x
      · have hn := hforward.1
        have hxin := (C.neck k).coordinate_inverse_mem x hxk
        have hxnext := (C.overlap_contains_quarters k hk hn).1
          (show x ∈ (C.neck k).region (L / 2) L from ⟨hxk,
            by rw [← (hF k hk).2.1 _ hxk]; exact hbL.1.trans_le hforward.2,
            by simpa only [C.epsilon_eq k hk] using hxin.2.2⟩)
        refine mem_iUnion.mpr ⟨k + 1, (hWmem hn).mpr ⟨hxnext, ?_, ?_⟩⟩
        · intro _
          simpa only [add_sub_cancel_right] using hab.trans_le hforward.2
        · intro _
          rw [(hF (k + 1) hn).2.1 _ hxnext]
          exact (C.overlap_within_three_quarters k hk hn ⟨hxk, hxnext⟩).2.2.2.trans hbL.1
      · have houtk : k + 1 ∈ C.shape.active → F k x < b := by
          intro hn
          exact lt_of_not_ge (fun h => hforward ⟨hn, h⟩)
        let E : Set ℤ := {i | i ∈ C.shape.active ∧ i < k ∧ F i x ≤ a}
        have hEfinite : E.Finite := by
          apply (Set.finite_Icc a0 b0).subset
          intro i hi
          exact (hactive i).mp hi.1
        let Ek : Finset ℤ := hEfinite.toFinset ∪ {k}
        have hkEk : k ∈ Ek := Finset.mem_union_right _ (Finset.mem_singleton_self _)
        let j := Ek.min' ⟨k, hkEk⟩
        have hjEk : j ∈ Ek := Finset.min'_mem _ _
        have hjle : j ≤ k := Finset.min'_le _ _ hkEk
        have hmin : ∀ r ∈ Ek, j ≤ r := fun r hr => Finset.min'_le _ _ hr
        have hjcases : j ∈ E ∨ j = k := by
          simpa only [Ek, Finset.mem_union, Set.Finite.mem_toFinset,
            Finset.mem_singleton] using hjEk
        have hj : j ∈ C.shape.active := hjcases.elim (fun h => h.1) (fun h => h ▸ hk)
        have hjF : j < k → F j x ≤ a := by
          intro hjk
          rcases hjcases with h | h
          · exact h.2.2
          · omega
        have hrF (r : ℤ) (hjr : j ≤ r) (hrk : r < k) : F r x ≤ a := by
          by_cases heq : j = r
          · subst r
            exact hjF hrk
          · have hr : r ∈ C.shape.active := hbetween hj hk hjr hrk.le
            exact (hleft hj hr (by omega) haL haL hxU (hjF (by omega))).le
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
            have hlow := hrF (r - 1) hjr (by omega)
            change F (r - 1) x = L at hex
            linarith [haL.2]
          exact hdesc j hjle le_rfl
        refine mem_iUnion.mpr ⟨j, (hWmem hj).mpr ⟨hxj, ?_, ?_⟩⟩
        · intro hp
          by_contra hn
          have hm : j - 1 ∈ E := ⟨hp, by omega, le_of_not_gt hn⟩
          have hmem : j - 1 ∈ Ek := Finset.mem_union_left _ (hEfinite.mem_toFinset.mpr hm)
          have h := hmin (j - 1) hmem
          omega
        · intro hn
          by_cases heq : j = k
          · rw [heq]
            exact houtk (by simpa only [heq] using hn)
          · exact (hjF (by omega)).trans_lt hab
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

end PoincareConjecture
