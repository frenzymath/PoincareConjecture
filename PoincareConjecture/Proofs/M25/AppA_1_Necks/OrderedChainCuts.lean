import PoincareConjecture.Proofs.M25.AppA_1_Necks.RetainedLevelComponents
import PoincareConjecture.Proofs.M25.AppA_1_Necks.AdjacentCutCover
import Mathlib.Data.Int.Init
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.IntermediateValue











set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.BalancedNeckChain

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ}




theorem exists_ordered_saturated_heights
    (C : BalancedNeckChain g epsilon)
    (hsep : ∀ i ∈ C.shape.active, (C.neck i).IsSeparating) :
    let L := epsilon⁻¹
    let K : ℤ → Set M := fun i => connectedComponent (C.neck i).center
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
    ∃ H : ℤ → M → ℝ,
      (∀ i, i ∉ C.shape.active → ∀ x, H i x = 0) ∧
      (∀ i ∈ C.shape.active,
        Continuous (H i) ∧
        (∀ x ∈ (C.neck i).carrier,
          H i x = ((C.neck i).coordinate_inverse x).2) ∧
        (∀ x ∈ K i \ (C.neck i).carrier, H i x = -L ∨ H i x = L) ∧
        (∀ x y : M,
          ENNReal.ofReal ((C.neck i).scale * Real.sqrt (1 - epsilon) *
            |H i x - H i y|) ≤ g.edist x y)) ∧
      (∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active, K i = K j) ∧
      (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
        (∀ x ∈ (C.neck (i + 1)).carrier, -L / 2 < H i x) ∧
        (∀ x ∈ (C.neck (i + 1)).carrier \ (C.neck i).carrier,
          H i x = L)) ∧
      (∀ i ∈ C.shape.active, ∀ t ∈ Ioo (-L) L,
        A i t = K i ∩ (H i) ⁻¹' Iio t ∧
        B i t = K i ∩ (H i) ⁻¹' Ioi t ∧
        frontier (A i t) = S i t ∧ frontier (B i t) = S i t ∧
        A i t ∪ S i t ∪ B i t = K i) ∧
      (∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active, i < j →
        ∀ s ∈ Ioo (L / 2) L, ∀ t ∈ Ioo (L / 2) L,
          closure (A i s) ⊆ A j t ∧ closure (B j t) ⊆ B i s) := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let L := epsilon⁻¹
  let K : ℤ → Set M := fun i => connectedComponent (C.neck i).center
  let q : ℤ → UnitTwoSphere := fun i =>
    ((C.neck i).coordinate_inverse (C.neck i).center).1
  let S : ℤ → ℝ → Set M := fun i t =>
    range (fun v : UnitTwoSphere => (C.neck i).coordinate_map (v, t))
  let A : ℤ → ℝ → Set M := fun i t =>
    connectedComponentIn (S i t)ᶜ ((C.neck i).coordinate_map (q i, (t - L) / 2))
  let B : ℤ → ℝ → Set M := fun i t =>
    connectedComponentIn (S i t)ᶜ ((C.neck i).coordinate_map (q i, (t + L) / 2))
  obtain ⟨i₀, hi₀⟩ := C.active_nonempty
  have hepos : 0 < epsilon := C.epsilon_eq i₀ hi₀ ▸ (C.neck i₀).epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepos
  have hbetween {i j k : ℤ} (hi : i ∈ C.shape.active) (hj : j ∈ C.shape.active)
      (hik : i ≤ k) (hkj : k ≤ j) : k ∈ C.shape.active := by
    cases hs : C.shape <;>
      simp only [hs, ChainShape.active, mem_Icc, mem_Ici, mem_Iic, mem_univ] at * <;> omega
  have hchoose (i : ℤ) : ∃ H : M → ℝ,
      (i ∉ C.shape.active → ∀ x, H x = 0) ∧
      (i ∈ C.shape.active → Continuous H ∧
        (∀ x ∈ (C.neck i).carrier, H x = ((C.neck i).coordinate_inverse x).2) ∧
        (∀ x ∈ K i \ (C.neck i).carrier, H x = -L ∨ H x = L) ∧
        (∀ x y : M, ENNReal.ofReal ((C.neck i).scale * Real.sqrt (1 - epsilon) *
          |H x - H y|) ≤ g.edist x y)) ∧
      (i ∈ C.shape.active → i + 1 ∈ C.shape.active →
        (∀ x ∈ (C.neck (i + 1)).carrier, -L / 2 < H x) ∧
        (∀ x ∈ (C.neck (i + 1)).carrier \ (C.neck i).carrier, H x = L)) := by
    by_cases hi : i ∈ C.shape.active
    · have hei := C.epsilon_eq i hi
      by_cases hn : i + 1 ∈ C.shape.active
      · obtain ⟨H, hH, hins, hout, hsign, hnext, hdist, _⟩ :=
          (C.neck i).exists_adjacent_saturated_cut_cover (C.neck (i + 1)) (hsep i hi)
            (by simpa only [hei] using (C.overlap_contains_quarters i hi hn).1)
            (fun _ hx => by
              simpa only [hei] using (C.overlap_within_three_quarters i hi hn hx).1)
        refine ⟨H, fun h => False.elim (h hi), fun _ => ?_, fun _ _ => ?_⟩
        · exact ⟨hH, hins, by simpa only [K, L, hei] using hout,
            by simpa only [hei] using hdist⟩
        · exact ⟨by simpa only [L, hei] using hsign, by simpa only [L, hei] using hnext⟩
      · obtain ⟨a₀, b₀, ha₀, hb₀, _, _, _, _, _, hcover⟩ :=
          (C.neck i).exists_opposite_central_components (hsep i hi)
        obtain ⟨H, hH, hins, hminus, hplus, _, hdist⟩ :=
          (C.neck i).exists_saturatedAxialHeight (hsep i hi) a₀ b₀ ha₀ hb₀
        refine ⟨H, fun h => False.elim (h hi), fun _ => ⟨hH, hins, ?_, ?_⟩,
          fun _ h => False.elim (hn h)⟩
        · intro x hx
          have hxK := hx.1
          change x ∈ connectedComponent (C.neck i).center at hxK
          rw [← hcover] at hxK
          rcases hxK with (hxA | hxS) | hxB
          · exact Or.inl (by simpa only [L, hei] using hminus x ⟨hxA, hx.2⟩)
          · exact False.elim (hx.2 ((C.neck i).central_sphere_subset hxS))
          · exact Or.inr (by simpa only [L, hei] using hplus x ⟨hxB, hx.2⟩)
        · simpa only [hei] using hdist
    · exact ⟨fun _ => 0, fun _ _ => rfl, fun h => False.elim (hi h),
        fun h => False.elim (hi h)⟩
  choose H hzero hH hnext using hchoose
  have hKadj {i : ℤ} (hi : i ∈ C.shape.active) (hn : i + 1 ∈ C.shape.active) :
      K i = K (i + 1) := by
    obtain ⟨x, hx, hxn⟩ := C.adjacent_overlap i hi hn
    exact (connectedComponent_eq ((C.neck i).m25_carrier_subset_connectedComponent hx)).trans
      (connectedComponent_eq ((C.neck (i + 1)).m25_carrier_subset_connectedComponent hxn)).symm
  have hKle {i j : ℤ} (hi : i ∈ C.shape.active) (hj : j ∈ C.shape.active)
      (hij : i ≤ j) : K i = K j := by
    refine Int.leInduction (motive := fun k _ => k ∈ C.shape.active → K i = K k)
      (fun _ => rfl) ?_ j hij hj
    intro k hik ih hk
    have hk₀ := hbetween hi hk hik (by omega)
    exact (ih hk₀).trans (hKadj hk₀ hk)
  have hKall (i : ℤ) (hi : i ∈ C.shape.active) (j : ℤ) (hj : j ∈ C.shape.active) :
      K i = K j := (le_total i j).elim (hKle hi hj) (fun h => (hKle hj hi h).symm)
  have hdom (i : ℤ) (hi : i ∈ C.shape.active) {t : ℝ} (ht : t ∈ Ioo (-L) L) :
      t ∈ Ioo (-(C.neck i).epsilon⁻¹) (C.neck i).epsilon⁻¹ := by
    simpa only [C.epsilon_eq i hi] using ht
  have hpoint (i : ℤ) (hi : i ∈ C.shape.active) (v : UnitTwoSphere)
      {t : ℝ} (ht : t ∈ Ioo (-L) L) :
      H i ((C.neck i).coordinate_map (v, t)) = t := by
    rw [(hH i hi).2.1 _ ((C.neck i).coordinate_map_mem ⟨mem_univ _, hdom i hi ht⟩),
      (C.neck i).coordinate_inverse_map (v, t) (hdom i hi ht)]
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
  have hcuts (i : ℤ) (hi : i ∈ C.shape.active) (t : ℝ) (ht : t ∈ Ioo (-L) L) :
      A i t = K i ∩ (H i) ⁻¹' Iio t ∧ B i t = K i ∩ (H i) ⁻¹' Ioi t ∧
      frontier (A i t) = S i t ∧ frontier (B i t) = S i t ∧
      A i t ∪ S i t ∪ B i t = K i := by
    have hm : (t - L) / 2 ∈ Ioo (-L) L := by constructor <;> linarith [ht.1, ht.2]
    have hp : (t + L) / 2 ∈ Ioo (-L) L := by constructor <;> linarith [ht.1, ht.2]
    have hmr : (C.neck i).coordinate_map (q i, (t - L) / 2) ∈
        (C.neck i).region (-(C.neck i).epsilon⁻¹) t := by
      refine ⟨(C.neck i).coordinate_map_mem ⟨mem_univ _, hdom i hi hm⟩, ?_⟩
      rw [(C.neck i).coordinate_inverse_map _ (hdom i hi hm)]
      exact ⟨(hdom i hi hm).1, by linarith [ht.1]⟩
    have hpr : (C.neck i).coordinate_map (q i, (t + L) / 2) ∈
        (C.neck i).region t (C.neck i).epsilon⁻¹ := by
      refine ⟨(C.neck i).coordinate_map_mem ⟨mem_univ _, hdom i hi hp⟩, ?_⟩
      rw [(C.neck i).coordinate_inverse_map _ (hdom i hi hp)]
      exact ⟨by linarith [ht.2], (hdom i hi hp).2⟩
    obtain ⟨a₀, b₀, _, _, hn, hpos, _, hfa, hfb, hcover⟩ :=
      (C.neck i).exists_opposite_retained_components (hsep i hi) (hdom i hi ht)
    have heA : connectedComponentIn (S i t)ᶜ a₀ = A i t := connectedComponentIn_eq (hn hmr)
    have heB : connectedComponentIn (S i t)ᶜ b₀ = B i t := connectedComponentIn_eq (hpos hpr)
    change frontier (connectedComponentIn (S i t)ᶜ a₀) = S i t at hfa
    change frontier (connectedComponentIn (S i t)ᶜ b₀) = S i t at hfb
    change connectedComponentIn (S i t)ᶜ a₀ ∪ S i t ∪
      connectedComponentIn (S i t)ᶜ b₀ = K i at hcover
    rw [heA] at hfa
    rw [heB] at hfb
    rw [heA, heB] at hcover
    have hAK {x : M} (hx : x ∈ A i t) : x ∈ K i := hcover ▸ Or.inl (Or.inl hx)
    have hBK {x : M} (hx : x ∈ B i t) : x ∈ K i := hcover ▸ Or.inr hx
    have hneg : ∀ x ∈ A i t, H i x < t := by
      intro x hx
      apply isPreconnected_connectedComponentIn.gt_of_ne (hH i hi).1.continuousOn _ _ hx
      · intro y hy heq
        exact connectedComponentIn_subset _ _ hy ((hlevel i hi ht (hAK hy)).mp heq)
      · refine ⟨(C.neck i).coordinate_map (q i, (t - L) / 2), ?_, ?_⟩
        · change (C.neck i).coordinate_map (q i, (t - L) / 2) ∈ A i t
          exact heA ▸ hn hmr
        · rw [hpoint i hi _ hm]
          linarith [ht.1]
    have hpositive : ∀ x ∈ B i t, t < H i x := by
      intro x hx
      apply isPreconnected_connectedComponentIn.lt_of_ne (hH i hi).1.continuousOn _ _ hx
      · intro y hy heq
        exact connectedComponentIn_subset _ _ hy ((hlevel i hi ht (hBK hy)).mp heq)
      · refine ⟨(C.neck i).coordinate_map (q i, (t + L) / 2), ?_, ?_⟩
        · change (C.neck i).coordinate_map (q i, (t + L) / 2) ∈ B i t
          exact heB ▸ hpos hpr
        · rw [hpoint i hi _ hp]
          linarith [ht.2]
    refine ⟨?_, ?_, hfa, hfb, hcover⟩
    · ext x
      constructor
      · intro hx
        exact ⟨hAK hx, hneg x hx⟩
      · rintro ⟨hxK, hxH⟩
        rcases hcover.symm ▸ hxK with (hxA | hxS) | hxB
        · exact hxA
        · exact False.elim (hxH.ne ((hlevel i hi ht hxK).mpr hxS))
        · exact False.elim (lt_asymm hxH (hpositive x hxB))
    · ext x
      constructor
      · intro hx
        exact ⟨hBK hx, hpositive x hx⟩
      · rintro ⟨hxK, hxH⟩
        rcases hcover.symm ▸ hxK with (hxA | hxS) | hxB
        · exact False.elim (lt_asymm hxH (hneg x hxA))
        · exact False.elim (hxH.ne ((hlevel i hi ht hxK).mpr hxS).symm)
        · exact hxB
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
  have hretained {s : ℝ} (hs : s ∈ Ioo (L / 2) L) : s ∈ Ioo (-L) L :=
    ⟨by linarith [hs.1], hs.2⟩
  have hadj (i : ℤ) (hi : i ∈ C.shape.active) (hn : i + 1 ∈ C.shape.active)
      (s : ℝ) (hs : s ∈ Ioo (L / 2) L) (t : ℝ) (ht : t ∈ Ioo (L / 2) L) :
      closure (A i s) ⊆ A (i + 1) t ∧ closure (B (i + 1) t) ⊆ B i s := by
    obtain ⟨ha, hb, hfa, _, _⟩ := hcuts i hi s (hretained hs)
    obtain ⟨hna, _, _, _, _⟩ := hcuts (i + 1) hn t (hretained ht)
    have hSA : S i s ⊆ A (i + 1) t := by
      rintro x ⟨v, rfl⟩
      have hxold := (C.neck i).coordinate_map_mem (z := (v, s))
        ⟨mem_univ v, hdom i hi (hretained hs)⟩
      have hxreg : (C.neck i).coordinate_map (v, s) ∈ (C.neck i).region (L / 2) L := by
        refine ⟨hxold, ?_⟩
        rw [(C.neck i).coordinate_inverse_map _ (hdom i hi (hretained hs))]
        exact hs
      have hxnew := (C.overlap_contains_quarters i hi hn).1 hxreg
      rw [hna]
      refine ⟨(C.neck (i + 1)).m25_carrier_subset_connectedComponent hxnew, ?_⟩
      change H (i + 1) ((C.neck i).coordinate_map (v, s)) < t
      rw [(hH (i + 1) hn).2.1 _ hxnew]
      exact (C.overlap_within_three_quarters i hi hn ⟨hxold, hxnew⟩).2.2.2.trans ht.1
    have hSB : S (i + 1) t ⊆ B i s := by
      rintro x ⟨v, rfl⟩
      have hxnew := (C.neck (i + 1)).coordinate_map_mem (z := (v, t))
        ⟨mem_univ v, hdom (i + 1) hn (hretained ht)⟩
      have hxout : (C.neck (i + 1)).coordinate_map (v, t) ∉ (C.neck i).carrier := by
        intro hxold
        have h := (C.overlap_within_three_quarters i hi hn ⟨hxold, hxnew⟩).2.2.2
        rw [(C.neck (i + 1)).coordinate_inverse_map _ (hdom (i + 1) hn (hretained ht))] at h
        exact lt_asymm ht.1 h
      rw [hb]
      refine ⟨(hKadj hi hn).symm ▸ (C.neck (i + 1)).m25_carrier_subset_connectedComponent hxnew, ?_⟩
      change s < H i ((C.neck (i + 1)).coordinate_map (v, t))
      rw [(hnext i hi hn).2 _ ⟨hxnew, hxout⟩]
      exact hs.2
    have hopen : IsOpen (A (i + 1) t) := by
      rw [hna]
      exact isOpen_connectedComponent.inter (isOpen_Iio.preimage (hH (i + 1) hn).1)
    have hpS : (C.neck i).coordinate_map (q i, s) ∈ S i s := mem_range_self _
    have hpcl : (C.neck i).coordinate_map (q i, s) ∈ closure (A i s) :=
      frontier_subset_closure (hfa.symm ▸ hpS)
    obtain ⟨w, hwn, hwi⟩ := mem_closure_iff.mp hpcl _ hopen (hSA hpS)
    have hsign : ∀ x ∈ A i s, H (i + 1) x < t := by
      intro x hx
      apply isPreconnected_connectedComponentIn.gt_of_ne (hH (i + 1) hn).1.continuousOn _ _ hx
      · intro y hy heq
        change y ∈ A i s at hy
        have hyi := ha ▸ hy
        have hyS := (hlevel (i + 1) hn (hretained ht) ((hKadj hi hn) ▸ hyi.1)).mp heq
        have hyB := hb ▸ hSB hyS
        exact lt_asymm (show H i y < s from hyi.2) (show s < H i y from hyB.2)
      · exact ⟨w, hwi, (hna ▸ hwn).2⟩
    have hac : closure (A i s) ⊆ A (i + 1) t := by
      rw [closure_eq_self_union_frontier, hfa]
      rintro x (hx | hx)
      · rw [hna]
        exact ⟨(hKadj hi hn) ▸ (ha ▸ hx).1, hsign x hx⟩
      · exact hSA hx
    refine ⟨hac, ?_⟩
    intro x hx
    have hxnext := (hclosure (i + 1) hn t (hretained ht)).2 ▸ hx
    have hxK : x ∈ K i := (hKadj hi hn).symm ▸ hxnext.1
    rw [hb]
    refine ⟨hxK, ?_⟩
    change s < H i x
    by_contra hnot
    have hxold : x ∈ closure (A i s) :=
      (hclosure i hi s (hretained hs)).1.symm ▸ ⟨hxK, le_of_not_gt hnot⟩
    exact (not_lt_of_ge (show t ≤ H (i + 1) x from hxnext.2))
      (show H (i + 1) x < t from (hna ▸ hac hxold).2)
  have hmid : 3 * L / 4 ∈ Ioo (L / 2) L := by constructor <;> linarith
  have hordered (i : ℤ) (hi : i ∈ C.shape.active) (j : ℤ) (hj : j ∈ C.shape.active)
      (hij : i < j) (s : ℝ) (hs : s ∈ Ioo (L / 2) L)
      (t : ℝ) (ht : t ∈ Ioo (L / 2) L) :
      closure (A i s) ⊆ A j t ∧ closure (B j t) ⊆ B i s := by
    let P (k : ℤ) := ∀ s ∈ Ioo (L / 2) L, ∀ t ∈ Ioo (L / 2) L,
      closure (A i s) ⊆ A k t ∧ closure (B k t) ⊆ B i s
    have hP : P j := by
      refine Int.leInduction (m := i + 1)
        (motive := fun k _ => k ∈ C.shape.active → P k) ?_ ?_ j (by omega) hj
      · intro hn
        exact hadj i hi hn
      · intro k hik ih hk₁ s hs t ht
        have hk : k ∈ C.shape.active := hbetween hi hk₁ (by omega) (by omega)
        have hprev := ih hk s hs (3 * L / 4) hmid
        have hsucc := hadj k hk hk₁ (3 * L / 4) hmid t ht
        exact ⟨hprev.1.trans (subset_closure.trans hsucc.1),
          hsucc.2.trans (subset_closure.trans hprev.2)⟩
    exact hP s hs t ht
  exact ⟨H, hzero, hH, hKall, hnext, hcuts, hordered⟩

end PoincareConjecture.BalancedNeckChain
