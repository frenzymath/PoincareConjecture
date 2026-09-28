import PoincareConjecture.Proofs.M25.AppA_20_Fibration.FiniteExtensionReturn
import Mathlib.Data.Int.Init










set_option autoImplicit false
open Set
open scoped Manifold ContDiff Bundle ENNReal
universe u
namespace PoincareConjecture




theorem BalancedNeckChain.exists_finite_backward_extension_or_deep_return :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon) {a b : ℤ},
      C.shape = ChainShape.finite a b → epsilon ≤ epsilon0 →
      ∀ (N' : EpsilonNeck g), N' ∈ C.source_necks →
      N'.epsilon = epsilon →
      N'.center ∈ closure ((C.neck a).region (-epsilon⁻¹) 0) →
      N'.center ∉ (⋃ i ∈ C.shape.active, (C.neck i).carrier) →
      (∃ (R : EpsilonNeck g) (D : BalancedNeckChain g epsilon),
        (R = N' ∨ R = N'.reverse) ∧ R.SameUpToReversal N' ∧
        D.shape = ChainShape.finite (a - 1) b ∧
        D.source_necks = C.source_necks ∧
        D.neck = Function.update C.neck (a - 1) R ∧
        closure (R.region (epsilon⁻¹ / 2) epsilon⁻¹) ⊆
          (C.neck a).carrier ∧
        closure ((C.neck a).region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) ⊆
          R.carrier) ∨
      (∀ c ∈ Ioo (0 : ℝ) epsilon⁻¹,
        ¬ Disjoint N'.carrier ((C.neck b).region c epsilon⁻¹)) := by
  classical
  obtain ⟨ee, hepos, hecap, hext⟩ :=
    BalancedNeckChain.exists_finite_forward_extension_or_deep_return.{u}
  obtain ⟨et, htpos, _, htransport⟩ :=
    EpsilonNeck.exists_relative_successor_height_continuity.{u}
  obtain ⟨el, hlpos, _, hlower⟩ := EpsilonNeck.exists_relative_height_lower_control.{u}
  obtain ⟨es, hspos, _, hscale⟩ :=
    EpsilonNeck.exists_intersecting_scale_control.{u} (α := (1 / 1000 : ℝ))
      (by norm_num)
  let B0 : ℝ := Real.sqrt 2 * (Real.pi + 1)
  have hB0 : 0 < B0 := by dsimp only [B0]; positivity
  have hden : 0 < 1000 * (B0 + 1) := by positivity
  refine ⟨min ee (min et (min el (min es
    (min (1 / 1000) (1 / (1000 * (B0 + 1))))))),
    lt_min hepos (lt_min htpos (lt_min hlpos (lt_min hspos
      (lt_min (by norm_num) (div_pos zero_lt_one hden))))),
    (min_le_left _ _).trans hecap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C a b hshape he N' hsource heN' hy hyout
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcomm (x y : M) : g.edist x y = g.edist y x := Manifold.riemannianEDist_comm
  rcases le_min_iff.mp he with ⟨hee, hrest⟩
  rcases le_min_iff.mp hrest with ⟨het, hrest⟩
  rcases le_min_iff.mp hrest with ⟨hel, hrest⟩
  rcases le_min_iff.mp hrest with ⟨hes, hrest⟩
  rcases le_min_iff.mp hrest with ⟨henum, hebudget⟩
  let L : ℝ := epsilon⁻¹
  let A := C.neck a
  let B := C.neck b
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let W : Set M := U ∪ N'.carrier
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by rw [hshape]; rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact ((hactive i).mp hi).1.trans ((hactive i).mp hi).2
  have ha : a ∈ C.shape.active := (hactive a).mpr ⟨le_rfl, hab⟩
  have hb : b ∈ C.shape.active := (hactive b).mpr ⟨hab, le_rfl⟩
  have heA : A.epsilon = epsilon := C.epsilon_eq a ha
  have heB : B.epsilon = epsilon := C.epsilon_eq b hb
  have hepsilonpos : 0 < epsilon := heA ▸ A.epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepsilonpos
  have hNU (i : ℤ) (hi : i ∈ C.shape.active) : (C.neck i).carrier ⊆ U :=
    fun _ hx => mem_iUnion₂.mpr ⟨i, hi, hx⟩
  have hUW : U ⊆ W := subset_union_left
  have hN'W : N'.carrier ⊆ W := subset_union_right
  have hNW (i : ℤ) (hi : i ∈ C.shape.active) : (C.neck i).carrier ⊆ W :=
    (hNU i hi).trans hUW
  have hopenU : IsOpen U :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => (C.neck i).carrier_open
  change N'.center ∈ closure (A.region (-L) 0) at hy
  change N'.center ∉ U at hyout
  by_cases hreturn : ∀ c ∈ Ioo (0 : ℝ) L, ¬ Disjoint N'.carrier (B.region c L)
  · exact Or.inr hreturn
  push Not at hreturn
  obtain ⟨c, hc, hcut⟩ := hreturn
  let G : M → ℝ := fun x => if x ∈ B.carrier then (B.coordinate_inverse x).2 else -L
  have hGin (x : M) (hx : x ∈ B.carrier) : G x = (B.coordinate_inverse x).2 := by
    simp only [G, if_pos hx]
  have hGout (x : M) (hx : x ∉ B.carrier) : G x = -L := by
    simp only [G, if_neg hx]

  have hGU : ContinuousOn G U := by
    let P : ℤ → Prop := fun i => ∃ F : M → ℝ,
      ContinuousOn F U ∧
      (∀ x ∈ (C.neck i).carrier, F x = ((C.neck i).coordinate_inverse x).2) ∧
      (∀ x ∈ U, x ∉ (C.neck i).carrier → F x = -L ∨ F x = L) ∧
      (∀ x ∈ ⋃ k ∈ Icc a i, (C.neck k).carrier,
        x ∉ (C.neck i).carrier → F x = -L)
    have hbase : P a := by
      refine ⟨fun x => if x ∈ A.carrier then (A.coordinate_inverse x).2 else L,
        (C.continuousOn_initial_height_of_finite hshape).1, ?_, ?_, ?_⟩
      · intro x hx
        exact if_pos hx
      · intro x _ hx
        exact Or.inr (if_neg hx)
      · intro x hx hxout
        obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
        have hka : k = a := le_antisymm hk.2 hk.1
        exact False.elim (hxout (by simpa only [hka] using hxk))
    have hstep (i : ℤ) (hi : i ∈ C.shape.active) (hn : i + 1 ∈ C.shape.active)
        (hPi : P i) : P (i + 1) := by
      obtain ⟨F, hFc, hFin, hFout, hFpast⟩ := hPi
      let Fnext : M → ℝ := fun x => if x ∈ (C.neck (i + 1)).carrier then
        ((C.neck (i + 1)).coordinate_inverse x).2
        else if F x < 3 * L / 4 then -L else L
      have htrans := htransport (C.neck i) (C.neck (i + 1))
        (by rw [C.epsilon_eq i hi]; exact het)
        ((C.epsilon_eq (i + 1) hn).trans (C.epsilon_eq i hi).symm)
      simp only [C.epsilon_eq i hi] at htrans
      refine ⟨Fnext, htrans (C.overlap_contains_quarters i hi hn).1
        (C.overlap_within_three_quarters i hi hn) U (hNU i hi) (hNU (i + 1) hn)
        F hFc hFin hFout, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Fnext, if_pos hx]
      · intro x _ hx
        by_cases ht : F x < 3 * L / 4
        · exact Or.inl (by simp only [Fnext, if_neg hx, if_pos ht])
        · exact Or.inr (by simp only [Fnext, if_neg hx, if_neg ht])
      · intro x hx hxout
        obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
        have hkne : k ≠ i + 1 := by
          intro hki
          exact hxout (by simpa only [hki] using hxk)
        have hki : k ≤ i := by have h := hk.2; omega
        have hxpast : x ∈ ⋃ k ∈ Icc a i, (C.neck k).carrier :=
          mem_iUnion₂.mpr ⟨k, ⟨hk.1, hki⟩, hxk⟩
        have hbelow : F x < 3 * L / 4 := by
          by_cases hxold : x ∈ (C.neck i).carrier
          · have hxcoord : ((C.neck i).coordinate_inverse x).2 < L := by
              simpa only [C.epsilon_eq i hi] using
                ((C.neck i).coordinate_inverse_mem x hxold).2.2
            have hhalf : ((C.neck i).coordinate_inverse x).2 ≤ L / 2 := by
              by_contra h
              exact hxout ((C.overlap_contains_quarters i hi hn).1
                ⟨hxold, lt_of_not_ge h, hxcoord⟩)
            rw [hFin x hxold]
            linarith only [hhalf, hL]
          · rw [hFpast x hxpast hxold]
            linarith only [hL]
        simp only [Fnext, if_neg hxout, if_pos hbelow]
    have hPall (i : ℤ) (hi : i ∈ C.shape.active) : P i := by
      refine Int.leInduction (m := a) (motive := fun k _ => k ≤ b → P k)
        (fun _ => hbase) ?_ i ((hactive i).mp hi).1 ((hactive i).mp hi).2
      intro k hak ih hkb
      exact hstep k ((hactive k).mpr ⟨hak, by omega⟩)
        ((hactive (k + 1)).mpr ⟨by omega, hkb⟩) (ih (by omega))
    obtain ⟨F, hFc, hFin, _, hFpast⟩ := hPall b hb
    apply hFc.congr
    intro x hx
    by_cases hxB : x ∈ B.carrier
    · rw [hGin x hxB]
      exact (hFin x hxB).symm
    · rw [hGout x hxB]
      apply (hFpast x ?_ hxB).symm
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨i, (hactive i).mp hi, hxi⟩
  have hGbound (x : M) : -L ≤ G x := by
    by_cases hxB : x ∈ B.carrier
    · rw [hGin x hxB]
      simpa only [heB] using (B.coordinate_inverse_mem x hxB).2.1.le
    · rw [hGout x hxB]
  have hGW : ContinuousOn G W := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    by_cases hxU : x ∈ U
    · exact hGU.continuousAt (hopenU.mem_nhds hxU)
    have hxN' : x ∈ N'.carrier := hx.resolve_left hxU
    have hxB : x ∉ B.carrier := fun h => hxU (hNU b hb h)
    change Filter.Tendsto G (nhds x) (nhds (G x))
    rw [hGout x hxB]
    apply tendsto_order.mpr
    constructor
    · intro d hd
      exact Filter.Eventually.of_forall fun z => hd.trans_le (hGbound z)
    · intro d hd
      let K := B.coordinate_map '' (univ ×ˢ Icc d c)
      have hKclosed : IsClosed K :=
        (B.isCompact_coordinate_slab (by rw [heB]; exact hd)
          (by rw [heB]; exact hc.2)).isClosed
      have hKsub : K ⊆ B.carrier := by
        rintro z ⟨w, hw, rfl⟩
        apply B.coordinate_map_mem
        refine ⟨mem_univ _, ?_, ?_⟩ <;> rw [heB]
        · exact hd.trans_le hw.2.1
        · exact hw.2.2.trans_lt hc.2
      have hxK : x ∉ K := fun h => hxB (hKsub h)
      filter_upwards [(N'.carrier_open.inter hKclosed.isOpen_compl).mem_nhds
        ⟨hxN', hxK⟩] with z hz
      by_cases hzB : z ∈ B.carrier
      · rw [hGin z hzB]
        have hzc : (B.coordinate_inverse z).2 ≤ c := by
          by_contra h
          have hh := (B.coordinate_inverse_mem z hzB).2.2
          rw [heB] at hh
          exact Set.disjoint_left.mp hcut hz.1 ⟨hzB, lt_of_not_ge h, hh⟩
        by_contra h
        exact hz.2 ⟨B.coordinate_inverse z, ⟨mem_univ _, le_of_not_gt h, hzc⟩,
          B.coordinate_map_inverse hzB⟩
      · rw [hGout z hzB]
        exact hd

  let P : ℤ → Prop := fun i => ∃ F : M → ℝ,
    ContinuousOn F W ∧
    (∀ x ∈ (C.neck i).carrier, F x = ((C.neck i).coordinate_inverse x).2) ∧
    (∀ x ∈ W, x ∉ (C.neck i).carrier → F x = -L ∨ F x = L) ∧
    (∀ x ∈ ⋃ k ∈ Icc i b, (C.neck k).carrier,
      x ∉ (C.neck i).carrier → F x = L) ∧
    (∀ x ∈ W, x ∉ U → F x = -L)
  have hbase : P b := by
    refine ⟨G, hGW, hGin, ?_, ?_, ?_⟩
    · intro x _ hx
      exact Or.inl (hGout x hx)
    · intro x hx hxout
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
      have hkb : k = b := le_antisymm hk.2 hk.1
      exact False.elim (hxout (by simpa only [hkb] using hxk))
    · intro x _ hx
      exact hGout x (fun h => hx (hNU b hb h))
  have hback (i : ℤ) (hi : i ∈ C.shape.active) (hn : i + 1 ∈ C.shape.active)
      (hPn : P (i + 1)) : P i := by
    obtain ⟨F, hFc, hFin, hFout, hFfuture, hFoutside⟩ := hPn
    have hei : (C.neck i).reverse.epsilon = epsilon := C.epsilon_eq i hi
    have hen : (C.neck (i + 1)).reverse.epsilon = epsilon := C.epsilon_eq (i + 1) hn
    have hquarter : (C.neck (i + 1)).reverse.region (L / 2) L ⊆
        (C.neck i).reverse.carrier := by
      intro x hx
      apply (C.overlap_contains_quarters i hi hn).2
      change x ∈ (C.neck (i + 1)).carrier ∧
        -L < ((C.neck (i + 1)).coordinate_inverse x).2 ∧
          ((C.neck (i + 1)).coordinate_inverse x).2 < -L / 2
      change x ∈ (C.neck (i + 1)).carrier ∧
        L / 2 < -((C.neck (i + 1)).coordinate_inverse x).2 ∧
          -((C.neck (i + 1)).coordinate_inverse x).2 < L at hx
      exact ⟨hx.1, by linarith only [hx.2.2], by linarith only [hx.2.1]⟩
    have hoverlap : (C.neck (i + 1)).reverse.carrier ∩ (C.neck i).reverse.carrier ⊆
        (C.neck (i + 1)).reverse.region (-L / 2) L ∩
          (C.neck i).reverse.region (-L) (L / 2) := by
      intro x hx
      have h := C.overlap_within_three_quarters i hi hn ⟨hx.2, hx.1⟩
      constructor
      · rw [EpsilonNeck.reverse_region]
        simpa only [neg_div, neg_neg] using h.2
      · rw [EpsilonNeck.reverse_region]
        simpa only [neg_div, neg_neg] using h.1
    have htrans := htransport (C.neck (i + 1)).reverse (C.neck i).reverse
      (by rw [hen]; exact het) (hei.trans hen.symm)
    simp only [hen] at htrans
    have hnegIn : ∀ x ∈ (C.neck (i + 1)).reverse.carrier,
        -F x = ((C.neck (i + 1)).reverse.coordinate_inverse x).2 := by
      intro x hx
      change -F x = -((C.neck (i + 1)).coordinate_inverse x).2
      rw [hFin x hx]
    have hnegOut : ∀ x ∈ W, x ∉ (C.neck (i + 1)).reverse.carrier →
        -F x = -L ∨ -F x = L := by
      intro x hx hxout
      rcases hFout x hx hxout with h | h
      · exact Or.inr (by rw [h]; simp only [neg_neg])
      · exact Or.inl (by rw [h])
    have hHc := htrans hquarter hoverlap W (hNW (i + 1) hn) (hNW i hi)
      (fun x => -F x) hFc.neg hnegIn hnegOut
    change ContinuousOn (fun x => if x ∈ (C.neck i).carrier then
      -((C.neck i).coordinate_inverse x).2 else if -F x < 3 * L / 4 then -L else L) W
      at hHc
    let J : M → ℝ := fun x => if x ∈ (C.neck i).carrier then
      ((C.neck i).coordinate_inverse x).2 else if -F x < 3 * L / 4 then L else -L
    have hJc : ContinuousOn J W := by
      apply hHc.neg.congr
      intro x _
      change J x = -(if x ∈ (C.neck i).carrier then
        -((C.neck i).coordinate_inverse x).2 else if -F x < 3 * L / 4 then -L else L)
      dsimp only [J]
      split_ifs <;> ring
    refine ⟨J, hJc, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [J, if_pos hx]
    · intro x _ hx
      by_cases ht : -F x < 3 * L / 4
      · exact Or.inr (by simp only [J, if_neg hx, if_pos ht])
      · exact Or.inl (by simp only [J, if_neg hx, if_neg ht])
    · intro x hx hxout
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
      have hkne : k ≠ i := by
        intro hki
        exact hxout (by simpa only [hki] using hxk)
      have hki : i + 1 ≤ k := by have h := hk.1; omega
      have hxfuture : x ∈ ⋃ k ∈ Icc (i + 1) b, (C.neck k).carrier :=
        mem_iUnion₂.mpr ⟨k, ⟨hki, hk.2⟩, hxk⟩
      have hbelow : -F x < 3 * L / 4 := by
        by_cases hxnext : x ∈ (C.neck (i + 1)).carrier
        · have hxcoord : -L < ((C.neck (i + 1)).coordinate_inverse x).2 := by
            simpa only [C.epsilon_eq (i + 1) hn] using
              ((C.neck (i + 1)).coordinate_inverse_mem x hxnext).2.1
          have hhalf : -L / 2 ≤ ((C.neck (i + 1)).coordinate_inverse x).2 := by
            by_contra h
            exact hxout ((C.overlap_contains_quarters i hi hn).2
              ⟨hxnext, hxcoord, lt_of_not_ge h⟩)
          rw [hFin x hxnext]
          linarith only [hhalf, hL]
        · rw [hFfuture x hxfuture hxnext]
          linarith only [hL]
      simp only [J, if_neg hxout, if_pos hbelow]
    · intro x hx hxout
      have hxi : x ∉ (C.neck i).carrier := fun h => hxout (hNU i hi h)
      rw [show J x = (if -F x < 3 * L / 4 then L else -L) from if_neg hxi,
        hFoutside x hx hxout]
      simp only [neg_neg, if_neg (by linarith only [hL] : ¬ L < 3 * L / 4)]
  have hPall (i : ℤ) (hi : i ∈ C.shape.active) : P i := by
    refine Int.leInductionDown (m := b) (motive := fun k _ => a ≤ k → P k)
      (fun _ => hbase) ?_ i ((hactive i).mp hi).2 ((hactive i).mp hi).1
    intro k hkb ih hak
    have hprev : k - 1 + 1 = k := by omega
    have hk : k ∈ C.shape.active := (hactive k).mpr ⟨by omega, hkb⟩
    exact hback (k - 1) ((hactive (k - 1)).mpr ⟨hak, by omega⟩)
      (by simpa only [hprev] using hk) (by simpa only [hprev] using ih (by omega))
  obtain ⟨F, hFc, hFin, hFout, hFfuture, hFoutside⟩ := hPall a ha
  have hOldHeight (x : M) (hx : x ∈ U) : -L < F x := by
    by_cases hxA : x ∈ A.carrier
    · rw [hFin x hxA]
      simpa only [heA] using (A.coordinate_inverse_mem x hxA).2.1
    · have hxall : x ∈ ⋃ k ∈ Icc a b, (C.neck k).carrier := by
        obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
        exact mem_iUnion₂.mpr ⟨k, (hactive k).mp hk, hxk⟩
      rw [hFfuture x hxall hxA]
      linarith only [hL]
  have hupper : ∀ x ∈ N'.carrier, F x < L / 5 := by
    have heAr : A.reverse.epsilon = epsilon := heA
    have h := hlower A.reverse N' (by rw [heAr]; exact hel) (heN'.trans heAr.symm)
    simp only [heAr] at h
    have hcenter : -F N'.center = L := by
      rw [hFoutside N'.center
        (hN'W (N'.central_sphere_subset N'.center_on_central_sphere)) hyout]
      exact neg_neg L
    have hlow := h W hN'W (fun x => -F x) hFc.neg (by
      intro x hx
      change -F x = -(A.coordinate_inverse x).2
      rw [hFin x hx]) (by
      intro x hx hxout
      change -F x = -L ∨ -F x = L
      rcases hFout x hx hxout with hh | hh
      · exact Or.inr ((congrArg Neg.neg hh).trans (neg_neg L))
      · exact Or.inl (congrArg Neg.neg hh)) hcenter
    intro x hx
    have hh := hlow x hx
    linarith only [hh]
  have hpositiveCut : Disjoint N'.carrier (A.region (L / 2) L) := by
    apply Set.disjoint_left.mpr
    intro x hx hxa
    have hh := hupper x hx
    rw [hFin x hxa.1] at hh
    linarith only [hh, hxa.2.1, hL]

  have hself : A.reverse.SameUpToReversal A.reverse := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, 1, Or.inl rfl, ?_⟩
    intro z _
    simp only [one_mul]
  have hnoadj (i : ℤ) (hi : i ∈ Icc (0 : ℤ) 0) (hn : i + 1 ∈ Icc (0 : ℤ) 0) :
      False := by
    rcases hi with ⟨hilo, hihi⟩
    rcases hn with ⟨hnlo, hnhi⟩
    omega
  let C0 : BalancedNeckChain g epsilon := {
    shape := .finite 0 0
    neck := fun _ => A.reverse
    source_necks := {A.reverse, N'}
    selected := fun _ _ => ⟨A.reverse, by simp, hself⟩
    active_nonempty := ⟨0, le_rfl, le_rfl⟩
    epsilon_eq := fun _ _ => heA
    centers_distinct := by
      intro i hi j hj hij
      change i ∈ Icc (0 : ℤ) 0 at hi
      change j ∈ Icc (0 : ℤ) 0 at hj
      exact False.elim (hij ((le_antisymm hi.2 hi.1).trans (le_antisymm hj.2 hj.1).symm))
    adjacent_overlap := fun i hi hn => (hnoadj i hi hn).elim
    overlap_contains_quarters := fun i hi hn => (hnoadj i hi hn).elim
    overlap_within_three_quarters := fun i hi hn => (hnoadj i hi hn).elim
    later_disjoint_negative_end := by
      intro i hi j hj hij
      change i ∈ Icc (0 : ℤ) 0 at hi
      change j ∈ Icc (0 : ℤ) 0 at hj
      have hi0 : i = 0 := le_antisymm hi.2 hi.1
      have hj0 : j = 0 := le_antisymm hj.2 hj.1
      omega
    balanced_center_distance := fun i hi hn => (hnoadj i hi hn).elim }
  have hyA : N'.center ∉ A.carrier := fun hx => hyout (hNU a ha hx)
  have hyrev : N'.center ∈ closure (A.reverse.region 0 L) := by
    simpa only [EpsilonNeck.reverse_region, neg_zero] using hy
  have hyC0 : N'.center ∉ ⋃ i ∈ C0.shape.active, (C0.neck i).carrier := by
    intro hx
    obtain ⟨i, _, hxi⟩ := mem_iUnion₂.mp hx
    have hx : N'.center ∈ A.carrier := hxi
    exact hyA hx
  rcases hext C0 (a := 0) (b := 0) rfl hee N' (by simp [C0]) heN' hyrev hyC0
    with hpair | hbad
  swap
  · apply False.elim
    apply hbad (-L / 2) ⟨by linarith only [hL], by linarith only [hL]⟩
    change Disjoint N'.carrier (A.reverse.region (-L) (-L / 2))
    simpa only [EpsilonNeck.reverse_region, neg_div, neg_neg] using hpositiveCut
  obtain ⟨T, E, hTchoice, hTselected, hEshape, _, hEneck, hclosedOld, hclosedNew⟩ := hpair
  have hE0 : E.neck 0 = A.reverse := by
    rw [hEneck]
    exact Function.update_of_ne (by norm_num : (0 : ℤ) ≠ 0 + 1) T C0.neck
  have hE1 : E.neck 1 = T := by
    rw [hEneck]
    exact Function.update_self (0 + 1) T C0.neck
  have hzeroE : (0 : ℤ) ∈ E.shape.active := by rw [hEshape]; change 0 ≤ 0 ∧ 0 ≤ 0 + 1; omega
  have honeE : (1 : ℤ) ∈ E.shape.active := by rw [hEshape]; change 0 ≤ 1 ∧ 1 ≤ 0 + 1; omega
  have hTinter := E.adjacent_overlap 0 hzeroE honeE
  have hToverlap := E.overlap_within_three_quarters 0 hzeroE honeE
  change ((E.neck 0).carrier ∩ (E.neck 1).carrier).Nonempty at hTinter
  simp only [zero_add] at hToverlap
  rw [hE0, hE1] at hTinter hToverlap
  change closure (A.reverse.region (L / 2) L) ⊆ T.carrier at hclosedOld
  change closure (T.region (-L) (-L / 2)) ⊆ A.carrier at hclosedNew
  obtain ⟨R, hchoice, hTregion⟩ : ∃ R : EpsilonNeck g,
      (R = N' ∨ R = N'.reverse) ∧
        ∀ p q : ℝ, T.region p q = R.region (-q) (-p) := by
    rcases hTchoice with h | h
    · refine ⟨N'.reverse, Or.inr rfl, ?_⟩
      intro p q
      rw [h, EpsilonNeck.reverse_region]
      simp only [neg_neg]
    · refine ⟨N', Or.inl rfl, ?_⟩
      intro p q
      rw [h]
      exact N'.reverse_region p q
  have hRc : R.center = N'.center := by rcases hchoice with rfl | rfl <;> rfl
  have hRu : R.carrier = N'.carrier := by rcases hchoice with rfl | rfl <;> rfl
  have hRe : R.epsilon = epsilon := by rcases hchoice with rfl | rfl <;> exact heN'
  have hTRu : T.carrier = R.carrier := hTselected.2.2.2.1.trans hRu.symm
  have hselected : R.SameUpToReversal N' := by
    rcases hchoice with rfl | rfl
    · refine ⟨rfl, rfl, rfl, rfl, rfl, 1, Or.inl rfl, ?_⟩
      intro z _
      simp only [one_mul]
    · refine ⟨rfl, rfl, rfl, rfl, rfl, -1, Or.inr rfl, ?_⟩
      intro z _
      change N'.coordinate_map (z.1, -z.2) = N'.coordinate_map (z.1, -1 * z.2)
      simp
  have hclosed : closure (R.region (L / 2) L) ⊆ A.carrier ∧
      closure (A.region (-L) (-L / 2)) ⊆ R.carrier := by
    constructor
    · rw [hTregion] at hclosedNew
      simpa only [neg_div, neg_neg] using hclosedNew
    · simpa only [EpsilonNeck.reverse_region, hTRu, neg_div] using hclosedOld
  have hquarter : R.region (L / 2) L ⊆ A.carrier ∧
      A.region (-L) (-L / 2) ⊆ R.carrier :=
    ⟨fun _ hx => hclosed.1 (subset_closure hx), fun _ hx => hclosed.2 (subset_closure hx)⟩
  have hoverlap : R.carrier ∩ A.carrier ⊆
      R.region (-L / 2) L ∩ A.region (-L) (L / 2) := by
    intro x hx
    have h := hToverlap ⟨hx.2, hTRu.symm ▸ hx.1⟩
    constructor
    · have hh := h.2
      rw [hTregion] at hh
      simpa only [neg_div, neg_neg] using hh
    · simpa only [EpsilonNeck.reverse_region, neg_div, neg_neg] using h.1
  have hinter : (R.carrier ∩ A.carrier).Nonempty := by
    obtain ⟨x, hxA, hxT⟩ := hTinter
    exact ⟨x, hTRu ▸ hxT, hxA⟩
  have hnegativeHeight (x : M) (hx : x ∈ R.region (-L) (-L / 2)) : F x = -L := by
    have hxA : x ∉ A.carrier := by
      intro hxa
      have hh := (hoverlap ⟨hx.1, hxa⟩).1.2.1
      linarith only [hh, hx.2.2]
    have hxN' : x ∈ N'.carrier := hRu ▸ hx.1
    rcases hFout x (hN'W hxN') hxA with h | h
    · exact h
    · have hh := hupper x hxN'
      linarith only [h, hh, hL]
  have hexclusion {j : ℤ} (hj : j ∈ C.shape.active) :
      Disjoint (C.neck j).carrier (R.region (-L) (-L / 2)) := by
    apply Set.disjoint_left.mpr
    intro x hxj hxR
    have hh := hOldHeight x (hNU j hj hxj)
    rw [hnegativeHeight x hxR] at hh
    exact lt_irrefl _ hh

  have hratio := (hscale R A (by rw [hRe]; exact hes)
    (by rw [heA]; exact hes) hinter).2
  have hRscale : 0 < R.scale := R.scale_pos
  have hAlower : (999 : ℝ) / 1000 * R.scale ≤ A.scale :=
    ((lt_div_iff₀ R.scale_pos).mp (show (999 : ℝ) / 1000 < A.scale / R.scale by
      linarith only [(abs_lt.mp hratio).1])).le
  have hAupper : A.scale ≤ (1001 : ℝ) / 1000 * R.scale :=
    ((div_lt_iff₀ R.scale_pos).mp (show A.scale / R.scale < (1001 : ℝ) / 1000 by
      linarith only [(abs_lt.mp hratio).2])).le
  have hsqrtLower : (999 : ℝ) / 1000 ≤ Real.sqrt (1 - epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [henum])
  have hsqrtUpper : Real.sqrt (1 + epsilon) ≤ (1001 : ℝ) / 1000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith only [henum]⟩
  have hB0L : B0 ≤ L / 1000 := by
    have hbudget := (le_div_iff₀ hden).mp hebudget
    have hBe : B0 * epsilon ≤ 1 / 1000 := by nlinarith only [hbudget, hepsilonpos]
    calc
      B0 ≤ (1 / 1000) / epsilon := (le_div_iff₀ hepsilonpos).mpr hBe
      _ = L / 1000 := by dsimp only [L]; ring
  have hbalance :
      ENNReal.ofReal ((0.99 : ℝ) * R.scale * epsilon⁻¹) ≤ g.edist R.center A.center ∧
        g.edist R.center A.center ≤ ENNReal.ofReal ((1.01 : ℝ) * R.scale * epsilon⁻¹) := by
    rw [hcomm R.center A.center, hRc]
    have hd := A.edist_center_closure_bounds (closure_mono (fun _ hx => hx.1) hy) hyA
    rw [heA] at hd
    constructor
    · apply (ENNReal.ofReal_le_ofReal ?_).trans hd.1
      change (0.99 : ℝ) * R.scale * L ≤ A.scale * Real.sqrt (1 - epsilon) * L
      calc
        _ ≤ ((999 / 1000) * R.scale) * (999 / 1000) * L := by
          nlinarith only [mul_pos R.scale_pos hL]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul hAlower hsqrtLower (by norm_num) A.scale_pos.le) hL.le
    · apply hd.2.trans (ENNReal.ofReal_le_ofReal ?_)
      change A.scale * Real.sqrt (1 + epsilon) * (L + B0) ≤ (1.01 : ℝ) * R.scale * L
      calc
        _ ≤ ((1001 / 1000) * R.scale) * (1001 / 1000) * (L + B0) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hAupper hsqrtUpper (Real.sqrt_nonneg _) (by positivity))
            (by positivity)
        _ ≤ ((1001 / 1000) * R.scale) * (1001 / 1000) * (L + L / 1000) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hB0L) (by positivity)
        _ ≤ _ := by nlinarith only [mul_pos R.scale_pos hL]
  have hcenters {j : ℤ} (hj : j ∈ C.shape.active) : (C.neck j).center ≠ R.center := by
    intro h
    apply hyout
    apply hNU j hj
    rw [← hRc, ← h]
    exact (C.neck j).central_sphere_subset (C.neck j).center_on_central_sphere
  let V := Function.update C.neck (a - 1) R
  have hVnew : V (a - 1) = R := Function.update_self _ _ _
  have hVold {i : ℤ} (hi : i ∈ C.shape.active) : V i = C.neck i := by
    have hile : a ≤ i := ((hactive i).mp hi).1
    exact Function.update_of_ne (by omega : i ≠ a - 1) R C.neck
  have hold {i : ℤ} (hi : i ∈ Icc (a - 1) b) (hne : i ≠ a - 1) :
      i ∈ C.shape.active := by
    apply (hactive i).mpr
    rcases hi with ⟨hia, hib⟩
    exact ⟨by omega, hib⟩
  have holdPair {i : ℤ} (hi : i ∈ Icc (a - 1) b) (hn : i + 1 ∈ Icc (a - 1) b)
      (hne : i ≠ a - 1) : i ∈ C.shape.active ∧ i + 1 ∈ C.shape.active := by
    rcases hi with ⟨hia, hib⟩
    rcases hn with ⟨hna, hnb⟩
    exact ⟨(hactive i).mpr ⟨by omega, hib⟩,
      (hactive (i + 1)).mpr ⟨by omega, hnb⟩⟩
  have hnewNext : a - 1 + 1 = a := by omega
  let D : BalancedNeckChain g epsilon := {
    shape := .finite (a - 1) b
    neck := V
    source_necks := C.source_necks
    selected := by
      intro i hi
      change i ∈ Icc (a - 1) b at hi
      by_cases hin : i = a - 1
      · subst i
        exact ⟨N', hsource, hVnew ▸ hselected⟩
      · have hio := hold hi hin
        simpa only [hVold hio] using C.selected i hio
    active_nonempty := ⟨a, by omega, hab⟩
    epsilon_eq := by
      intro i hi
      change i ∈ Icc (a - 1) b at hi
      by_cases hin : i = a - 1
      · subst i
        rw [hVnew]
        exact hRe
      · rw [hVold (hold hi hin)]
        exact C.epsilon_eq i (hold hi hin)
    centers_distinct := by
      intro i hi j hj hij
      change i ∈ Icc (a - 1) b at hi
      change j ∈ Icc (a - 1) b at hj
      by_cases hin : i = a - 1
      · subst i
        have hjo := hold hj (Ne.symm hij)
        rw [hVnew, hVold hjo]
        exact (hcenters hjo).symm
      · have hio := hold hi hin
        by_cases hjn : j = a - 1
        · subst j
          rw [hVold hio, hVnew]
          exact hcenters hio
        · have hjo := hold hj hjn
          rw [hVold hio, hVold hjo]
          exact C.centers_distinct hio hjo hij
    adjacent_overlap := by
      intro i hi hn
      change i ∈ Icc (a - 1) b at hi
      change i + 1 ∈ Icc (a - 1) b at hn
      by_cases hin : i = a - 1
      · subst i
        rw [hnewNext, hVnew, hVold ha]
        exact hinter
      · obtain ⟨hio, hno⟩ := holdPair hi hn hin
        rw [hVold hio, hVold hno]
        exact C.adjacent_overlap i hio hno
    overlap_contains_quarters := by
      intro i hi hn
      change i ∈ Icc (a - 1) b at hi
      change i + 1 ∈ Icc (a - 1) b at hn
      by_cases hin : i = a - 1
      · subst i
        rw [hnewNext, hVnew, hVold ha]
        exact hquarter
      · obtain ⟨hio, hno⟩ := holdPair hi hn hin
        rw [hVold hio, hVold hno]
        exact C.overlap_contains_quarters i hio hno
    overlap_within_three_quarters := by
      intro i hi hn
      change i ∈ Icc (a - 1) b at hi
      change i + 1 ∈ Icc (a - 1) b at hn
      by_cases hin : i = a - 1
      · subst i
        rw [hnewNext, hVnew, hVold ha]
        exact hoverlap
      · obtain ⟨hio, hno⟩ := holdPair hi hn hin
        rw [hVold hio, hVold hno]
        exact C.overlap_within_three_quarters i hio hno
    later_disjoint_negative_end := by
      intro i hi j hj hij
      change i ∈ Icc (a - 1) b at hi
      change j ∈ Icc (a - 1) b at hj
      have hjo : j ∈ C.shape.active := by
        apply (hactive j).mpr
        rcases hi with ⟨hia, hib⟩
        rcases hj with ⟨hja, hjb⟩
        exact ⟨by omega, hjb⟩
      by_cases hin : i = a - 1
      · subst i
        refine ⟨-L / 2, ⟨by linarith only [hL], by linarith only [hL]⟩, ?_⟩
        rw [hVold hjo, hVnew]
        exact hexclusion hjo
      · have hio := hold hi hin
        simpa only [hVold hio, hVold hjo] using
          C.later_disjoint_negative_end i hio j hjo hij
    balanced_center_distance := by
      intro i hi hn
      change i ∈ Icc (a - 1) b at hi
      change i + 1 ∈ Icc (a - 1) b at hn
      by_cases hin : i = a - 1
      · subst i
        rw [hnewNext, hVnew, hVold ha]
        exact hbalance
      · obtain ⟨hio, hno⟩ := holdPair hi hn hin
        rw [hVold hio, hVold hno]
        exact C.balanced_center_distance i hio hno }
  exact Or.inl ⟨R, D, hchoice, hselected, rfl, rfl, rfl, hclosed.1, hclosed.2⟩

end PoincareConjecture
