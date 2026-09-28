import PoincareConjecture.Proofs.M25.AppA_20_Fibration.IntrinsicHeights
import PoincareConjecture.Proofs.M25.Mathlib.OppositeCollarComponents
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Maps.Basic










set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



theorem BalancedNeckChain.intrinsic_ordered_cuts_of_relative_heights
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (C : BalancedNeckChain g epsilon) {a b : ℤ}
    (hshape : C.shape = ChainShape.finite a b) :
    let L := epsilon⁻¹
    let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
    ∀ (F : ℤ → M → ℝ),
      (∀ i ∈ C.shape.active,
        ContinuousOn (F i) U ∧
        (∀ x ∈ (C.neck i).carrier,
          F i x = ((C.neck i).coordinate_inverse x).2) ∧
        (∀ x ∈ U, x ∉ (C.neck i).carrier →
          F i x = -L ∨ F i x = L)) →
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
      IsOpen U ∧ IsConnected U ∧
      (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
        (∀ x ∈ (C.neck (i + 1)).carrier, -L / 2 < F i x) ∧
        (∀ x ∈ (C.neck (i + 1)).carrier \ (C.neck i).carrier,
          F i x = L)) ∧
      (∀ i ∈ C.shape.active, ∀ t ∈ Ioo (-L) L,
        U ∩ (F i) ⁻¹' {t} = S i t ∧
        A i t = U ∩ (F i) ⁻¹' Iio t ∧
        B i t = U ∩ (F i) ⁻¹' Ioi t ∧
        IsOpen (A i t) ∧ IsOpen (B i t) ∧
        IsConnected (A i t) ∧ IsConnected (B i t) ∧
        Disjoint (A i t) (B i t) ∧
        U ∩ closure (A i t) = U ∩ (F i) ⁻¹' Iic t ∧
        U ∩ closure (B i t) = U ∩ (F i) ⁻¹' Ici t ∧
        U ∩ frontier (A i t) = S i t ∧
        U ∩ frontier (B i t) = S i t ∧
        (C.neck i).region (-L) t ⊆ A i t ∧
        (C.neck i).region t L ⊆ B i t ∧
        A i t ∪ S i t ∪ B i t = U) ∧
      (∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active, i < j →
        ∀ s ∈ Ioo (L / 2) L, ∀ t ∈ Ioo (L / 2) L,
          U ∩ closure (A i s) ⊆ A j t ∧
          U ∩ closure (B j t) ⊆ B i s) := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let L := epsilon⁻¹
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  dsimp only
  intro F hF
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
  change IsOpen U ∧ IsConnected U ∧ _
  obtain ⟨i₀, hi₀⟩ := C.active_nonempty
  have hepos : 0 < epsilon := C.epsilon_eq i₀ hi₀ ▸ (C.neck i₀).epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepos
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by
    rw [hshape]
    rfl
  have hbetween {i j k : ℤ} (hi : i ∈ C.shape.active) (hj : j ∈ C.shape.active)
      (hik : i ≤ k) (hkj : k ≤ j) : k ∈ C.shape.active :=
    (hactive k).mpr ⟨((hactive i).mp hi).1.trans hik,
      hkj.trans ((hactive j).mp hj).2⟩
  have hNU (i : ℤ) (hi : i ∈ C.shape.active) : (C.neck i).carrier ⊆ U :=
    fun _ hx => mem_iUnion₂.mpr ⟨i, hi, hx⟩
  have hopenU : IsOpen U :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => (C.neck i).carrier_open
  have hconnU : IsConnected U := by
    apply IsConnected.biUnion_of_chain C.active_nonempty
    · rw [hshape]
      exact ordConnected_Icc
    · intro i _
      exact (C.neck i).isConnected_carrier
    · intro i hi hn
      change i + 1 ∈ C.shape.active at hn
      change ((C.neck i).carrier ∩ (C.neck (i + 1)).carrier).Nonempty
      exact C.adjacent_overlap i hi hn
  let : ConnectedSpace U := Subtype.connectedSpace hconnU
  let : LocallyConnectedSpace U := hopenU.locallyConnectedSpace
  have hdom (i : ℤ) (hi : i ∈ C.shape.active) {t : ℝ}
      (ht : t ∈ Ioo (-L) L) : t ∈ Ioo (-(C.neck i).epsilon⁻¹) (C.neck i).epsilon⁻¹ := by
    simpa only [C.epsilon_eq i hi] using ht
  have hmemS (i : ℤ) (hi : i ∈ C.shape.active) {t : ℝ}
      (ht : t ∈ Ioo (-L) L) (x : M) :
      x ∈ S i t ↔ x ∈ (C.neck i).carrier ∧ ((C.neck i).coordinate_inverse x).2 = t := by
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨(C.neck i).coordinate_map_mem ⟨mem_univ _, hdom i hi ht⟩,
        congrArg Prod.snd ((C.neck i).coordinate_inverse_map (v, t) (hdom i hi ht))⟩
    · rintro ⟨hx, hxt⟩
      refine ⟨((C.neck i).coordinate_inverse x).1, ?_⟩
      rw [← hxt]
      exact (C.neck i).coordinate_map_inverse hx
  have hSU (i : ℤ) (hi : i ∈ C.shape.active) {t : ℝ}
      (ht : t ∈ Ioo (-L) L) : S i t ⊆ U :=
    fun x hx => hNU i hi ((hmemS i hi ht x).mp hx).1
  have hlevel (i : ℤ) (hi : i ∈ C.shape.active) {t : ℝ}
      (ht : t ∈ Ioo (-L) L) : U ∩ (F i) ⁻¹' {t} = S i t := by
    ext x
    constructor
    · rintro ⟨hxU, hxt⟩
      change F i x = t at hxt
      by_cases hx : x ∈ (C.neck i).carrier
      · exact (hmemS i hi ht x).mpr ⟨hx, ((hF i hi).2.1 x hx).symm.trans hxt⟩
      · rcases (hF i hi).2.2 x hxU hx with hm | hp
        · exact False.elim ((ne_of_lt ht.1) (hm.symm.trans hxt))
        · exact False.elim ((ne_of_gt ht.2) (hp.symm.trans hxt))
    · intro hx
      obtain ⟨hxN, hxt⟩ := (hmemS i hi ht x).mp hx
      exact ⟨hNU i hi hxN, ((hF i hi).2.1 x hxN).trans hxt⟩
  have hnext (i : ℤ) (hi : i ∈ C.shape.active) (hn : i + 1 ∈ C.shape.active) :
      (∀ x ∈ (C.neck (i + 1)).carrier, -L / 2 < F i x) ∧
      (∀ x ∈ (C.neck (i + 1)).carrier \ (C.neck i).carrier, F i x = L) := by
    have hav (x : M) (hx : x ∈ (C.neck (i + 1)).carrier) : F i x ≠ -L / 2 := by
      by_cases ho : x ∈ (C.neck i).carrier
      · rw [(hF i hi).2.1 x ho]
        exact ne_of_gt (C.overlap_within_three_quarters i hi hn ⟨ho, hx⟩).1.2.1
      · rcases (hF i hi).2.2 x (hNU (i + 1) hn hx) ho with hm | hp
        · rw [hm]; linarith only [hL]
        · rw [hp]; linarith only [hL]
    have hm : 3 * L / 4 ∈ Ioo (-L) L := by constructor <;> linarith only [hL]
    have hxN := (C.neck i).coordinate_map_mem (z := (q i, 3 * L / 4))
      ⟨mem_univ _, hdom i hi hm⟩
    have hxreg : (C.neck i).coordinate_map (q i, 3 * L / 4) ∈
        (C.neck i).region (L / 2) L := by
      refine ⟨hxN, ?_⟩
      rw [(C.neck i).coordinate_inverse_map _ (hdom i hi hm)]
      constructor <;> linarith only [hL]
    have hsign (x : M) (hx : x ∈ (C.neck (i + 1)).carrier) : -L / 2 < F i x := by
      apply (C.neck (i + 1)).isConnected_carrier.isPreconnected.lt_of_ne
        ((hF i hi).1.mono (hNU (i + 1) hn)) hav ?_ hx
      refine ⟨(C.neck i).coordinate_map (q i, 3 * L / 4),
        (C.overlap_contains_quarters i hi hn).1 hxreg, ?_⟩
      rw [(hF i hi).2.1 _ hxN, (C.neck i).coordinate_inverse_map _ (hdom i hi hm)]
      dsimp only
      linarith only [hL]
    refine ⟨hsign, ?_⟩
    intro x hx
    rcases (hF i hi).2.2 x (hNU (i + 1) hn hx.1) hx.2 with hm | hp
    · have h := hsign x hx.1
      rw [hm] at h
      linarith only [hL, h]
    · exact hp
  have hcuts (i : ℤ) (hi : i ∈ C.shape.active) (t : ℝ) (ht : t ∈ Ioo (-L) L) :
      U ∩ (F i) ⁻¹' {t} = S i t ∧
      A i t = U ∩ (F i) ⁻¹' Iio t ∧ B i t = U ∩ (F i) ⁻¹' Ioi t ∧
      IsOpen (A i t) ∧ IsOpen (B i t) ∧
      IsConnected (A i t) ∧ IsConnected (B i t) ∧ Disjoint (A i t) (B i t) ∧
      U ∩ closure (A i t) = U ∩ (F i) ⁻¹' Iic t ∧
      U ∩ closure (B i t) = U ∩ (F i) ⁻¹' Ici t ∧
      U ∩ frontier (A i t) = S i t ∧ U ∩ frontier (B i t) = S i t ∧
      (C.neck i).region (-L) t ⊆ A i t ∧ (C.neck i).region t L ⊆ B i t ∧
      A i t ∪ S i t ∪ B i t = U := by
    let N := C.neck i
    let Shat : Set U := (Subtype.val : U → M) ⁻¹' S i t
    have hfc : Continuous (fun x : U => F i x.1) :=
      (hF i hi).1.comp_continuous continuous_subtype_val (fun x => x.property)
    have hhatlevel (x : U) : F i x.1 = t ↔ x ∈ Shat := by
      constructor
      · intro hx
        change x.1 ∈ S i t
        exact hlevel i hi ht ▸ (show x.1 ∈ U ∩ (F i) ⁻¹' {t} from ⟨x.2, hx⟩)
      · intro hx
        have h : x.1 ∈ U ∩ (F i) ⁻¹' {t} := (hlevel i hi ht).symm ▸ hx
        exact h.2
    have hShat : IsClosed Shat := by
      have heq : Shat = (fun x : U => F i x.1) ⁻¹' {t} := by
        ext x
        exact (hhatlevel x).symm
      rw [heq]
      exact isClosed_singleton.preimage hfc
    have haht : (t - L) / 2 ∈ Ioo (-L) t := by
      constructor <;> linarith only [ht.1]
    have hbht : (t + L) / 2 ∈ Ioo t L := by
      constructor <;> linarith only [ht.2]
    have hadom := hdom i hi ⟨haht.1, haht.2.trans ht.2⟩
    have hbdom := hdom i hi ⟨ht.1.trans hbht.1, hbht.2⟩
    have haN := N.coordinate_map_mem (z := (q i, (t - L) / 2)) ⟨mem_univ _, hadom⟩
    have hbN := N.coordinate_map_mem (z := (q i, (t + L) / 2)) ⟨mem_univ _, hbdom⟩
    let aa : U := ⟨N.coordinate_map (q i, (t - L) / 2), hNU i hi haN⟩
    let bb : U := ⟨N.coordinate_map (q i, (t + L) / 2), hNU i hi hbN⟩
    have haaHeight : F i aa.1 = (t - L) / 2 := by
      rw [(hF i hi).2.1 _ haN, N.coordinate_inverse_map _ hadom]
    have hbbHeight : F i bb.1 = (t + L) / 2 := by
      rw [(hF i hi).2.1 _ hbN, N.coordinate_inverse_map _ hbdom]
    have haaLt : F i aa.1 < t := by
      rw [haaHeight]
      exact haht.2
    have hbbGt : t < F i bb.1 := by
      rw [hbbHeight]
      exact hbht.1
    have haa : aa ∉ Shat := fun h => (ne_of_lt haaLt) ((hhatlevel aa).mpr h)
    have hbb : bb ∉ Shat := fun h => (ne_of_gt hbbGt) ((hhatlevel bb).mpr h)
    let Ah : Set U := connectedComponentIn Shatᶜ aa
    let Bh : Set U := connectedComponentIn Shatᶜ bb
    have hAh : IsConnected Ah := isConnected_connectedComponentIn_iff.mpr haa
    have hBh : IsConnected Bh := isConnected_connectedComponentIn_iff.mpr hbb
    have hAo : IsOpen Ah := hShat.isOpen_compl.connectedComponentIn
    have hBo : IsOpen Bh := hShat.isOpen_compl.connectedComponentIn
    have hAavoid (x : U) (hx : x ∈ Ah) : F i x.1 ≠ t :=
      fun he => (connectedComponentIn_subset Shatᶜ aa hx) ((hhatlevel x).mp he)
    have hBavoid (x : U) (hx : x ∈ Bh) : F i x.1 ≠ t :=
      fun he => (connectedComponentIn_subset Shatᶜ bb hx) ((hhatlevel x).mp he)
    have hAsign (x : U) (hx : x ∈ Ah) : F i x.1 < t :=
      hAh.isPreconnected.gt_of_ne hfc.continuousOn hAavoid
        ⟨aa, mem_connectedComponentIn haa, haaLt⟩ hx
    have hBsign (x : U) (hx : x ∈ Bh) : t < F i x.1 :=
      hBh.isPreconnected.lt_of_ne hfc.continuousOn hBavoid
        ⟨bb, mem_connectedComponentIn hbb, hbbGt⟩ hx
    have hne : Ah ≠ Bh := by
      intro heq
      exact lt_asymm haaLt (hBsign aa (heq ▸ mem_connectedComponentIn haa))
    let r := min (t + L) (L - t) / 2
    have hmin : 0 < min (t + L) (L - t) :=
      lt_min (by linarith only [ht.1]) (by linarith only [ht.2])
    have hr : 0 < r := half_pos hmin
    have hlo : -L < t - r := by
      have hm := min_le_left (t + L) (L - t)
      dsimp only [r]
      linarith only [ht.1, hm]
    have hhi : t + r < L := by
      have hm := min_le_right (t + L) (L - t)
      dsimp only [r]
      linarith only [ht.2, hm]
    have hshift (s : Ioo (-r) r) : t + (s : ℝ) ∈ Ioo (-L) L := by
      constructor <;> linarith only [hlo, hhi, s.property.1, s.property.2]
    let Vhat : Set U := {x | x.1 ∈ N.region (t - r) (t + r)}
    have hVhat : IsOpen Vhat := (N.isOpen_region _ _).preimage continuous_subtype_val
    let e : (UnitTwoSphere × Ioo (-r) r) ≃ₜ Vhat :=
      { toFun := fun z => ⟨⟨N.coordinate_map (z.1, t + (z.2 : ℝ)),
          hNU i hi (N.coordinate_map_mem ⟨mem_univ _, hdom i hi (hshift z.2)⟩)⟩, by
          refine ⟨N.coordinate_map_mem ⟨mem_univ _, hdom i hi (hshift z.2)⟩, ?_, ?_⟩
          · rw [N.coordinate_inverse_map _ (hdom i hi (hshift z.2))]
            dsimp only
            linarith only [z.2.property.1]
          · rw [N.coordinate_inverse_map _ (hdom i hi (hshift z.2))]
            dsimp only
            linarith only [z.2.property.2]⟩
        invFun := fun x => ((N.coordinate_inverse x.1.1).1,
          ⟨(N.coordinate_inverse x.1.1).2 - t, by
            constructor <;> linarith only [x.property.2.1, x.property.2.2]⟩)
        left_inv := by
          intro z
          apply Prod.ext
          · change (N.coordinate_inverse (N.coordinate_map (z.1, t + (z.2 : ℝ)))).1 = z.1
            exact congrArg Prod.fst
              (N.coordinate_inverse_map (z.1, t + (z.2 : ℝ)) (hdom i hi (hshift z.2)))
          · apply Subtype.ext
            change (N.coordinate_inverse (N.coordinate_map (z.1, t + (z.2 : ℝ)))).2 - t = _
            rw [N.coordinate_inverse_map _ (hdom i hi (hshift z.2))]
            dsimp only
            ring
        right_inv := by
          intro x
          apply Subtype.ext
          apply Subtype.ext
          change N.coordinate_map ((N.coordinate_inverse x.1.1).1,
            t + ((N.coordinate_inverse x.1.1).2 - t)) = x.1.1
          rw [show t + ((N.coordinate_inverse x.1.1).2 - t) =
            (N.coordinate_inverse x.1.1).2 by ring]
          exact N.coordinate_map_inverse x.property.1
        continuous_toFun := by
          apply Continuous.subtype_mk
          apply Continuous.subtype_mk
          apply N.coordinate_map_smooth.continuousOn.comp_continuous
          · exact continuous_fst.prodMk (continuous_const.add
              (continuous_subtype_val.comp continuous_snd))
          · intro z
            exact ⟨mem_univ _, hdom i hi (hshift z.2)⟩
        continuous_invFun := by
          have hc : Continuous (fun x : Vhat => N.coordinate_inverse x.1.1) :=
            N.coordinate_inverse_smooth.continuousOn.comp_continuous
              (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.property.1)
          exact hc.fst.prodMk ((hc.snd.sub continuous_const).subtype_mk _) }
    have hecenter : range (fun v : UnitTwoSphere =>
        (e (v, ⟨0, neg_lt_zero.mpr hr, hr⟩) : U)) = Shat := by
      apply Subset.antisymm
      · rintro x ⟨v, rfl⟩
        change N.coordinate_map (v, t + 0) ∈ S i t
        simpa only [add_zero] using
          (mem_range_self v : N.coordinate_map (v, t) ∈ S i t)
      · intro x hx
        change x.1 ∈ S i t at hx
        obtain ⟨v, hv⟩ := hx
        refine ⟨v, ?_⟩
        apply Subtype.ext
        change N.coordinate_map (v, t + 0) = x.1
        simpa only [add_zero] using hv
    have hregion (c d : ℝ) (hc : -L ≤ c) (hd : d ≤ L) (hcd : c < d) :
        IsConnected ((Subtype.val : U → M) ⁻¹' N.region c d) := by
      have hprod : univ ×ˢ Ioo c d ⊆ N.cylinderDomain := by
        rintro z ⟨_, hz⟩
        exact ⟨mem_univ _, hdom i hi ⟨hc.trans_lt hz.1, hz.2.trans_le hd⟩⟩
      have heq : N.coordinate_map '' (univ ×ˢ Ioo c d) = N.region c d := by
        apply Subset.antisymm
        · rintro x ⟨z, hz, rfl⟩
          refine ⟨N.coordinate_map_mem (hprod hz), ?_⟩
          simpa only [N.coordinate_inverse_map z (hprod hz).2, mem_Ioo] using hz.2
        · intro x hx
          exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2⟩, N.coordinate_map_inverse hx.1⟩
      have hcN : IsConnected (N.region c d) := by
        rw [← heq]
        exact (isConnected_univ.prod (isConnected_Ioo hcd)).image _
          (N.coordinate_map_smooth.continuousOn.mono hprod)
      exact hcN.preimage_of_isOpenMap Subtype.val_injective hopenU.isOpenMap_subtype_val
        (fun x hx => ⟨⟨x, hNU i hi hx.1⟩, rfl⟩)
    have hnegA : (Subtype.val : U → M) ⁻¹' N.region (-L) t ⊆ Ah := by
      apply (hregion (-L) t le_rfl ht.2.le ht.1).isPreconnected.subset_connectedComponentIn
      · change N.coordinate_map (q i, (t - L) / 2) ∈ N.region (-L) t
        refine ⟨haN, ?_⟩
        rw [N.coordinate_inverse_map (q i, (t - L) / 2) hadom]
        exact haht
      · intro x hx hxS
        exact ne_of_lt hx.2.2 ((hmemS i hi ht x.1).mp hxS).2
    have hposB : (Subtype.val : U → M) ⁻¹' N.region t L ⊆ Bh := by
      apply (hregion t L ht.1.le le_rfl ht.2).isPreconnected.subset_connectedComponentIn
      · change N.coordinate_map (q i, (t + L) / 2) ∈ N.region t L
        refine ⟨hbN, ?_⟩
        rw [N.coordinate_inverse_map (q i, (t + L) / 2) hbdom]
        exact hbht
      · intro x hx hxS
        exact ne_of_gt hx.2.1 ((hmemS i hi ht x.1).mp hxS).2
    have hminus : (fun z => (e z : U)) '' {z | (z.2 : ℝ) < 0} ⊆ Ah := by
      rintro x ⟨z, hz, rfl⟩
      change (z.2 : ℝ) < 0 at hz
      apply hnegA
      change N.coordinate_map (z.1, t + (z.2 : ℝ)) ∈ N.region (-L) t
      refine ⟨N.coordinate_map_mem ⟨mem_univ _, hdom i hi (hshift z.2)⟩, ?_⟩
      rw [N.coordinate_inverse_map _ (hdom i hi (hshift z.2))]
      exact ⟨(hshift z.2).1, by dsimp only; linarith only [hz]⟩
    have hplus : (fun z => (e z : U)) '' {z | 0 < (z.2 : ℝ)} ⊆ Bh := by
      rintro x ⟨z, hz, rfl⟩
      change 0 < (z.2 : ℝ) at hz
      apply hposB
      change N.coordinate_map (z.1, t + (z.2 : ℝ)) ∈ N.region t L
      refine ⟨N.coordinate_map_mem ⟨mem_univ _, hdom i hi (hshift z.2)⟩, ?_⟩
      rw [N.coordinate_inverse_map _ (hdom i hi (hshift z.2))]
      exact ⟨by dsimp only; linarith only [hz], (hshift z.2).2⟩
    have hfront : Shat ⊆ frontier Ah ∩ frontier Bh := by
      intro x hx
      have hxS := hx
      obtain ⟨v, rfl⟩ := hecenter.symm ▸ hx
      have hn := Poincare.Topology.collar_center_mem_closure_negative hr e v
      have hp := Poincare.Topology.collar_center_mem_closure_positive hr e v
      exact ⟨⟨closure_mono hminus hn,
        fun h => (connectedComponentIn_subset Shatᶜ aa (interior_subset h)) hxS⟩,
        ⟨closure_mono hplus hp,
          fun h => (connectedComponentIn_subset Shatᶜ bb (interior_subset h)) hxS⟩⟩
    have hop := Poincare.Topology.opposite_collar_components hr hVhat e
      (a := aa) (b := bb) (by simpa only [hecenter] using haa)
      (by simpa only [hecenter] using hbb) (by simpa only [hecenter] using hne)
      (by simpa only [hecenter] using hfront)
    have hAf : frontier Ah = Shat := by simpa only [hecenter] using hop.1
    have hBf : frontier Bh = Shat := by simpa only [hecenter] using hop.2.1
    have hcoverh : Ah ∪ Shat ∪ Bh = (univ : Set U) := by
      simpa only [hecenter, PreconnectedSpace.connectedComponent_eq_univ] using hop.2.2.2.2
    have hAeq : Ah = {x : U | F i x.1 < t} := by
      ext x
      constructor
      · exact hAsign x
      · intro hx
        rcases hcoverh.symm ▸ (mem_univ x) with (ha | hs) | hb
        · exact ha
        · exact False.elim ((ne_of_lt hx) ((hhatlevel x).mpr hs))
        · exact False.elim (lt_asymm hx (hBsign x hb))
    have hBeq : Bh = {x : U | t < F i x.1} := by
      ext x
      constructor
      · exact hBsign x
      · intro hx
        rcases hcoverh.symm ▸ (mem_univ x) with (ha | hs) | hb
        · exact False.elim (lt_asymm (hAsign x ha) hx)
        · exact False.elim ((ne_of_gt hx) ((hhatlevel x).mpr hs))
        · exact hb

    have hcomponent (c : U) (hc : c ∉ Shat) :
        (Subtype.val : U → M) '' connectedComponentIn Shatᶜ c =
          connectedComponentIn (U \ S i t) c.1 := by
      have hcM : c.1 ∈ U \ S i t := ⟨c.2, hc⟩
      have himage : IsConnected ((Subtype.val : U → M) '' connectedComponentIn Shatᶜ c) :=
        (isConnected_connectedComponentIn_iff.mpr hc).image _ continuous_subtype_val.continuousOn
      apply Subset.antisymm
      · apply himage.isPreconnected.subset_connectedComponentIn
        · exact ⟨c, mem_connectedComponentIn hc, rfl⟩
        · rintro x ⟨y, hy, rfl⟩
          exact ⟨y.2, connectedComponentIn_subset Shatᶜ c hy⟩
      · intro x hx
        let Z := connectedComponentIn (U \ S i t) c.1
        have hZsub : Z ⊆ U \ S i t := connectedComponentIn_subset _ _
        have hZconn : IsConnected Z := isConnected_connectedComponentIn_iff.mpr hcM
        have hZlift : IsConnected ((Subtype.val : U → M) ⁻¹' Z) :=
          hZconn.preimage_of_isOpenMap Subtype.val_injective hopenU.isOpenMap_subtype_val
            (fun y hy => ⟨⟨y, (hZsub hy).1⟩, rfl⟩)
        have hpre : (Subtype.val : U → M) ⁻¹' Z ⊆ Shatᶜ :=
          fun y hy => (hZsub hy).2
        have hsub := hZlift.isPreconnected.subset_connectedComponentIn
          (show c ∈ (Subtype.val : U → M) ⁻¹' Z from mem_connectedComponentIn hcM) hpre
        exact ⟨⟨x, (hZsub hx).1⟩, hsub hx, rfl⟩
    have hAA : (Subtype.val : U → M) '' Ah = A i t := hcomponent aa haa
    have hBB : (Subtype.val : U → M) '' Bh = B i t := hcomponent bb hbb
    have ha : A i t = U ∩ (F i) ⁻¹' Iio t := by
      rw [← hAA, hAeq]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨hxU, hx⟩
        exact ⟨⟨x, hxU⟩, hx, rfl⟩
    have hb : B i t = U ∩ (F i) ⁻¹' Ioi t := by
      rw [← hBB, hBeq]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨hxU, hx⟩
        exact ⟨⟨x, hxU⟩, hx, rfl⟩
    have hpreA : (Subtype.val : U → M) ⁻¹' A i t = Ah := by
      rw [← hAA, preimage_image_eq _ Subtype.val_injective]
    have hpreB : (Subtype.val : U → M) ⁻¹' B i t = Bh := by
      rw [← hBB, preimage_image_eq _ Subtype.val_injective]
    have hfrontTransport (E : Set M) (D : Set U)
        (hpre : (Subtype.val : U → M) ⁻¹' E = D) (hDf : frontier D = Shat) :
        U ∩ frontier E = S i t := by
      have heq : (Subtype.val : U → M) ⁻¹' frontier E = Shat := by
        rw [hopenU.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
          continuous_subtype_val E, hpre, hDf]
      ext x
      constructor
      · rintro ⟨hxU, hx⟩
        have h : (⟨x, hxU⟩ : U) ∈ (Subtype.val : U → M) ⁻¹' frontier E := hx
        change (⟨x, hxU⟩ : U) ∈ Shat
        exact heq ▸ h
      · intro hx
        have hxU := hSU i hi ht hx
        have h : (⟨x, hxU⟩ : U) ∈ Shat := hx
        refine ⟨hxU, ?_⟩
        change (⟨x, hxU⟩ : U) ∈ (Subtype.val : U → M) ⁻¹' frontier E
        exact heq.symm ▸ h
    have hfa := hfrontTransport (A i t) Ah hpreA hAf
    have hfb := hfrontTransport (B i t) Bh hpreB hBf
    have hca : U ∩ closure (A i t) = U ∩ (F i) ⁻¹' Iic t := by
      ext x
      constructor
      · rintro ⟨hxU, hx⟩
        rw [closure_eq_self_union_frontier] at hx
        rcases hx with hx | hx
        · exact ⟨hxU, (show F i x < t from (ha ▸ hx).2).le⟩
        · have hxS : x ∈ S i t := hfa ▸ ⟨hxU, hx⟩
          have hxlev : x ∈ U ∩ (F i) ⁻¹' {t} := (hlevel i hi ht).symm ▸ hxS
          exact ⟨hxU, (show F i x = t from hxlev.2).le⟩
      · rintro ⟨hxU, hx⟩
        refine ⟨hxU, ?_⟩
        rcases (show F i x ≤ t from hx).lt_or_eq with hlt | heq
        · exact subset_closure (ha.symm ▸ ⟨hxU, hlt⟩)
        · have hxS : x ∈ S i t := hlevel i hi ht ▸ ⟨hxU, heq⟩
          exact (hfa.symm ▸ hxS).2.1
    have hcb : U ∩ closure (B i t) = U ∩ (F i) ⁻¹' Ici t := by
      ext x
      constructor
      · rintro ⟨hxU, hx⟩
        rw [closure_eq_self_union_frontier] at hx
        rcases hx with hx | hx
        · exact ⟨hxU, (show t < F i x from (hb ▸ hx).2).le⟩
        · have hxS : x ∈ S i t := hfb ▸ ⟨hxU, hx⟩
          have hxlev : x ∈ U ∩ (F i) ⁻¹' {t} := (hlevel i hi ht).symm ▸ hxS
          exact ⟨hxU, (show F i x = t from hxlev.2).ge⟩
      · rintro ⟨hxU, hx⟩
        refine ⟨hxU, ?_⟩
        rcases (show t ≤ F i x from hx).lt_or_eq with hlt | heq
        · exact subset_closure (hb.symm ▸ ⟨hxU, hlt⟩)
        · have hxS : x ∈ S i t := hlevel i hi ht ▸ ⟨hxU, heq.symm⟩
          exact (hfb.symm ▸ hxS).2.1
    refine ⟨hlevel i hi ht, ha, hb, ?_, ?_, ?_, ?_, ?_, hca, hcb, hfa, hfb, ?_, ?_, ?_⟩
    · rw [← hAA]
      exact hopenU.isOpenMap_subtype_val _ hAo
    · rw [← hBB]
      exact hopenU.isOpenMap_subtype_val _ hBo
    · rw [← hAA]
      exact hAh.image _ continuous_subtype_val.continuousOn
    · rw [← hBB]
      exact hBh.image _ continuous_subtype_val.continuousOn
    · apply disjoint_left.mpr
      intro x hxA hxB
      exact lt_asymm (show F i x < t from (ha ▸ hxA).2)
        (show t < F i x from (hb ▸ hxB).2)
    · intro x hx
      rw [ha]
      refine ⟨hNU i hi hx.1, ?_⟩
      change F i x < t
      rw [(hF i hi).2.1 x hx.1]
      exact hx.2.2
    · intro x hx
      rw [hb]
      refine ⟨hNU i hi hx.1, ?_⟩
      change t < F i x
      rw [(hF i hi).2.1 x hx.1]
      exact hx.2.1
    · ext x
      constructor
      · rintro ((hx | hx) | hx)
        · exact (ha ▸ hx).1
        · exact hSU i hi ht hx
        · exact (hb ▸ hx).1
      · intro hxU
        rcases lt_trichotomy (F i x) t with hlt | heq | hgt
        · exact Or.inl (Or.inl (ha.symm ▸ ⟨hxU, hlt⟩))
        · exact Or.inl (Or.inr (hlevel i hi ht ▸ ⟨hxU, heq⟩))
        · exact Or.inr (hb.symm ▸ ⟨hxU, hgt⟩)
  have hretained {s : ℝ} (hs : s ∈ Ioo (L / 2) L) : s ∈ Ioo (-L) L :=
    ⟨by linarith only [hL, hs.1], hs.2⟩
  have hadj (i : ℤ) (hi : i ∈ C.shape.active) (hn : i + 1 ∈ C.shape.active)
      (s : ℝ) (hs : s ∈ Ioo (L / 2) L) (t : ℝ) (ht : t ∈ Ioo (L / 2) L) :
      U ∩ closure (A i s) ⊆ A (i + 1) t ∧ U ∩ closure (B (i + 1) t) ⊆ B i s := by
    obtain ⟨_, ha, hb, _, _, hAc, _, _, hca, _, hfa, _, _, _, _⟩ :=
      hcuts i hi s (hretained hs)
    obtain ⟨_, hna, _, hnaOpen, _, _, _, _, _, hncb, _, _, _, _, _⟩ :=
      hcuts (i + 1) hn t (hretained ht)
    have hSA : S i s ⊆ A (i + 1) t := by
      rintro x ⟨v, rfl⟩
      have hxold := (C.neck i).coordinate_map_mem (z := (v, s))
        ⟨mem_univ _, hdom i hi (hretained hs)⟩
      have hxreg : (C.neck i).coordinate_map (v, s) ∈ (C.neck i).region (L / 2) L := by
        refine ⟨hxold, ?_⟩
        rw [(C.neck i).coordinate_inverse_map (v, s) (hdom i hi (hretained hs))]
        exact hs
      have hxnew := (C.overlap_contains_quarters i hi hn).1 hxreg
      rw [hna]
      refine ⟨hNU (i + 1) hn hxnew, ?_⟩
      change F (i + 1) ((C.neck i).coordinate_map (v, s)) < t
      rw [(hF (i + 1) hn).2.1 _ hxnew]
      exact (C.overlap_within_three_quarters i hi hn ⟨hxold, hxnew⟩).2.2.2.trans ht.1
    have hSB : S (i + 1) t ⊆ B i s := by
      rintro x ⟨v, rfl⟩
      have hxnew := (C.neck (i + 1)).coordinate_map_mem (z := (v, t))
        ⟨mem_univ _, hdom (i + 1) hn (hretained ht)⟩
      have hxout : (C.neck (i + 1)).coordinate_map (v, t) ∉ (C.neck i).carrier := by
        intro hxold
        have h := (C.overlap_within_three_quarters i hi hn ⟨hxold, hxnew⟩).2.2.2
        rw [(C.neck (i + 1)).coordinate_inverse_map _ (hdom (i + 1) hn (hretained ht))] at h
        exact lt_asymm ht.1 h
      rw [hb]
      refine ⟨hNU (i + 1) hn hxnew, ?_⟩
      change s < F i ((C.neck (i + 1)).coordinate_map (v, t))
      rw [(hnext i hi hn).2 _ ⟨hxnew, hxout⟩]
      exact hs.2
    have hpS : (C.neck i).coordinate_map (q i, s) ∈ S i s := mem_range_self _
    have hpcl : (C.neck i).coordinate_map (q i, s) ∈ closure (A i s) :=
      (hfa.symm ▸ hpS).2.1
    obtain ⟨w, hwn, hwi⟩ := mem_closure_iff.mp hpcl _ hnaOpen (hSA hpS)
    have hsign (x : M) (hx : x ∈ A i s) : F (i + 1) x < t := by
      apply hAc.isPreconnected.gt_of_ne
        ((hF (i + 1) hn).1.mono (fun _ h => (ha ▸ h).1)) ?_ ?_ hx
      · intro y hy heq
        have hyS : y ∈ S (i + 1) t :=
          hlevel (i + 1) hn (hretained ht) ▸ ⟨(ha ▸ hy).1, heq⟩
        exact lt_asymm (show F i y < s from (ha ▸ hy).2)
          (show s < F i y from (hb ▸ hSB hyS).2)
      · exact ⟨w, hwi, (hna ▸ hwn).2⟩
    have hac : U ∩ closure (A i s) ⊆ A (i + 1) t := by
      intro x hx
      have hxi := hca ▸ hx
      rcases (show F i x ≤ s from hxi.2).lt_or_eq with hlt | heq
      · rw [hna]
        exact ⟨hx.1, hsign x (ha.symm ▸ ⟨hx.1, hlt⟩)⟩
      · exact hSA (hlevel i hi (hretained hs) ▸ ⟨hx.1, heq⟩)
    refine ⟨hac, ?_⟩
    intro x hx
    have hxnext := hncb ▸ hx
    rw [hb]
    refine ⟨hx.1, ?_⟩
    change s < F i x
    by_contra hnot
    have hxold : x ∈ U ∩ closure (A i s) :=
      hca.symm ▸ ⟨hx.1, le_of_not_gt hnot⟩
    exact (not_lt_of_ge (show t ≤ F (i + 1) x from hxnext.2))
      (show F (i + 1) x < t from (hna ▸ hac hxold).2)
  have hmid : 3 * L / 4 ∈ Ioo (L / 2) L := by constructor <;> linarith only [hL]
  have hordered (i : ℤ) (hi : i ∈ C.shape.active) (j : ℤ) (hj : j ∈ C.shape.active)
      (hij : i < j) (s : ℝ) (hs : s ∈ Ioo (L / 2) L)
      (t : ℝ) (ht : t ∈ Ioo (L / 2) L) :
      U ∩ closure (A i s) ⊆ A j t ∧ U ∩ closure (B j t) ⊆ B i s := by
    let P (k : ℤ) := ∀ s ∈ Ioo (L / 2) L, ∀ t ∈ Ioo (L / 2) L,
      U ∩ closure (A i s) ⊆ A k t ∧ U ∩ closure (B k t) ⊆ B i s
    have hP : P j := by
      refine Int.leInduction (m := i + 1)
        (motive := fun k _ => k ∈ C.shape.active → P k) ?_ ?_ j (by omega) hj
      · intro hn
        exact hadj i hi hn
      · intro k hik ih hk₁ s hs t ht
        have hk : k ∈ C.shape.active := hbetween hi hk₁ (by omega) (by omega)
        have hp := ih hk s hs (3 * L / 4) hmid
        have hn := hadj k hk hk₁ (3 * L / 4) hmid t ht
        have hAk : A k (3 * L / 4) ⊆ U ∩ closure (A k (3 * L / 4)) :=
          fun _ hx => ⟨(connectedComponentIn_subset _ _ hx).1, subset_closure hx⟩
        have hBk : B k (3 * L / 4) ⊆ U ∩ closure (B k (3 * L / 4)) :=
          fun _ hx => ⟨(connectedComponentIn_subset _ _ hx).1, subset_closure hx⟩
        exact ⟨hp.1.trans (hAk.trans hn.1), hn.2.trans (hBk.trans hp.2)⟩
    exact hP s hs t ht
  exact ⟨hopenU, hconnU, hnext, hcuts, hordered⟩

end PoincareConjecture
