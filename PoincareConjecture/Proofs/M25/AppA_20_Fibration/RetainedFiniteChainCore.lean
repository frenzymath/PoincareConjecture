import PoincareConjecture.Proofs.M25.AppA_1_Necks.SliceProjectionDifferential
import PoincareConjecture.Proofs.M25.Mathlib.FiberwiseGraphComplement
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem BalancedNeckChain.exists_finite_retained_core_cover :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon), epsilon ≤ epsilon0 →
      ∀ a b : ℤ, C.shape = ChainShape.finite a b →
        let L := epsilon⁻¹
        let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
        ∃ lo : ℤ → ℝ,
          let K : Set M := ⋃ i ∈ C.shape.active,
            (C.neck i).coordinate_map ''
              (univ ×ˢ Icc (lo i) (3 * L / 4))
          (∀ i ∈ C.shape.active, -L < lo i ∧ lo i ≤ -L / 2) ∧
          lo a = -L / 2 ∧ IsCompact K ∧
          U = (K ∪ (C.neck a).region (-L) (lo a)) ∪
            (C.neck b).region (3 * L / 4) L := by
  obtain ⟨epsilon0, hpos, hcap, hgraph⟩ :=
    EpsilonNeck.exists_contained_slice_graph.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C hepsilon a b hshape
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let L : ℝ := epsilon⁻¹
  let T : ℝ := 3 * L / 4
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by
    rw [hshape]
    rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact ((hactive i).mp hi).1.trans ((hactive i).mp hi).2
  have ha : a ∈ C.shape.active := (hactive a).mpr ⟨le_rfl, hab⟩
  have hb : b ∈ C.shape.active := (hactive b).mpr ⟨hab, le_rfl⟩
  have hfinite : C.shape.active.Finite := by
    rw [hshape]
    exact Set.finite_Icc a b
  have hepos : 0 < epsilon := C.epsilon_eq a ha ▸ (C.neck a).epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepos
  have hTlo : L / 2 < T := by dsimp only [T]; linarith
  have hThi : T < L := by dsimp only [T]; linarith
  have hTneg : -L < T := by linarith

  have hpair (i : ℤ) (hi : i ∈ C.shape.active)
      (hi1 : i + 1 ∈ C.shape.active) :
      ∃ m : ℝ, -L < m ∧
        (∀ x ∈ (C.neck i).region T L,
          x ∈ (C.neck (i + 1)).carrier ∧
            m < ((C.neck (i + 1)).coordinate_inverse x).2 ∧
              ((C.neck (i + 1)).coordinate_inverse x).2 < L / 2) ∧
        (∀ x ∈ (C.neck (i + 1)).carrier,
          ((C.neck (i + 1)).coordinate_inverse x).2 < m →
            x ∈ (C.neck i).region (-L / 2) T) := by
    let N := C.neck i
    let N' := C.neck (i + 1)
    have he : N.epsilon = epsilon := C.epsilon_eq i hi
    have he' : N'.epsilon = epsilon := C.epsilon_eq (i + 1) hi1
    have hquarter : N.region (L / 2) L ⊆ N'.carrier :=
      (C.overlap_contains_quarters i hi hi1).1
    have hoverlap : N.carrier ∩ N'.carrier ⊆
        N.region (-L / 2) L ∩ N'.region (-L) (L / 2) :=
      C.overlap_within_three_quarters i hi hi1
    have hTN : T ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      rw [he]
      exact ⟨hTneg, hThi⟩
    have hsub (q : UnitTwoSphere) : N.coordinate_map (q, T) ∈ N'.carrier := by
      apply hquarter
      refine ⟨N.coordinate_map_mem ⟨mem_univ _, hTN⟩, ?_⟩
      simpa only [N.coordinate_inverse_map (q, T) hTN, mem_Ioo] using
        (show T ∈ Ioo (L / 2) L from ⟨hTlo, hThi⟩)
    have hsmall : N.epsilon ≤ epsilon0 := by rw [he]; exact hepsilon
    have hsmall' : N'.epsilon ≤ epsilon0 := by rw [he']; exact hepsilon
    obtain ⟨f, hfs, hfdom0, hfrange⟩ :=
      (hgraph N' N hsmall' hsmall T hTN hsub).1
    have hf : Continuous f := hfs.continuous
    have hfdom (q : UnitTwoSphere) : f q ∈ Ioo (-L) L := by
      simpa only [he'] using hfdom0 q
    have hfbound (q : UnitTwoSphere) : f q ∈ Ioo (-L) (L / 2) := by
      have hxnew : N'.coordinate_map (q, f q) ∈ N'.carrier :=
        N'.coordinate_map_mem ⟨mem_univ _, hfdom0 q⟩
      have hxrange : N'.coordinate_map (q, f q) ∈
          range (fun p : UnitTwoSphere => N.coordinate_map (p, T)) := by
        rw [← hfrange]
        exact mem_range_self q
      obtain ⟨p, hp⟩ := hxrange
      have hxold : N'.coordinate_map (q, f q) ∈ N.carrier := by
        rw [← hp]
        exact N.coordinate_map_mem ⟨mem_univ _, hTN⟩
      have hxhi := (hoverlap ⟨hxold, hxnew⟩).2.2.2
      refine ⟨(hfdom q).1, ?_⟩
      simpa only [N'.coordinate_inverse_map (q, f q) (hfdom0 q)] using hxhi
    let S : Set M := range (fun q : UnitTwoSphere => N.coordinate_map (q, T))
    have hmemS {x : M} : x ∈ S ↔ x ∈ N.carrier ∧
        (N.coordinate_inverse x).2 = T := by
      constructor
      · rintro ⟨q, rfl⟩
        exact ⟨N.coordinate_map_mem ⟨mem_univ _, hTN⟩,
          congrArg Prod.snd (N.coordinate_inverse_map (q, T) hTN)⟩
      · rintro ⟨hx, hxt⟩
        refine ⟨(N.coordinate_inverse x).1, ?_⟩
        rw [← hxt]
        exact N.coordinate_map_inverse hx
    have hnewheight {x : M} (hx : x ∈ N'.carrier) :
        (N'.coordinate_inverse x).2 ∈ Ioo (-L) L := by
      simpa only [he'] using (N'.coordinate_inverse_mem x hx).2
    have hequal {x : M} (hx : x ∈ N'.carrier) :
        x ∈ S ↔ (N'.coordinate_inverse x).2 = f (N'.coordinate_inverse x).1 := by
      change x ∈ range (fun q : UnitTwoSphere => N.coordinate_map (q, T)) ↔ _
      rw [← hfrange]
      constructor
      · rintro ⟨q, rfl⟩
        rw [N'.coordinate_inverse_map (q, f q) (hfdom0 q)]
      · intro hxeq
        refine ⟨(N'.coordinate_inverse x).1, ?_⟩
        change N'.coordinate_map
          ((N'.coordinate_inverse x).1, f (N'.coordinate_inverse x).1) = x
        rw [← hxeq]
        exact N'.coordinate_map_inverse hx
    let Dminus : Set RoundCylinderSpace := {z | -L < z.2 ∧ z.2 < f z.1}
    let Dplus : Set RoundCylinderSpace := {z | f z.1 < z.2 ∧ z.2 < L}
    let Wminus : Set M := N'.coordinate_map '' Dminus
    let Wplus : Set M := N'.coordinate_map '' Dplus
    have hminusD : Dminus ⊆ N'.cylinderDomain := by
      intro z hz
      rw [EpsilonNeck.cylinderDomain, he']
      exact ⟨mem_univ _, hz.1, hz.2.trans (hfdom z.1).2⟩
    have hplusD : Dplus ⊆ N'.cylinderDomain := by
      intro z hz
      rw [EpsilonNeck.cylinderDomain, he']
      exact ⟨mem_univ _, (hfdom z.1).1.trans hz.1, hz.2⟩
    have hminus : IsConnected Wminus :=
      (isConnected_between_continuous_graphs continuous_const hf
        (fun q => (hfdom q).1)).image N'.coordinate_map
          (N'.coordinate_map_smooth.continuousOn.mono hminusD)
    have hplus : IsConnected Wplus :=
      (isConnected_between_continuous_graphs hf continuous_const
        (fun q => (hfdom q).2)).image N'.coordinate_map
          (N'.coordinate_map_smooth.continuousOn.mono hplusD)
    have hminusV : Wminus ⊆ N'.carrier := by
      rintro x ⟨z, hz, rfl⟩
      exact N'.coordinate_map_mem (hminusD hz)
    have hplusV : Wplus ⊆ N'.carrier := by
      rintro x ⟨z, hz, rfl⟩
      exact N'.coordinate_map_mem (hplusD hz)
    have hmemMinus {x : M} (hx : x ∈ N'.carrier) :
        x ∈ Wminus ↔ (N'.coordinate_inverse x).2 < f (N'.coordinate_inverse x).1 := by
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa only [N'.coordinate_inverse_map z (hminusD hz).2] using hz.2
      · intro hxlt
        exact ⟨N'.coordinate_inverse x, ⟨(hnewheight hx).1, hxlt⟩,
          N'.coordinate_map_inverse hx⟩
    have hmemPlus {x : M} (hx : x ∈ N'.carrier) :
        x ∈ Wplus ↔ f (N'.coordinate_inverse x).1 < (N'.coordinate_inverse x).2 := by
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa only [N'.coordinate_inverse_map z (hplusD hz).2] using hz.1
      · intro hxlt
        exact ⟨N'.coordinate_inverse x, ⟨hxlt, (hnewheight hx).2⟩,
          N'.coordinate_map_inverse hx⟩
    let E : Set M := N.region (-L) T ∩ N'.carrier
    let J : Set M := N.coordinate_map '' (univ ×ˢ Icc (-L / 2) T)
    have hEopen : IsOpen E := (N.isOpen_region _ _).inter N'.carrier_open
    have hEJ : E ⊆ J := by
      intro x hx
      have hxlo := (hoverlap ⟨hx.1.1, hx.2⟩).1.2.1
      exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hxlo.le, hx.1.2.2.le⟩,
        N.coordinate_map_inverse hx.1.1⟩
    have hJcompact : IsCompact J := by
      apply N.isCompact_coordinate_slab
      · rw [he]
        change -L < -L / 2
        linarith
      · rw [he]
        exact hThi
    have hclosure : closure E ⊆ J := closure_minimal hEJ hJcompact.isClosed
    have hJmem {x : M} (hx : x ∈ J) :
        x ∈ N.carrier ∧ (N.coordinate_inverse x).2 ≤ T := by
      rcases hx with ⟨z, hz, rfl⟩
      have hzdom : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
        rw [he]
        exact ⟨by linarith [hz.2.1], hz.2.2.trans_lt hThi⟩
      exact ⟨N.coordinate_map_mem ⟨mem_univ _, hzdom⟩,
        by simpa only [N.coordinate_inverse_map z hzdom] using hz.2.2⟩
    have hclosedBelow {x : M} (hx : x ∈ closure E) (hxV : x ∈ N'.carrier)
        (hxS : x ∉ S) : x ∈ E := by
      have hxJ := hJmem (hclosure hx)
      have hxne : (N.coordinate_inverse x).2 ≠ T :=
        fun heq => hxS (hmemS.mpr ⟨hxJ.1, heq⟩)
      have hxlo : -L < (N.coordinate_inverse x).2 := by
        simpa only [he] using (N.coordinate_inverse_mem x hxJ.1).2.1
      exact ⟨⟨hxJ.1, hxlo, lt_of_le_of_ne hxJ.2 hxne⟩, hxV⟩
    have hclosureMinus : closure E ∩ Wminus ⊆ E := by
      intro x hx
      have hxV := hminusV hx.2
      apply hclosedBelow hx.1 hxV
      intro hxS
      exact ((hmemMinus hxV).mp hx.2).ne ((hequal hxV).mp hxS)
    have hclosurePlus : closure E ∩ Wplus ⊆ E := by
      intro x hx
      have hxV := hplusV hx.2
      apply hclosedBelow hx.1 hxV
      intro hxS
      exact ((hmemPlus hxV).mp hx.2).ne ((hequal hxV).mp hxS).symm
    let q0 : UnitTwoSphere := (N.coordinate_inverse N.center).1
    let y : M := N'.coordinate_map (q0, T)
    have hyD : (q0, T) ∈ Dplus := ⟨(hfbound q0).2.trans hTlo, hThi⟩
    have hyplus : y ∈ Wplus := ⟨_, hyD, rfl⟩
    have hynot : y ∉ E := by
      intro hyE
      have hybound := (hoverlap ⟨hyE.1.1, hyE.2⟩).2.2.2
      change (N'.coordinate_inverse (N'.coordinate_map (q0, T))).2 < L / 2 at hybound
      rw [N'.coordinate_inverse_map (q0, T) (hplusD hyD).2] at hybound
      exact (not_lt_of_gt hTlo) hybound
    have hplusAvoid : Disjoint Wplus E := by
      apply Set.disjoint_left.mpr
      intro x hxplus hxE
      have hsubE := hplus.isPreconnected.subset_of_closure_inter_subset hEopen
        ⟨x, hxplus, hxE⟩ hclosurePlus
      exact hynot (hsubE hyplus)
    let r : ℝ := 5 * L / 8
    let x0 : M := N.coordinate_map (q0, r)
    have hr : r ∈ Ioo (L / 2) T := by
      dsimp only [r, T]
      constructor <;> linarith
    have hrdom : r ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      rw [he]
      exact ⟨by linarith [hr.1], hr.2.trans hThi⟩
    have hx0old : x0 ∈ N.region (L / 2) L := by
      refine ⟨N.coordinate_map_mem ⟨mem_univ _, hrdom⟩, ?_⟩
      simpa only [x0, N.coordinate_inverse_map (q0, r) hrdom, mem_Ioo] using
        (show r ∈ Ioo (L / 2) L from ⟨hr.1, hr.2.trans hThi⟩)
    have hx0V : x0 ∈ N'.carrier := hquarter hx0old
    have hx0E : x0 ∈ E := by
      refine ⟨⟨hx0old.1, ?_⟩, hx0V⟩
      simpa only [x0, N.coordinate_inverse_map (q0, r) hrdom, mem_Ioo] using
        (show r ∈ Ioo (-L) T from ⟨by linarith [hr.1], hr.2⟩)
    have hx0notS : x0 ∉ S := by
      intro hxS
      exact hx0E.1.2.2.ne (hmemS.mp hxS).2
    have hx0minus : x0 ∈ Wminus := by
      have hne : (N'.coordinate_inverse x0).2 ≠ f (N'.coordinate_inverse x0).1 :=
        fun heq => hx0notS ((hequal hx0V).mpr heq)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact (hmemMinus hx0V).mpr hlt
      · exact False.elim (Set.disjoint_left.mp hplusAvoid ((hmemPlus hx0V).mpr hgt) hx0E)
    have hminusE : Wminus ⊆ E :=
      hminus.isPreconnected.subset_of_closure_inter_subset hEopen
        ⟨x0, hx0minus, hx0E⟩ hclosureMinus
    obtain ⟨qmin, _, hmin⟩ :=
      (isCompact_univ : IsCompact (univ : Set UnitTwoSphere)).exists_isMinOn
        ⟨q0, mem_univ _⟩ hf.continuousOn
    have hminle (q : UnitTwoSphere) : f qmin ≤ f q := hmin (mem_univ q)
    refine ⟨f qmin, (hfdom qmin).1, ?_, ?_⟩
    · intro x hx
      have hxV : x ∈ N'.carrier :=
        hquarter ⟨hx.1, hTlo.trans hx.2.1, hx.2.2⟩
      have hxnotS : x ∉ S := by
        intro hxS
        exact hx.2.1.ne ((hmemS.mp hxS).2).symm
      have hxnotMinus : x ∉ Wminus := by
        intro hxm
        exact (not_lt_of_gt hx.2.1) (hminusE hxm).1.2.2
      have hgt : f (N'.coordinate_inverse x).1 < (N'.coordinate_inverse x).2 := by
        have hne : (N'.coordinate_inverse x).2 ≠ f (N'.coordinate_inverse x).1 :=
          fun heq => hxnotS ((hequal hxV).mpr heq)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact False.elim (hxnotMinus ((hmemMinus hxV).mpr hlt))
        · exact hgt
      exact ⟨hxV, (hminle _).trans_lt hgt, (hoverlap ⟨hx.1, hxV⟩).2.2.2⟩
    · intro x hxV hxlt
      have hxE : x ∈ E := hminusE ((hmemMinus hxV).mpr (hxlt.trans_le (hminle _)))
      exact ⟨hxE.1.1, (hoverlap ⟨hxE.1.1, hxV⟩).1.2.1, hxE.1.2.2⟩
  let m : ℤ → ℝ := fun i =>
    if h : i ∈ C.shape.active ∧ i + 1 ∈ C.shape.active then
      Classical.choose (hpair i h.1 h.2) else 0
  have hm (i : ℤ) (hi : i ∈ C.shape.active) (hi1 : i + 1 ∈ C.shape.active) :
      -L < m i ∧
        (∀ x ∈ (C.neck i).region T L,
          x ∈ (C.neck (i + 1)).carrier ∧
            m i < ((C.neck (i + 1)).coordinate_inverse x).2 ∧
              ((C.neck (i + 1)).coordinate_inverse x).2 < L / 2) ∧
        (∀ x ∈ (C.neck (i + 1)).carrier,
          ((C.neck (i + 1)).coordinate_inverse x).2 < m i →
            x ∈ (C.neck i).region (-L / 2) T) := by
    simpa only [m, dif_pos (And.intro hi hi1)] using Classical.choose_spec (hpair i hi hi1)
  let lo : ℤ → ℝ := fun i =>
    if i ∈ C.shape.active ∧ a < i then
      (-L + min (-L / 2) (m (i - 1))) / 2 else -L / 2
  have hloa : lo a = -L / 2 := by simp [lo]
  have hlo (i : ℤ) (hi : i ∈ C.shape.active) : -L < lo i ∧ lo i ≤ -L / 2 := by
    by_cases hai : a < i
    · have hprev : i - 1 ∈ C.shape.active :=
        (hactive _).mpr (by have hib := ((hactive i).mp hi).2; constructor <;> omega)
      have hprevnext : i - 1 + 1 ∈ C.shape.active := by simpa only [sub_add_cancel] using hi
      have hmlower := (hm (i - 1) hprev hprevnext).1
      have hminlower : -L < min (-L / 2) (m (i - 1)) := lt_min (by linarith) hmlower
      have hminupper := min_le_left (-L / 2) (m (i - 1))
      simp only [lo, if_pos (And.intro hi hai)]
      constructor <;> linarith
    · simp only [lo, hai, and_false, if_false]
      constructor <;> linarith
  have hnextlo (i : ℤ) (hi : i ∈ C.shape.active) (hi1 : i + 1 ∈ C.shape.active) :
      lo (i + 1) < m i := by
    have hai : a < i + 1 := by have hai := ((hactive i).mp hi).1; omega
    have hmlower := (hm i hi hi1).1
    have hminupper := min_le_right (-L / 2) (m i)
    simp only [lo, if_pos (And.intro hi1 hai), add_sub_cancel_right]
    linarith
  let K : Set M := ⋃ i ∈ C.shape.active,
    (C.neck i).coordinate_map '' (univ ×ˢ Icc (lo i) T)
  have hKcompact : IsCompact K := by
    apply hfinite.isCompact_biUnion
    intro i hi
    apply (C.neck i).isCompact_coordinate_slab
    · rw [C.epsilon_eq i hi]
      exact (hlo i hi).1
    · rw [C.epsilon_eq i hi]
      exact hThi
  have hKU : K ⊆ U := by
    intro x hx
    obtain ⟨i, hi, z, hz, rfl⟩ := mem_iUnion₂.mp hx
    refine mem_iUnion₂.mpr ⟨i, hi, (C.neck i).coordinate_map_mem ?_⟩
    rw [EpsilonNeck.cylinderDomain, C.epsilon_eq i hi]
    exact ⟨mem_univ _, (hlo i hi).1.trans_le hz.2.1, hz.2.2.trans_lt hThi⟩
  have hmemK (i : ℤ) (hi : i ∈ C.shape.active) {x : M}
      (hx : x ∈ (C.neck i).carrier)
      (hxlo : lo i ≤ ((C.neck i).coordinate_inverse x).2)
      (hxhi : ((C.neck i).coordinate_inverse x).2 ≤ T) : x ∈ K :=
    mem_iUnion₂.mpr ⟨i, hi, (C.neck i).coordinate_inverse x,
      ⟨mem_univ _, hxlo, hxhi⟩, (C.neck i).coordinate_map_inverse hx⟩
  have hcover : U = (K ∪ (C.neck a).region (-L) (lo a)) ∪
      (C.neck b).region T L := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      have hxiheight : ((C.neck i).coordinate_inverse x).2 ∈ Ioo (-L) L := by
        simpa only [C.epsilon_eq i hi] using ((C.neck i).coordinate_inverse_mem x hxi).2
      by_cases hxlo : ((C.neck i).coordinate_inverse x).2 < lo i
      · by_cases hia : i = a
        · subst i
          exact Or.inl (Or.inr ⟨hxi, hxiheight.1, hxlo⟩)
        · have hprev : i - 1 ∈ C.shape.active :=
            (hactive _).mpr (by obtain ⟨hai, hib⟩ := (hactive i).mp hi; constructor <;> omega)
          have hprevnext : i - 1 + 1 ∈ C.shape.active := by simpa only [sub_add_cancel] using hi
          have hcut : lo i < m (i - 1) := by
            simpa only [sub_add_cancel] using hnextlo (i - 1) hprev hprevnext
          have hprevlow := (hm (i - 1) hprev hprevnext).2.2
          have hxprev : x ∈ (C.neck (i - 1)).region (-L / 2) T := by
            apply hprevlow x
            · simpa only [sub_add_cancel] using hxi
            · simpa only [sub_add_cancel] using hxlo.trans hcut
          exact Or.inl (Or.inl (hmemK (i - 1) hprev hxprev.1
            ((hlo (i - 1) hprev).2.trans hxprev.2.1.le) hxprev.2.2.le))
      · by_cases hxhi : T < ((C.neck i).coordinate_inverse x).2
        · by_cases hib : i = b
          · subst i
            exact Or.inr ⟨hxi, hxhi, hxiheight.2⟩
          · have hnext : i + 1 ∈ C.shape.active :=
              (hactive _).mpr (by obtain ⟨hai, hib'⟩ := (hactive i).mp hi; constructor <;> omega)
            have hxnext := (hm i hi hnext).2.1 x ⟨hxi, hxhi, hxiheight.2⟩
            exact Or.inl (Or.inl (hmemK (i + 1) hnext hxnext.1
              ((hnextlo i hi hnext).trans hxnext.2.1).le (hxnext.2.2.trans hTlo).le))
        · exact Or.inl (Or.inl (hmemK i hi hxi (le_of_not_gt hxlo) (le_of_not_gt hxhi)))
    · intro x hx
      rcases hx with (hxK | hxneg) | hxpos
      · exact hKU hxK
      · exact mem_iUnion₂.mpr ⟨a, ha, hxneg.1⟩
      · exact mem_iUnion₂.mpr ⟨b, hb, hxpos.1⟩
  exact ⟨lo, hlo, hloa, hKcompact, hcover⟩

end PoincareConjecture
