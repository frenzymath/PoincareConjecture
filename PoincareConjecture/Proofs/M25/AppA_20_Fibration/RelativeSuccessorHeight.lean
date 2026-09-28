import PoincareConjecture.Proofs.M25.AppA_1_Necks.SliceProjectionDifferential
import PoincareConjecture.Proofs.M25.Mathlib.FiberwiseGraphComplement
import Mathlib.Topology.Order.Compact











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

open Classical in



theorem EpsilonNeck.exists_relative_successor_height_continuity :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon = N.epsilon →
        let L := N.epsilon⁻¹
        N.region (L / 2) L ⊆ N'.carrier →
        N.carrier ∩ N'.carrier ⊆
          N.region (-L / 2) L ∩ N'.region (-L) (L / 2) →
        ∀ (X : Set M), N.carrier ⊆ X → N'.carrier ⊆ X →
        ∀ (F : M → ℝ), ContinuousOn F X →
          (∀ x ∈ N.carrier, F x = (N.coordinate_inverse x).2) →
          (∀ x ∈ X, x ∉ N.carrier → F x = -L ∨ F x = L) →
          ContinuousOn
            (fun x => if x ∈ N'.carrier then
              (N'.coordinate_inverse x).2
            else if F x < 3 * L / 4 then -L else L) X := by
  obtain ⟨epsilon0, hpos, hcap, hgraph⟩ :=
    EpsilonNeck.exists_contained_slice_graph.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN he
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let L : ℝ := N.epsilon⁻¹
  let T : ℝ := 3 * L / 4
  dsimp only
  intro hquarter hoverlap X hNX hVX F hFc hFin hFplateau
  let G : M → ℝ := fun x => if x ∈ N'.carrier then
    (N'.coordinate_inverse x).2 else if F x < T then -L else L
  change ContinuousOn G X
  have hL : 0 < L := inv_pos.mpr N.epsilon_pos
  have hTlo : L / 2 < T := by dsimp only [T]; linarith only [hL]
  have hThi : T < L := by dsimp only [T]; linarith only [hL]
  have hTneg : -L < T := by linarith only [hL, hTlo]
  have hTN : T ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := ⟨hTneg, hThi⟩
  have hsub (q : UnitTwoSphere) : N.coordinate_map (q, T) ∈ N'.carrier := by
    apply hquarter
    refine ⟨N.coordinate_map_mem ⟨mem_univ _, hTN⟩, ?_⟩
    simpa only [N.coordinate_inverse_map (q, T) hTN, mem_Ioo] using
      (show T ∈ Ioo (L / 2) L from ⟨hTlo, hThi⟩)
  have hN' : N'.epsilon ≤ epsilon0 := by rw [he]; exact hN
  obtain ⟨f, hfs, hfdom0, hfrange⟩ := (hgraph N' N hN' hN T hTN hsub).1
  have hf : Continuous f := hfs.continuous
  have hfdom (q : UnitTwoSphere) : f q ∈ Ioo (-L) L := by
    simpa only [he] using hfdom0 q
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
  have hSV : S ⊆ N'.carrier := by
    rintro x ⟨q, rfl⟩
    exact hsub q
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
    simpa only [he] using (N'.coordinate_inverse_mem x hx).2
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
    rw [EpsilonNeck.cylinderDomain, he]
    exact ⟨mem_univ _, hz.1, hz.2.trans (hfdom z.1).2⟩
  have hplusD : Dplus ⊆ N'.cylinderDomain := by
    intro z hz
    rw [EpsilonNeck.cylinderDomain, he]
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
  have hJcompact : IsCompact J :=
    N.isCompact_coordinate_slab (by change -L < -L / 2; linarith only [hL]) hThi
  have hclosure : closure E ⊆ J := closure_minimal hEJ hJcompact.isClosed
  have hJmem {x : M} (hx : x ∈ J) :
      x ∈ N.carrier ∧ (N.coordinate_inverse x).2 ≤ T := by
    rcases hx with ⟨z, hz, rfl⟩
    have hzdom : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      ⟨by change -L < z.2; linarith only [hL, hz.2.1], hz.2.2.trans_lt hThi⟩
    exact ⟨N.coordinate_map_mem ⟨mem_univ _, hzdom⟩,
      by simpa only [N.coordinate_inverse_map z hzdom] using hz.2.2⟩
  have hclosedBelow {x : M} (hx : x ∈ closure E) (hxV : x ∈ N'.carrier)
      (hxS : x ∉ S) : x ∈ E := by
    have hxJ := hJmem (hclosure hx)
    have hxne : (N.coordinate_inverse x).2 ≠ T :=
      fun heq => hxS (hmemS.mpr ⟨hxJ.1, heq⟩)
    have hxlo : -L < (N.coordinate_inverse x).2 :=
      (N.coordinate_inverse_mem x hxJ.1).2.1
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
    constructor <;> linarith only [hL]
  have hrdom : r ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨by change -L < r; linarith only [hL, hr.1], hr.2.trans hThi⟩
  have hx0old : x0 ∈ N.region (L / 2) L := by
    refine ⟨N.coordinate_map_mem ⟨mem_univ _, hrdom⟩, ?_⟩
    simpa only [x0, N.coordinate_inverse_map (q0, r) hrdom, mem_Ioo] using
      (show r ∈ Ioo (L / 2) L from ⟨hr.1, hr.2.trans hThi⟩)
  have hx0V : x0 ∈ N'.carrier := hquarter hx0old
  have hx0E : x0 ∈ E := by
    refine ⟨⟨hx0old.1, ?_⟩, hx0V⟩
    simpa only [x0, N.coordinate_inverse_map (q0, r) hrdom, mem_Ioo] using
      (show r ∈ Ioo (-L) T from ⟨by linarith only [hL, hr.1], hr.2⟩)
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
  have hlevel {x : M} (hx : x ∈ X) : F x = T ↔ x ∈ S := by
    constructor
    · intro hFT
      by_cases hxN : x ∈ N.carrier
      · exact hmemS.mpr ⟨hxN, (hFin x hxN).symm.trans hFT⟩
      · rcases hFplateau x hx hxN with hlo | hhi
        · exact False.elim (hTneg.ne (hlo.symm.trans hFT))
        · exact False.elim (hThi.ne (hFT.symm.trans hhi))
    · intro hxS
      exact (hFin x (hmemS.mp hxS).1).trans (hmemS.mp hxS).2
  have hminusF (x : M) (hx : x ∈ Wminus) : F x < T := by
    rw [hFin x (hminusE hx).1.1]
    exact (hminusE hx).1.2.2
  let r1 : ℝ := 7 * L / 8
  let x1 : M := N.coordinate_map (q0, r1)
  have hr1 : r1 ∈ Ioo T L := by
    dsimp only [r1, T]
    constructor <;> linarith only [hL]
  have hr1dom : r1 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨hTneg.trans hr1.1, hr1.2⟩
  have hx1old : x1 ∈ N.region (L / 2) L := by
    refine ⟨N.coordinate_map_mem ⟨mem_univ _, hr1dom⟩, ?_⟩
    simpa only [x1, N.coordinate_inverse_map (q0, r1) hr1dom, mem_Ioo] using
      (show r1 ∈ Ioo (L / 2) L from ⟨hTlo.trans hr1.1, hr1.2⟩)
  have hx1V : x1 ∈ N'.carrier := hquarter hx1old
  have hx1height : (N.coordinate_inverse x1).2 = r1 :=
    congrArg Prod.snd (N.coordinate_inverse_map (q0, r1) hr1dom)
  have hx1notS : x1 ∉ S := by
    intro hxS
    have hF := (hlevel (hNX hx1old.1)).mpr hxS
    rw [hFin x1 hx1old.1, hx1height] at hF
    exact hr1.1.ne hF.symm
  have hx1plus : x1 ∈ Wplus := by
    have hne : (N'.coordinate_inverse x1).2 ≠ f (N'.coordinate_inverse x1).1 :=
      fun heq => hx1notS ((hequal hx1V).mpr heq)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hxE := hminusE ((hmemMinus hx1V).mpr hlt)
      have hxlt : r1 < T := hx1height ▸ hxE.1.2.2
      exact False.elim ((not_lt_of_gt hr1.1) hxlt)
    · exact (hmemPlus hx1V).mpr hgt
  have hplusF (x : M) (hx : x ∈ Wplus) : T < F x := by
    apply hplus.isPreconnected.lt_of_ne (hFc.mono (hplusV.trans hVX)) ?_ ?_ hx
    · intro z hz hFT
      have hzV := hplusV hz
      have hzS := (hlevel (hVX hzV)).mp hFT
      exact ((hmemPlus hzV).mp hz).ne ((hequal hzV).mp hzS).symm
    · refine ⟨x1, hx1plus, ?_⟩
      rw [hFin x1 hx1old.1, hx1height]
      exact hr1.1
  have hbelow {x : M} (hx : x ∈ N'.carrier) (hFx : F x < T) :
      (N'.coordinate_inverse x).2 < f (N'.coordinate_inverse x).1 := by
    by_contra h
    rcases eq_or_lt_of_le (le_of_not_gt h) with heq | hgt
    · exact hFx.ne ((hlevel (hVX hx)).mpr ((hequal hx).mpr heq.symm))
    · exact (not_lt_of_gt hFx) (hplusF x ((hmemPlus hx).mpr hgt))
  have habove {x : M} (hx : x ∈ N'.carrier) (hFx : T < F x) :
      f (N'.coordinate_inverse x).1 < (N'.coordinate_inverse x).2 := by
    by_contra h
    rcases eq_or_lt_of_le (le_of_not_gt h) with heq | hlt
    · exact hFx.ne ((hlevel (hVX hx)).mpr ((hequal hx).mpr heq)).symm
    · exact (not_lt_of_gt hFx) (hminusF x ((hmemMinus hx).mpr hlt))
  obtain ⟨qmin, _, hmin⟩ :=
    (isCompact_univ : IsCompact (univ : Set UnitTwoSphere)).exists_isMinOn
      ⟨q0, mem_univ _⟩ hf.continuousOn
  have hminle (q : UnitTwoSphere) : f qmin ≤ f q := hmin (mem_univ q)
  have hslab (c d : ℝ) (hc : -L < c) (hd : d < L) :
      IsClosed (N'.coordinate_map '' (univ ×ˢ Icc c d)) ∧
        N'.coordinate_map '' (univ ×ˢ Icc c d) ⊆ N'.carrier := by
    constructor
    · apply (N'.isCompact_coordinate_slab ?_ ?_).isClosed
      · simpa only [he] using hc
      · simpa only [he] using hd
    · rintro x ⟨z, hz, rfl⟩
      apply N'.coordinate_map_mem
      refine ⟨mem_univ _, ?_⟩
      simpa only [he] using
        (show z.2 ∈ Ioo (-L) L from ⟨hc.trans_le hz.2.1, hz.2.2.trans_lt hd⟩)
  have hGin (x : M) (hx : x ∈ N'.carrier) : G x = (N'.coordinate_inverse x).2 := by
    simp only [G, if_pos hx]
  have hGout (x : M) (hx : x ∉ N'.carrier) : G x = if F x < T then -L else L := by
    simp only [G, if_neg hx]
  have hGbounds (x : M) : G x ∈ Icc (-L) L := by
    by_cases hx : x ∈ N'.carrier
    · rw [hGin x hx]
      exact ⟨(hnewheight hx).1.le, (hnewheight hx).2.le⟩
    · rw [hGout x hx]
      split_ifs <;> constructor <;> linarith only [hL]

  intro x hxX
  by_cases hxV : x ∈ N'.carrier
  · have hc := N'.coordinate_inverse_smooth.continuousOn.continuousAt
      (N'.carrier_open.mem_nhds hxV)
    have hGc : ContinuousAt G x := by
      apply hc.snd.congr_of_eventuallyEq
      filter_upwards [N'.carrier_open.mem_nhds hxV] with y hy
      exact hGin y hy
    exact hGc.continuousWithinAt
  · have hne : F x ≠ T := fun h => hxV (hSV ((hlevel hxX).mp h))
    have hFt : Filter.Tendsto F (nhdsWithin x X) (nhds (F x)) := hFc x hxX
    rcases lt_or_gt_of_ne hne with hFx | hFx
    · change Filter.Tendsto G (nhdsWithin x X) (nhds (G x))
      rw [hGout x hxV, if_pos hFx]
      apply tendsto_order.mpr
      constructor
      · intro d hd
        exact Filter.Eventually.of_forall fun y => hd.trans_le (hGbounds y).1
      · intro d hd
        let K := N'.coordinate_map '' (univ ×ˢ Icc d (L / 2))
        obtain ⟨hKclosed, hKsub⟩ := hslab d (L / 2) hd (by linarith only [hL])
        have hxK : x ∉ K := fun h => hxV (hKsub h)
        have hnear : {y | F y < T} ∈ nhdsWithin x X :=
          hFt.eventually (isOpen_Iio.mem_nhds hFx)
        have havoid : Kᶜ ∈ nhdsWithin x X :=
          mem_nhdsWithin_of_mem_nhds (hKclosed.isOpen_compl.mem_nhds hxK)
        filter_upwards [hnear, havoid] with y hyF hyK
        by_cases hyV : y ∈ N'.carrier
        · rw [hGin y hyV]
          have hhi := (hbelow hyV hyF).trans (hfbound (N'.coordinate_inverse y).1).2
          by_contra h
          exact hyK ⟨N'.coordinate_inverse y,
            ⟨mem_univ _, le_of_not_gt h, hhi.le⟩, N'.coordinate_map_inverse hyV⟩
        · rw [hGout y hyV, if_pos hyF]
          exact hd
    · change Filter.Tendsto G (nhdsWithin x X) (nhds (G x))
      rw [hGout x hxV, if_neg (not_lt_of_gt hFx)]
      apply tendsto_order.mpr
      constructor
      · intro d hd
        let K := N'.coordinate_map '' (univ ×ˢ Icc (f qmin) d)
        obtain ⟨hKclosed, hKsub⟩ := hslab (f qmin) d (hfdom qmin).1 hd
        have hxK : x ∉ K := fun h => hxV (hKsub h)
        have hnear : {y | T < F y} ∈ nhdsWithin x X :=
          hFt.eventually (isOpen_Ioi.mem_nhds hFx)
        have havoid : Kᶜ ∈ nhdsWithin x X :=
          mem_nhdsWithin_of_mem_nhds (hKclosed.isOpen_compl.mem_nhds hxK)
        filter_upwards [hnear, havoid] with y hyF hyK
        by_cases hyV : y ∈ N'.carrier
        · rw [hGin y hyV]
          have hlo := (hminle (N'.coordinate_inverse y).1).trans_lt (habove hyV hyF)
          by_contra h
          exact hyK ⟨N'.coordinate_inverse y,
            ⟨mem_univ _, hlo.le, le_of_not_gt h⟩, N'.coordinate_map_inverse hyV⟩
        · rw [hGout y hyV, if_neg (not_lt_of_gt hyF)]
          exact hd
      · intro d hd
        exact Filter.Eventually.of_forall fun y => (hGbounds y).2.trans_lt hd

end PoincareConjecture
