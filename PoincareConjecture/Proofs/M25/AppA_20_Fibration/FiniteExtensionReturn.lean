import PoincareConjecture.Proofs.M25.AppA_20_Fibration.RelativeSuccessorHeight
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.IntrinsicFiniteChain
import PoincareConjecture.Proofs.M25.AppA_1_Necks.OrientedFrontierGraph
import PoincareConjecture.Proofs.M25.AppA_1_Necks.ClosedFrontierQuarters
import PoincareConjecture.Proofs.M25.AppA_1_Necks.TransitionHeight
import PoincareConjecture.Proofs.M25.Mathlib.PlateauMeanValue
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Order.IntermediateValue
import PoincareConjecture.Proofs.M25.AppA_1_Necks.RelativeHeightControl

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture

theorem BalancedNeckChain.exists_finite_forward_extension_or_deep_return :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon) {a b : ℤ},
      C.shape = ChainShape.finite a b → epsilon ≤ epsilon0 →
      ∀ (N' : EpsilonNeck g), N' ∈ C.source_necks →
      N'.epsilon = epsilon →
      N'.center ∈ closure ((C.neck b).region 0 epsilon⁻¹) →
      N'.center ∉ (⋃ i ∈ C.shape.active, (C.neck i).carrier) →
      (∃ (R : EpsilonNeck g) (D : BalancedNeckChain g epsilon),
        (R = N' ∨ R = N'.reverse) ∧ R.SameUpToReversal N' ∧
        D.shape = ChainShape.finite a (b + 1) ∧
        D.source_necks = C.source_necks ∧
        D.neck = Function.update C.neck (b + 1) R ∧
        closure ((C.neck b).region (epsilon⁻¹ / 2) epsilon⁻¹) ⊆
          R.carrier ∧
        closure (R.region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) ⊆
          (C.neck b).carrier) ∨
      (∀ c ∈ Ioo (-epsilon⁻¹) 0,
        ¬ Disjoint N'.carrier ((C.neck a).region (-epsilon⁻¹) c)) := by
  classical
  obtain ⟨et, htpos, htcap, htransport⟩ :=
    EpsilonNeck.exists_relative_successor_height_continuity.{u}
  obtain ⟨el, hlpos, _, hlower⟩ := EpsilonNeck.exists_relative_height_lower_control.{u}
  obtain ⟨eo, hopos, _, horient⟩ := EpsilonNeck.exists_oriented_positive_frontier_graph.{u}
  obtain ⟨ep, hppos, _, hfront⟩ := EpsilonNeck.exists_positive_frontier_quarter_control.{u}
  obtain ⟨ec, hcpos, _, hclosed⟩ :=
    EpsilonNeck.exists_positive_frontier_closed_quarter_control.{u}
  obtain ⟨es, hspos, _, hscale⟩ :=
    EpsilonNeck.exists_intersecting_scale_control.{u} (α := (1 / 1000 : ℝ))
      (by norm_num)
  obtain ⟨ea, hapos, _, _⟩ :=
    EpsilonNeck.exists_intersecting_axial_derivative_control.{u}
      (η := (1 / 1000 : ℝ)) (by norm_num)
  let B0 : ℝ := Real.sqrt 2 * (Real.pi + 1)
  have hB0 : 0 < B0 := by dsimp only [B0]; positivity
  have hden : 0 < 10000 * (B0 + 1) := by positivity
  refine ⟨min et (min el (min eo (min ep (min ec (min es (min ea
    (min (1 / 10000) (1 / (10000 * (B0 + 1)))))))))),
    lt_min htpos (lt_min hlpos (lt_min hopos (lt_min hppos (lt_min hcpos
      (lt_min hspos (lt_min hapos (lt_min (by norm_num) (div_pos zero_lt_one hden)))))))),
    (min_le_left _ _).trans htcap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C a b hshape hepsilon N' hsource heN' hy hyout
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let L : ℝ := epsilon⁻¹
  let N := C.neck a
  let B := C.neck b
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  change N'.center ∈ closure (B.region 0 L) at hy
  change N'.center ∉ U at hyout
  by_cases hreturn : ∀ c ∈ Ioo (-L) 0, ¬ Disjoint N'.carrier (N.region (-L) c)
  · exact Or.inr hreturn
  push Not at hreturn
  obtain ⟨c, hc, hcut⟩ := hreturn
  rcases le_min_iff.mp hepsilon with ⟨het, hrest⟩
  rcases le_min_iff.mp hrest with ⟨hel, hrest⟩
  rcases le_min_iff.mp hrest with ⟨heo, hrest⟩
  rcases le_min_iff.mp hrest with ⟨hep, hrest⟩
  rcases le_min_iff.mp hrest with ⟨hec, hrest⟩
  rcases le_min_iff.mp hrest with ⟨hes, hrest⟩
  rcases le_min_iff.mp hrest with ⟨_, hrest⟩
  rcases le_min_iff.mp hrest with ⟨henum, hebudget⟩
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by rw [hshape]; rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact ((hactive i).mp hi).1.trans ((hactive i).mp hi).2
  have ha : a ∈ C.shape.active := (hactive a).mpr ⟨le_rfl, hab⟩
  have hb : b ∈ C.shape.active := (hactive b).mpr ⟨hab, le_rfl⟩
  have heN : N.epsilon = epsilon := C.epsilon_eq a ha
  have heB : B.epsilon = epsilon := C.epsilon_eq b hb
  have hepos : 0 < epsilon := heN ▸ N.epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepos
  have hBscale : 0 < B.scale := B.scale_pos
  have hNU (i : ℤ) (hi : i ∈ C.shape.active) : (C.neck i).carrier ⊆ U :=
    fun _ hx => mem_iUnion₂.mpr ⟨i, hi, hx⟩
  have hyB : N'.center ∉ B.carrier := fun hx => hyout (hNU b hb hx)
  have hycl : N'.center ∈ closure (B.region 0 B.epsilon⁻¹) := by
    simpa only [heB] using hy
  obtain ⟨R, f, hchoice, hfs, hfdom, hfquant, hgraph⟩ :=
    horient B N' (by rw [heB]; exact heo) (heN'.trans heB.symm) hycl hyB
  have heR : R.epsilon = epsilon := by rcases hchoice with rfl | rfl <;> exact heN'
  have hRc : R.center = N'.center := by rcases hchoice with rfl | rfl <;> rfl
  have hRu : R.carrier = N'.carrier := by rcases hchoice with rfl | rfl <;> rfl
  have hselected : R.SameUpToReversal N' := by
    rcases hchoice with rfl | rfl
    · refine ⟨rfl, rfl, rfl, rfl, rfl, 1, Or.inl rfl, ?_⟩
      intro z _
      simp
    · refine ⟨rfl, rfl, rfl, rfl, rfl, -1, Or.inr rfl, ?_⟩
      intro z _
      change N'.coordinate_map (z.1, -z.2) = N'.coordinate_map (z.1, -1 * z.2)
      simp
  have hyR : R.center ∉ U := by rw [hRc]; exact hyout
  have hyRcl : R.center ∈ closure (B.region 0 B.epsilon⁻¹) := by rw [hRc]; exact hycl
  have hyRB : R.center ∉ B.carrier := by rw [hRc]; exact hyB
  have hcutR : Disjoint R.carrier (N.region (-L) c) := by rw [hRu]; exact hcut
  have hcR := (R.mem_central_sphere_iff R.center).mp R.center_on_central_sphere
  let W : Set M := U ∪ R.carrier
  have hUW : U ⊆ W := subset_union_left
  have hRW : R.carrier ⊆ W := subset_union_right
  have hNW (i : ℤ) (hi : i ∈ C.shape.active) : (C.neck i).carrier ⊆ W :=
    (hNU i hi).trans hUW
  have hopenU : IsOpen U :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => (C.neck i).carrier_open
  let P : ℤ → Prop := fun i => ∃ F : M → ℝ,
    ContinuousOn F W ∧
      (∀ x ∈ (C.neck i).carrier, F x = ((C.neck i).coordinate_inverse x).2) ∧
      (∀ x ∈ W, x ∉ (C.neck i).carrier → F x = -L ∨ F x = L) ∧
      (∀ x ∈ W, x ∉ U → F x = L)
  have hbase : P a := by
    let F : M → ℝ := fun x => if x ∈ N.carrier then (N.coordinate_inverse x).2 else L
    have hFin (x : M) (hx : x ∈ N.carrier) : F x = (N.coordinate_inverse x).2 := by
      simp only [F, if_pos hx]
    have hFout (x : M) (hx : x ∉ N.carrier) : F x = L := by
      simp only [F, if_neg hx]
    have hFbound (x : M) : F x ≤ L := by
      by_cases hx : x ∈ N.carrier
      · rw [hFin x hx]
        simpa only [heN] using (N.coordinate_inverse_mem x hx).2.2.le
      · rw [hFout x hx]
    have hFU : ContinuousOn F U := (C.continuousOn_initial_height_of_finite hshape).1
    have hcont (x : M) (hx : x ∈ W) : ContinuousAt F x := by
      by_cases hxU : x ∈ U
      · exact hFU.continuousAt (hopenU.mem_nhds hxU)
      have hxR : x ∈ R.carrier := hx.resolve_left hxU
      by_cases hxN : x ∈ N.carrier
      · have hd := N.coordinate_inverse_smooth.continuousOn.continuousAt
          (N.carrier_open.mem_nhds hxN)
        apply hd.snd.congr_of_eventuallyEq
        filter_upwards [N.carrier_open.mem_nhds hxN] with z hz
        exact hFin z hz
      · change Filter.Tendsto F (nhds x) (nhds (F x))
        rw [hFout x hxN]
        apply tendsto_order.mpr
        constructor
        · intro d hd
          let K := N.coordinate_map '' (univ ×ˢ Icc c d)
          have hKclosed : IsClosed K :=
            (N.isCompact_coordinate_slab (by rw [heN]; exact hc.1)
              (by rw [heN]; exact hd)).isClosed
          have hKsub : K ⊆ N.carrier := by
            rintro z ⟨w, hw, rfl⟩
            apply N.coordinate_map_mem
            refine ⟨mem_univ _, ?_, ?_⟩ <;> rw [heN]
            · exact hc.1.trans_le hw.2.1
            · exact hw.2.2.trans_lt hd
          have hxK : x ∉ K := fun h => hxN (hKsub h)
          filter_upwards [(R.carrier_open.inter hKclosed.isOpen_compl).mem_nhds
            ⟨hxR, hxK⟩] with z hz
          by_cases hzN : z ∈ N.carrier
          · rw [hFin z hzN]
            have hcz : c ≤ (N.coordinate_inverse z).2 := by
              by_contra h
              have hh := (N.coordinate_inverse_mem z hzN).2.1
              rw [heN] at hh
              exact Set.disjoint_left.mp hcutR hz.1 ⟨hzN, hh, lt_of_not_ge h⟩
            by_contra h
            exact hz.2 ⟨N.coordinate_inverse z, ⟨mem_univ _, hcz, le_of_not_gt h⟩,
              N.coordinate_map_inverse hzN⟩
          · rw [hFout z hzN]
            exact hd
        · intro d hd
          exact Filter.Eventually.of_forall fun z => (hFbound z).trans_lt hd
    refine ⟨F, continuousOn_of_forall_continuousAt hcont, hFin, ?_, ?_⟩
    · intro x _ hx
      exact Or.inr (hFout x hx)
    · intro x _ hx
      exact hFout x (fun h => hx (hNU a ha h))
  have hstep (i : ℤ) (hi : i ∈ C.shape.active) (hi1 : i + 1 ∈ C.shape.active)
      (hPi : P i) : P (i + 1) := by
    obtain ⟨F, hFc, hFin, hplateau, houtside⟩ := hPi
    let G : M → ℝ := fun x => if x ∈ (C.neck (i + 1)).carrier then
      ((C.neck (i + 1)).coordinate_inverse x).2 else if F x < 3 * L / 4 then -L else L
    have htrans := htransport (C.neck i) (C.neck (i + 1))
      (by rw [C.epsilon_eq i hi]; exact het)
      ((C.epsilon_eq (i + 1) hi1).trans (C.epsilon_eq i hi).symm)
    simp only [C.epsilon_eq i hi] at htrans
    have hGc : ContinuousOn G W := htrans
      (C.overlap_contains_quarters i hi hi1).1
      (C.overlap_within_three_quarters i hi hi1) W (hNW i hi) (hNW (i + 1) hi1)
      F hFc hFin hplateau
    refine ⟨G, hGc, ?_, ?_, ?_⟩
    · intro x hx
      simp only [G, if_pos hx]
    · intro x _ hx
      by_cases ht : F x < 3 * L / 4
      · exact Or.inl (by simp only [G, if_neg hx, if_pos ht])
      · exact Or.inr (by simp only [G, if_neg hx, if_neg ht])
    · intro x hx hxout
      have hxnext : x ∉ (C.neck (i + 1)).carrier := fun h => hxout (hNU (i + 1) hi1 h)
      have hFx := houtside x hx hxout
      simp only [G, if_neg hxnext, hFx, if_neg (by linarith only [hL] : ¬ L < 3 * L / 4)]
  have hPall (i : ℤ) (hi : i ∈ C.shape.active) : P i := by
    refine Int.leInduction (motive := fun j _ => j ≤ b → P j)
      (fun _ => hbase) ?_ i ((hactive i).mp hi).1 ((hactive i).mp hi).2
    intro j haj ih hjb
    have hj : j ∈ C.shape.active := (hactive j).mpr ⟨haj, by omega⟩
    have hj1 : j + 1 ∈ C.shape.active := (hactive (j + 1)).mpr ⟨by omega, hjb⟩
    exact hstep j hj hj1 (ih (by omega))
  have hcontrol (i : ℤ) (hi : i ∈ C.shape.active) (F : M → ℝ)
      (hFc : ContinuousOn F W)
      (hFin : ∀ x ∈ (C.neck i).carrier, F x = ((C.neck i).coordinate_inverse x).2)
      (hplateau : ∀ x ∈ W, x ∉ (C.neck i).carrier → F x = -L ∨ F x = L)
      (houtside : ∀ x ∈ W, x ∉ U → F x = L) :
      ∀ x ∈ R.carrier, -L / 5 < F x := by
    have h := hlower (C.neck i) R (by rw [C.epsilon_eq i hi]; exact hel)
      (heR.trans (C.epsilon_eq i hi).symm)
    simp only [C.epsilon_eq i hi] at h
    exact h W hRW F hFc hFin hplateau (houtside R.center (hRW hcR.1) hyR)
  have hexclusion (i : ℤ) (hi : i ∈ C.shape.active) :
      Disjoint R.carrier ((C.neck i).region (-L) (-L / 2)) := by
    obtain ⟨F, hFc, hFin, hplateau, houtside⟩ := hPall i hi
    apply Set.disjoint_left.mpr
    intro x hxR hxi
    have hlo := hcontrol i hi F hFc hFin hplateau houtside x hxR
    rw [hFin x hxi.1] at hlo
    linarith only [hlo, hxi.2.2, hL]
  obtain ⟨F, hFc, hFin, hplateau, houtside⟩ := hPall b hb
  have hBlower := hcontrol b hb F hFc hFin hplateau houtside
  have hFcenter : F R.center = L := houtside R.center (hRW hcR.1) hyR
  have hquarter : B.region (L / 2) L ⊆ R.carrier ∧
      ENNReal.ofReal ((0.99 : ℝ) * B.scale * L) ≤ g.edist B.center R.center ∧
      g.edist B.center R.center ≤ ENNReal.ofReal ((1.01 : ℝ) * B.scale * L) := by
    simpa only [heB] using hfront B R (by rw [heB]; exact hep)
      (heR.trans heB.symm) hyRcl hyRB
  have hclosedOld : closure (B.region (L / 2) L) ⊆ R.carrier := by
    simpa only [heB] using hclosed B R (by rw [heB]; exact hec)
      (heR.trans heB.symm) hyRcl hyRB
  have hinter : (B.carrier ∩ R.carrier).Nonempty := by
    obtain ⟨z, hzR, hzB⟩ := mem_closure_iff.mp hyRcl R.carrier R.carrier_open hcR.1
    exact ⟨z, hzB.1, hzR⟩
  let T : ℝ := 3 * L / 4
  let S : Set M := range (fun q : UnitTwoSphere => B.coordinate_map (q, T))
  have hT : T ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ := by
    rw [heB]
    change -L < T ∧ T < L
    dsimp only [T]
    constructor <;> linarith only [hL]
  have hf : Continuous f := hfs.continuous
  have hfstrip (q : UnitTwoSphere) : -L < f q ∧ f q < L := by
    simpa only [heR, Set.mem_Ioo, L] using hfdom q
  have hfquantL (q : UnitTwoSphere) : -(3 * L / 10) < f q ∧ f q < -(L / 5) := by
    simpa only [heB] using hfquant q
  have hgraphS : S = range (fun q : UnitTwoSphere => R.coordinate_map (q, f q)) := by
    simpa only [S, T, heB] using hgraph
  have hlevel (x : M) (hx : x ∈ R.carrier) : F x = T ↔ x ∈ S := by
    by_cases hxB : x ∈ B.carrier
    · rw [hFin x hxB]
      constructor
      · intro heq
        refine ⟨(B.coordinate_inverse x).1, ?_⟩
        rw [← heq]
        exact B.coordinate_map_inverse hxB
      · rintro ⟨q, rfl⟩
        rw [B.coordinate_inverse_map (q, T) hT]
    · have hne : F x ≠ T := by
        rcases hplateau x (hRW hx) hxB with h | h <;>
          dsimp only [T] <;> linarith only [h, hL]
      refine iff_of_false hne ?_
      rintro ⟨q, hq⟩
      exact hxB (hq ▸ B.coordinate_map_mem ⟨mem_univ _, hT⟩)
  have hequal (x : M) (hx : x ∈ R.carrier) :
      x ∈ S ↔ (R.coordinate_inverse x).2 = f (R.coordinate_inverse x).1 := by
    rw [hgraphS]
    constructor
    · rintro ⟨q, rfl⟩
      rw [R.coordinate_inverse_map (q, f q) (hfdom q)]
    · intro heq
      refine ⟨(R.coordinate_inverse x).1, ?_⟩
      change R.coordinate_map ((R.coordinate_inverse x).1,
        f (R.coordinate_inverse x).1) = x
      rw [← heq]
      exact R.coordinate_map_inverse hx
  let Dminus : Set RoundCylinderSpace := {z | -L < z.2 ∧ z.2 < f z.1}
  let Dplus : Set RoundCylinderSpace := {z | f z.1 < z.2 ∧ z.2 < L}
  let Wminus := R.coordinate_map '' Dminus
  let Wplus := R.coordinate_map '' Dplus
  have hminusD : Dminus ⊆ R.cylinderDomain := by
    intro z hz
    exact ⟨mem_univ _, by simpa only [heR] using
      (show z.2 ∈ Ioo (-L) L from ⟨hz.1, hz.2.trans (hfstrip z.1).2⟩)⟩
  have hplusD : Dplus ⊆ R.cylinderDomain := by
    intro z hz
    exact ⟨mem_univ _, by simpa only [heR] using
      (show z.2 ∈ Ioo (-L) L from ⟨(hfstrip z.1).1.trans hz.1, hz.2⟩)⟩
  have hminus : IsConnected Wminus :=
    (isConnected_between_continuous_graphs continuous_const hf
      (fun q => (hfstrip q).1)).image _ (R.coordinate_map_smooth.continuousOn.mono hminusD)
  have hplus : IsConnected Wplus :=
    (isConnected_between_continuous_graphs hf continuous_const
      (fun q => (hfstrip q).2)).image _ (R.coordinate_map_smooth.continuousOn.mono hplusD)
  have hminusR : Wminus ⊆ R.carrier := by
    rintro x ⟨z, hz, rfl⟩
    exact R.coordinate_map_mem (hminusD hz)
  have hplusR : Wplus ⊆ R.carrier := by
    rintro x ⟨z, hz, rfl⟩
    exact R.coordinate_map_mem (hplusD hz)
  have hmemMinus (x : M) (hx : x ∈ R.carrier) :
      x ∈ Wminus ↔ (R.coordinate_inverse x).2 < f (R.coordinate_inverse x).1 := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [R.coordinate_inverse_map z (hminusD hz).2] using hz.2
    · intro hlt
      have hd := (R.coordinate_inverse_mem x hx).2.1
      rw [heR] at hd
      exact ⟨R.coordinate_inverse x, ⟨hd, hlt⟩, R.coordinate_map_inverse hx⟩
  have hmemPlus (x : M) (hx : x ∈ R.carrier) :
      x ∈ Wplus ↔ f (R.coordinate_inverse x).1 < (R.coordinate_inverse x).2 := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [R.coordinate_inverse_map z (hplusD hz).2] using hz.1
    · intro hlt
      have hd := (R.coordinate_inverse_mem x hx).2.2
      rw [heR] at hd
      exact ⟨R.coordinate_inverse x, ⟨hlt, hd⟩, R.coordinate_map_inverse hx⟩
  have hplusF (x : M) (hx : x ∈ Wplus) : T < F x := by
    apply hplus.isPreconnected.lt_of_ne (hFc.mono (hplusR.trans hRW)) ?_ ?_ hx
    · intro z hz heq
      have hzR := hplusR hz
      have he := (hequal z hzR).mp ((hlevel z hzR).mp heq)
      exact ((hmemPlus z hzR).mp hz).ne he.symm
    · refine ⟨R.center, (hmemPlus _ hcR.1).mpr ?_, ?_⟩
      · rw [hcR.2]
        have h := (hfquantL (R.coordinate_inverse R.center).1).2
        linarith only [h, hL]
      · rw [hFcenter]
        dsimp only [T]
        linarith only [hL]
  let q0 := (B.coordinate_inverse B.center).1
  let x0 := B.coordinate_map (q0, 5 * L / 8)
  have hr0 : 5 * L / 8 ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ := by
    rw [heB]
    change -L < 5 * L / 8 ∧ 5 * L / 8 < L
    constructor <;> linarith only [hL]
  have hx0B : x0 ∈ B.carrier := B.coordinate_map_mem ⟨mem_univ _, hr0⟩
  have hx0height : (B.coordinate_inverse x0).2 = 5 * L / 8 :=
    congrArg Prod.snd (B.coordinate_inverse_map (q0, 5 * L / 8) hr0)
  have hx0R : x0 ∈ R.carrier := hquarter.1
    ⟨hx0B, by rw [hx0height]; constructor <;> linarith only [hL]⟩
  have hx0F : F x0 < T := by
    rw [hFin x0 hx0B, hx0height]
    dsimp only [T]
    linarith only [hL]
  have hx0minus : x0 ∈ Wminus := by
    apply (hmemMinus x0 hx0R).mpr
    by_contra h
    rcases eq_or_lt_of_le (le_of_not_gt h) with heq | hgt
    · exact hx0F.ne ((hlevel x0 hx0R).mpr ((hequal x0 hx0R).mpr heq.symm))
    · exact (not_lt_of_gt hx0F) (hplusF x0 ((hmemPlus x0 hx0R).mpr hgt))
  have hminusF (x : M) (hx : x ∈ Wminus) : F x < T := by
    apply hminus.isPreconnected.gt_of_ne (hFc.mono (hminusR.trans hRW)) ?_ ?_ hx
    · intro z hz heq
      have hzR := hminusR hz
      exact ((hmemMinus z hzR).mp hz).ne ((hequal z hzR).mp ((hlevel z hzR).mp heq))
    · exact ⟨x0, hx0minus, hx0F⟩
  let K := B.coordinate_map '' (univ ×ˢ Icc (-L / 5) T)
  have hKclosed : IsClosed K :=
    (B.isCompact_coordinate_slab (by rw [heB]; change -L < -L / 5; linarith only [hL])
      hT.2).isClosed
  have hKsub : K ⊆ B.carrier := by
    rintro x ⟨z, hz, rfl⟩
    apply B.coordinate_map_mem
    refine ⟨mem_univ _, ?_, hz.2.2.trans_lt hT.2⟩
    rw [heB]
    change -L < z.2
    linarith only [hz.2.1, hL]
  have hnegativeK : R.region (-L) (-L / 2) ⊆ K := by
    intro x hx
    have hxminus : x ∈ Wminus := (hmemMinus x hx.1).mpr (by
      have h := (hfquantL (R.coordinate_inverse x).1).1
      linarith only [h, hx.2.2, hL])
    have hlow := hBlower x hx.1
    have hhigh := hminusF x hxminus
    have hxB : x ∈ B.carrier := by
      by_contra hout
      rcases hplateau x (hRW hx.1) hout with h | h <;>
        dsimp only [T] at hhigh <;> linarith only [hlow, hhigh, h, hL]
    rw [hFin x hxB] at hlow hhigh
    exact ⟨B.coordinate_inverse x, ⟨mem_univ _, hlow.le, hhigh.le⟩,
      B.coordinate_map_inverse hxB⟩
  have hclosedNew : closure (R.region (-L) (-L / 2)) ⊆ B.carrier :=
    (closure_minimal hnegativeK hKclosed).trans hKsub
  have hB0L : B0 ≤ L / 1000 := by
    have h := (le_div_iff₀ hden).mp hebudget
    have he : B0 * epsilon ≤ 1 / 1000 := by nlinarith only [h, hepos]
    calc
      B0 ≤ (1 / 1000) / epsilon := (le_div_iff₀ hepos).mpr he
      _ = L / 1000 := by dsimp only [L]; ring
  have hsqlo : (99 : ℝ) / 100 ≤ Real.sqrt (1 - epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [henum])
  have hsqhi : Real.sqrt (1 + epsilon) ≤ (101 : ℝ) / 100 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith only [henum]⟩
  have hratio := (hscale B R (by rw [heB]; exact hes)
    (by rw [heR]; exact hes) hinter).2
  have hscaleLower : (99 : ℝ) / 100 * B.scale ≤ R.scale := by
    apply (le_div_iff₀ B.scale_pos).mp
    linarith only [(abs_lt.mp hratio).1]
  have hprodLower : (9801 : ℝ) / 10000 * B.scale ≤ R.scale * Real.sqrt (1 - epsilon) := by
    calc
      _ = ((99 / 100 : ℝ) * B.scale) * (99 / 100) := by ring
      _ ≤ _ := mul_le_mul hscaleLower hsqlo (by norm_num) R.scale_pos.le
  have hnewLower (x : M) (hx : x ∈ R.carrier) :
      ENNReal.ofReal ((9801 : ℝ) / 10000 * B.scale * |(R.coordinate_inverse x).2|) ≤
        g.edist x R.center := by
    have hdiff : R.axialDepth x - R.axialDepth R.center =
        -|(R.coordinate_inverse x).2| := by
      simp only [EpsilonNeck.axialDepth, if_pos hx, if_pos hcR.1, hcR.2, abs_zero, sub_zero]
      ring
    have hd := R.axialDepth_edist_le x R.center
    rw [hdiff, abs_neg, abs_abs, heR] at hd
    exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hprodLower (abs_nonneg _))).trans hd
  have hfrontUpper (x : M) (hx : x ∈ B.carrier) (hhigh : T < (B.coordinate_inverse x).2) :
      g.edist x R.center ≤ ENNReal.ofReal ((25351 : ℝ) / 100000 * B.scale * L) := by
    have hu := B.edist_le_positive_frontier hx hyRcl hyRB
    rw [heB] at hu
    apply hu.trans (ENNReal.ofReal_le_ofReal ?_)
    change B.scale * Real.sqrt (1 + epsilon) *
      (L - (B.coordinate_inverse x).2 + B0) ≤ _
    calc
      _ ≤ B.scale * Real.sqrt (1 + epsilon) * (L / 4 + B0) :=
        mul_le_mul_of_nonneg_left (by dsimp only [T] at hhigh; linarith only [hhigh])
          (mul_nonneg B.scale_pos.le (Real.sqrt_nonneg _))
      _ ≤ B.scale * (101 / 100) * (L / 4 + B0) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqhi B.scale_pos.le)
          (by positivity)
      _ ≤ B.scale * (101 / 100) * (L / 4 + L / 1000) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hB0L) (by positivity)
      _ = _ := by ring
  have hoverlap : B.carrier ∩ R.carrier ⊆
      B.region (-L / 2) L ∩ R.region (-L) (L / 2) := by
    intro x hx
    have hOld : -L / 2 < (B.coordinate_inverse x).2 := by
      have h := hBlower x hx.2
      rw [hFin x hx.1] at h
      linarith only [h, hL]
    have hNew : (R.coordinate_inverse x).2 < L / 2 := by
      by_contra hn
      have hheight := le_of_not_gt hn
      have hxplus : x ∈ Wplus := (hmemPlus x hx.2).mpr (by
        have h := (hfquantL (R.coordinate_inverse x).1).2
        linarith only [h, hheight, hL])
      have hhigh := hplusF x hxplus
      rw [hFin x hx.1] at hhigh
      have hu := hfrontUpper x hx.1 hhigh
      have hgap : L / 2 ≤ |(R.coordinate_inverse x).2| := hheight.trans (le_abs_self _)
      have hd : ENNReal.ofReal ((49005 : ℝ) / 100000 * B.scale * L) ≤
          g.edist x R.center := by
        apply (ENNReal.ofReal_le_ofReal ?_).trans (hnewLower x hx.2)
        calc
          _ = ((9801 : ℝ) / 10000 * B.scale) * (L / 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hgap (by positivity)
      have hstrict : ENNReal.ofReal ((25351 : ℝ) / 100000 * B.scale * L) <
          ENNReal.ofReal ((49005 : ℝ) / 100000 * B.scale * L) := by
        apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        nlinarith only [mul_pos B.scale_pos hL]
      exact (not_le_of_gt hstrict) (hd.trans hu)
    exact ⟨⟨hx.1, hOld, by simpa only [heB] using
      (B.coordinate_inverse_mem x hx.1).2.2⟩,
      ⟨hx.2, by simpa only [heR] using (R.coordinate_inverse_mem x hx.2).2.1, hNew⟩⟩
  have hcenters {i : ℤ} (hi : i ∈ C.shape.active) : (C.neck i).center ≠ R.center := by
    intro heq
    apply hyR
    apply hNU i hi
    rw [← heq]
    exact (C.neck i).central_sphere_subset (C.neck i).center_on_central_sphere
  let V := Function.update C.neck (b + 1) R
  have hVnew : V (b + 1) = R := Function.update_self _ _ _
  have hVold {i : ℤ} (hi : i ∈ C.shape.active) : V i = C.neck i := by
    have hile := ((hactive i).mp hi).2
    exact Function.update_of_ne (by omega : i ≠ b + 1) R C.neck
  have hold {i : ℤ} (hi : i ∈ Icc a (b + 1)) (hne : i ≠ b + 1) :
      i ∈ C.shape.active := (hactive i).mpr ⟨hi.1, by have h := hi.2; omega⟩
  have holdPair {i : ℤ} (hi : i ∈ Icc a (b + 1)) (hi1 : i + 1 ∈ Icc a (b + 1))
      (hne : i ≠ b) : i ∈ C.shape.active ∧ i + 1 ∈ C.shape.active := by
    rcases hi with ⟨hia, hib⟩
    rcases hi1 with ⟨hi1a, hi1b⟩
    exact ⟨(hactive i).mpr ⟨hia, by omega⟩,
      (hactive (i + 1)).mpr ⟨hi1a, by omega⟩⟩
  let D : BalancedNeckChain g epsilon := {
    shape := .finite a (b + 1)
    neck := V
    source_necks := C.source_necks
    selected := by
      intro i hi
      change i ∈ Icc a (b + 1) at hi
      by_cases hin : i = b + 1
      · subst i
        exact ⟨N', hsource, hVnew ▸ hselected⟩
      · have hio := hold hi hin
        simpa only [hVold hio] using C.selected i hio
    active_nonempty := ⟨a, le_rfl, by omega⟩
    epsilon_eq := by
      intro i hi
      change i ∈ Icc a (b + 1) at hi
      by_cases hin : i = b + 1
      · subst i
        rw [hVnew]
        exact heR
      · rw [hVold (hold hi hin)]
        exact C.epsilon_eq i (hold hi hin)
    centers_distinct := by
      intro i hi j hj hij
      change i ∈ Icc a (b + 1) at hi
      change j ∈ Icc a (b + 1) at hj
      by_cases hin : i = b + 1
      · subst i
        have hjo := hold hj (Ne.symm hij)
        rw [hVnew, hVold hjo]
        exact (hcenters hjo).symm
      · have hio := hold hi hin
        by_cases hjn : j = b + 1
        · subst j
          rw [hVold hio, hVnew]
          exact hcenters hio
        · have hjo := hold hj hjn
          rw [hVold hio, hVold hjo]
          exact C.centers_distinct hio hjo hij
    adjacent_overlap := by
      intro i hi hi1
      change i ∈ Icc a (b + 1) at hi
      change i + 1 ∈ Icc a (b + 1) at hi1
      by_cases hib : i = b
      · subst i
        rw [hVold hb, hVnew]
        exact hinter
      · obtain ⟨hio, hi1o⟩ := holdPair hi hi1 hib
        rw [hVold hio, hVold hi1o]
        exact C.adjacent_overlap i hio hi1o
    overlap_contains_quarters := by
      intro i hi hi1
      change i ∈ Icc a (b + 1) at hi
      change i + 1 ∈ Icc a (b + 1) at hi1
      by_cases hib : i = b
      · subst i
        rw [hVold hb, hVnew]
        exact ⟨hquarter.1, fun _ hx => hclosedNew (subset_closure hx)⟩
      · obtain ⟨hio, hi1o⟩ := holdPair hi hi1 hib
        rw [hVold hio, hVold hi1o]
        exact C.overlap_contains_quarters i hio hi1o
    overlap_within_three_quarters := by
      intro i hi hi1
      change i ∈ Icc a (b + 1) at hi
      change i + 1 ∈ Icc a (b + 1) at hi1
      by_cases hib : i = b
      · subst i
        rw [hVold hb, hVnew]
        exact hoverlap
      · obtain ⟨hio, hi1o⟩ := holdPair hi hi1 hib
        rw [hVold hio, hVold hi1o]
        exact C.overlap_within_three_quarters i hio hi1o
    later_disjoint_negative_end := by
      intro i hi j hj hij
      change i ∈ Icc a (b + 1) at hi
      change j ∈ Icc a (b + 1) at hj
      have hio : i ∈ C.shape.active := by
        apply (hactive i).mpr
        rcases hi with ⟨hia, hib⟩
        rcases hj with ⟨hja, hjb⟩
        exact ⟨hia, by omega⟩
      by_cases hjn : j = b + 1
      · subst j
        refine ⟨-L / 2, ⟨by linarith only [hL], by linarith only [hL]⟩, ?_⟩
        rw [hVnew, hVold hio]
        exact hexclusion i hio
      · have hjo := hold hj hjn
        simpa only [hVold hio, hVold hjo] using
          C.later_disjoint_negative_end i hio j hjo hij
    balanced_center_distance := by
      intro i hi hi1
      change i ∈ Icc a (b + 1) at hi
      change i + 1 ∈ Icc a (b + 1) at hi1
      by_cases hib : i = b
      · subst i
        rw [hVold hb, hVnew]
        exact hquarter.2
      · obtain ⟨hio, hi1o⟩ := holdPair hi hi1 hib
        rw [hVold hio, hVold hi1o]
        exact C.balanced_center_distance i hio hi1o }
  exact Or.inl ⟨R, D, hchoice, hselected, rfl, rfl, rfl, hclosedOld, hclosedNew⟩

end PoincareConjecture
