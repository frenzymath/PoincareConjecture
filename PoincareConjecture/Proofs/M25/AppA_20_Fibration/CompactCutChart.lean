import PoincareConjecture.Proofs.M25.AppA_1_Necks.InitialAngularCorrection
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.IntrinsicSmoothChainChart
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.InitialGraphCut

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.BalancedNeckChain

theorem exists_initial_aligned_compact_cut_chart :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon) {a b : ℤ},
      C.shape = ChainShape.finite a b → epsilon ≤ epsilon0 →
        let L := epsilon⁻¹
        let N := C.neck a
        let B := C.neck b
        let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
        let Sp : Set M := range (fun q : UnitTwoSphere =>
          B.coordinate_map (q, 3 * L / 4))
        let Pplus : Set M := connectedComponentIn (U \ Sp)
          (B.coordinate_map ((B.coordinate_inverse B.center).1, 7 * L / 8))
        ∃ (P : OpenPartialHomeomorph M RoundCylinderSpace)
          (upper beta : UnitTwoSphere → ℝ),
          ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ upper ∧
          ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ beta ∧
          (∀ q, L ≤ upper q ∧ L / 2 < beta q ∧ beta q < upper q) ∧
          P.source = U ∧
          P.target = {z : RoundCylinderSpace | -L < z.2 ∧ z.2 < upper z.1} ∧
          ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ P P.source ∧
          ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ P.symm P.target ∧
          (∀ z ∈ N.cylinderDomain, z.2 ≤ -(3 * L / 4) →
            P (N.coordinate_map z) = z ∧ P.symm z = N.coordinate_map z) ∧
          P '' Sp = range (fun q : UnitTwoSphere => (q, beta q)) ∧
          P '' Pplus = {z : RoundCylinderSpace | beta z.1 < z.2 ∧ z.2 < upper z.1} ∧
          (∀ (h : UnitTwoSphere → ℝ), Continuous h →
            (∀ q, -(9 * L / 10) < h q ∧ h q < -(4 * L / 5)) →
            let Sm : Set M := range (fun q => N.coordinate_map (q, h q))
            let Gminus : Set M := N.coordinate_map ''
              {z : RoundCylinderSpace | -L < z.2 ∧ z.2 < h z.1}
            let K : Set M := U \ (Gminus ∪ Pplus)
            let D : Set RoundCylinderSpace := {z | h z.1 ≤ z.2 ∧ z.2 ≤ beta z.1}
            IsCompact K ∧ frontier K = Sm ∪ Sp ∧
            P '' Sm = range (fun q : UnitTwoSphere => (q, h q)) ∧
            P '' Gminus = {z : RoundCylinderSpace | -L < z.2 ∧ z.2 < h z.1} ∧
            D ⊆ P.target ∧ P '' K = D ∧ P.source ∩ P ⁻¹' D = K ∧ P.symm '' D = K ∧
            P '' interior K = {z : RoundCylinderSpace | h z.1 < z.2 ∧ z.2 < beta z.1}) := by
  obtain ⟨ec, hcp, hcc, chart⟩ := exists_intrinsic_smooth_chain_partial_chart.{u}
  obtain ⟨eh, hhp, _, heights⟩ := exists_finite_relative_saturated_heights.{u}
  obtain ⟨ek, hkp, _, cut⟩ := exists_compact_cut_between_initial_graph_and_last_slice.{u}
  refine ⟨min ec (min eh ek), lt_min hcp (lt_min hhp hkp),
    (min_le_left _ _).trans hcc, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C a b hshape hepsilon
  classical
  let L : ℝ := epsilon⁻¹
  let N := C.neck a
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let d : ℝ := 3 * L / 4
  let c : ℝ := 25 * L / 32
  let q0 : ℤ → UnitTwoSphere := fun i =>
    ((C.neck i).coordinate_inverse (C.neck i).center).1
  let S : ℤ → ℝ → Set M := fun i t =>
    range (fun q : UnitTwoSphere => (C.neck i).coordinate_map (q, t))
  let neg : ℤ → ℝ → Set M := fun i t => connectedComponentIn (U \ S i t)
    ((C.neck i).coordinate_map (q0 i, (t - L) / 2))
  let pos : ℤ → ℝ → Set M := fun i t => connectedComponentIn (U \ S i t)
    ((C.neck i).coordinate_map (q0 i, (t + L) / 2))
  let W : ℤ → Set M := fun i => if i ∈ C.shape.active then
    ((C.neck i).carrier ∩
      (if i - 1 ∈ C.shape.active then pos (i - 1) (23 * L / 32) else univ)) ∩
      (if i + 1 ∈ C.shape.active then neg i c else univ) else ∅
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by rw [hshape]; rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact ((hactive i).mp hi).1.trans ((hactive i).mp hi).2
  have ha : a ∈ C.shape.active := (hactive a).mpr ⟨le_rfl, hab⟩
  have hb : b ∈ C.shape.active := (hactive b).mpr ⟨hab, le_rfl⟩
  have hNe : N.epsilon = epsilon := C.epsilon_eq a ha
  have hL : 0 < L := inv_pos.mpr (hNe ▸ N.epsilon_pos)
  have hd : d ∈ Ioo (-L) L := by dsimp only [d]; constructor <;> linarith
  have hc : c ∈ Ioo (-L) L := by dsimp only [c]; constructor <;> linarith
  have hNU (i : ℤ) (hi : i ∈ C.shape.active) : (C.neck i).carrier ⊆ U :=
    fun _ hx => mem_iUnion₂.mpr ⟨i, hi, hx⟩
  obtain ⟨H, hH⟩ := heights C hshape
    (hepsilon.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨hUopen, _, _, hcuts, horder⟩ :=
    C.intrinsic_ordered_cuts_of_relative_heights hshape H hH
  have hlevelEq (i : ℤ) (hi : i ∈ C.shape.active) (t : ℝ) (ht : t ∈ Ioo (-L) L) :
      U ∩ (H i) ⁻¹' {t} = S i t := (hcuts i hi t ht).1
  have hnegEq (i : ℤ) (hi : i ∈ C.shape.active) (t : ℝ) (ht : t ∈ Ioo (-L) L) :
      neg i t = U ∩ (H i) ⁻¹' Iio t := (hcuts i hi t ht).2.1
  have hposEq (i : ℤ) (hi : i ∈ C.shape.active) (t : ℝ) (ht : t ∈ Ioo (-L) L) :
      pos i t = U ∩ (H i) ⁻¹' Ioi t := (hcuts i hi t ht).2.2.1
  obtain ⟨e, F, B, P0, hFa, _, he, hfirst, hmono, _, hupper,
    hbounds, hP0s, hP0t, hP0smooth, hP0inv, hformula⟩ :=
    chart C hshape (hepsilon.trans (min_le_left _ _)) a ha
  let upper : UnitTwoSphere → ℝ := fun q => (F b ((B b).symm q, L)).2
  let V : Set RoundCylinderSpace := {z | -L < z.2 ∧ z.2 < upper z.1}
  change P0.source = U at hP0s
  have hP0target : P0.target = V := by
    simpa only [hshape, hFa, Diffeomorph.coe_refl, id_eq] using hP0t
  have hu : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ upper := by
    simpa only [hshape] using hupper
  have huL (q : UnitTwoSphere) : L ≤ upper q := by
    simpa only [hshape] using (hbounds q).2
  have hP0cont : ContinuousOn P0 U := hP0s ▸ hP0smooth.continuousOn
  have hedom (i : ℤ) (hi : i ∈ C.shape.active) {q : UnitTwoSphere} {s : ℝ}
      (hs : s ∈ Ioo (-L) L) : (q, s) ∈ (e i).source := by
    rw [(he i hi).1]
    exact ⟨mem_univ _, hs⟩
  have heiheight (i : ℤ) (hi : i ∈ C.shape.active) {x : M}
      (hx : x ∈ (C.neck i).carrier) :
      ((e i).symm x).2 = ((C.neck i).coordinate_inverse x).2 := by
    have hxt : x ∈ (e i).target := (he i hi).2.1.symm ▸ hx
    have h := (he i hi).2.2.2.2.1 _ ((e i).map_target hxt)
    rw [(e i).right_inv hxt] at h
    exact h.symm
  have hslice (i : ℤ) (hi : i ∈ C.shape.active) {t : ℝ} (ht : t ∈ Ioo (-L) L) :
      S i t = range (fun q : UnitTwoSphere => e i (q, t)) := by
    have hdom (q : UnitTwoSphere) : (q, t) ∈ (C.neck i).cylinderDomain := by
      rw [EpsilonNeck.cylinderDomain, C.epsilon_eq i hi]
      exact ⟨mem_univ _, ht⟩
    apply Subset.antisymm
    · rintro _ ⟨q, rfl⟩
      have hx := (C.neck i).coordinate_map_mem (hdom q)
      refine ⟨((e i).symm ((C.neck i).coordinate_map (q, t))).1, ?_⟩
      have hh := heiheight i hi hx
      rw [(C.neck i).coordinate_inverse_coordinate_map (hdom q)] at hh
      change ((e i).symm ((C.neck i).coordinate_map (q, t))).2 = t at hh
      change e i (((e i).symm ((C.neck i).coordinate_map (q, t))).1, t) = _
      have hp : (((e i).symm ((C.neck i).coordinate_map (q, t))).1, t) =
          (e i).symm ((C.neck i).coordinate_map (q, t)) := Prod.ext rfl hh.symm
      exact (congrArg (e i) hp).trans
        ((e i).right_inv ((he i hi).2.1.symm ▸ hx))
    · rintro _ ⟨q, rfl⟩
      have hx : e i (q, t) ∈ (C.neck i).carrier :=
        (he i hi).2.1 ▸ (e i).map_source (hedom i hi ht)
      refine ⟨((C.neck i).coordinate_inverse (e i (q, t))).1, ?_⟩
      have hh := (he i hi).2.2.2.2.1 (q, t) (hedom i hi ht)
      change ((C.neck i).coordinate_inverse (e i (q, t))).2 = t at hh
      change (C.neck i).coordinate_map
        (((C.neck i).coordinate_inverse (e i (q, t))).1, t) = _
      have hp : (((C.neck i).coordinate_inverse (e i (q, t))).1, t) =
          (C.neck i).coordinate_inverse (e i (q, t)) := Prod.ext rfl hh.symm
      exact (congrArg (C.neck i).coordinate_map hp).trans
        ((C.neck i).coordinate_map_coordinate_inverse hx)
  have hWa {x : M} (hx : x ∈ N.carrier)
      (ht : (N.coordinate_inverse x).2 < c) : x ∈ W a := by
    have hp : a - 1 ∉ C.shape.active := by
      intro hi
      have h := ((hactive (a - 1)).mp hi).1
      omega
    dsimp only [W]
    rw [if_pos ha, if_neg hp]
    refine ⟨⟨hx, mem_univ _⟩, ?_⟩
    split_ifs with hn
    · rw [hnegEq a ha c hc]
      refine ⟨hNU a ha hx, ?_⟩
      change H a x < c
      rw [(hH a ha).2.1 x hx]
      exact ht
    · exact mem_univ _
  have hPinitial {x : M} (hx : x ∈ N.carrier)
      (ht : (N.coordinate_inverse x).2 < c) : P0 x = (e a).symm x := by
    have h := (hformula a).1 (hWa hx ht)
    simpa only [hFa, Diffeomorph.coe_refl, id_eq] using h
  have hinitial (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-L) c) :
      P0 (e a (q, s)) = (q, s) := by
    have hsc : s ∈ Ioo (-L) L := ⟨hs.1, hs.2.trans hc.2⟩
    have hx : e a (q, s) ∈ N.carrier :=
      (he a ha).2.1 ▸ (e a).map_source (hedom a ha hsc)
    rw [hPinitial hx (by rw [(he a ha).2.2.2.2.1 _ (hedom a ha hsc)]; exact hs.2),
      (e a).left_inv (hedom a ha hsc)]
  have hWsub (i : ℤ) (hi : i ∈ C.shape.active) : W i ⊆ U := by
    intro x hx
    dsimp only [W] at hx
    rw [if_pos hi] at hx
    exact hNU i hi hx.1.1
  have hWopen (i : ℤ) (hi : i ∈ C.shape.active) : IsOpen (W i) := by
    dsimp only [W]
    rw [if_pos hi]
    apply IsOpen.inter
    · apply (C.neck i).carrier_open.inter
      split_ifs with hp
      · exact (hcuts (i - 1) hp (23 * L / 32)
          (by constructor <;> linarith)).2.2.2.2.1
      · exact isOpen_univ
    · split_ifs with hn
      · exact (hcuts i hi c hc).2.2.2.1
      · exact isOpen_univ
  let beta : UnitTwoSphere → ℝ := fun q => (F b ((B b).symm q, d)).2
  have hbeta : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ beta :=
    ((F b).contMDiff.comp ((B b).symm.contMDiff.prodMk contMDiff_const)).snd
  have hbetau (q : UnitTwoSphere) : beta q < upper q := hmono b _ hd.2
  have hPformula (i : ℤ) {z : RoundCylinderSpace} (hz : z ∈ (e i).source)
      (hw : e i z ∈ W i) : P0 (e i z) = F i z :=
    ((hformula i).1 hw).trans (congrArg (F i) ((e i).left_inv hz))
  have hSpimage : P0 '' S b d = range (fun q : UnitTwoSphere => (q, beta q)) := by
    rw [hslice b hb hd]
    ext z
    constructor
    · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
      refine ⟨B b q, ?_⟩
      change (B b q, beta (B b q)) = P0 (e b (q, d))
      rw [hPformula b (hedom b hb hd) ((he b hb).2.2.2.2.2.2 q)]
      apply Prod.ext
      · exact (hfirst b (q, d)).1.symm
      · simp only [beta, (B b).symm_apply_apply]
    · rintro ⟨q, rfl⟩
      refine ⟨e b ((B b).symm q, d), ⟨(B b).symm q, rfl⟩, ?_⟩
      change P0 (e b ((B b).symm q, d)) = (q, beta q)
      rw [hPformula b (hedom b hb hd) ((he b hb).2.2.2.2.2.2 _)]
      exact Prod.ext ((hfirst b _).1.trans ((B b).apply_symm_apply q)) rfl

  have hclassify (i : ℤ) (hi : i ∈ C.shape.active) (t : ℝ) (ht : t ∈ Ioo (-L) L)
      (f : UnitTwoSphere → ℝ) (hf : Continuous f)
      (hgraph : P0 '' S i t = range (fun q : UnitTwoSphere => (q, f q)))
      (hm : ∃ x ∈ U, H i x < t ∧ (P0 x).2 < f (P0 x).1)
      (hp : ∃ x ∈ U, t < H i x ∧ f (P0 x).1 < (P0 x).2) :
      ∀ x ∈ U, (H i x < t ↔ (P0 x).2 < f (P0 x).1) ∧
        (t < H i x ↔ f (P0 x).1 < (P0 x).2) := by
    obtain ⟨_, _, _, _, _, hcn, hcpSide, _⟩ := hcuts i hi t ht
    have hlevel := hlevelEq i hi t ht
    have hn := hnegEq i hi t ht
    have hpSide := hposEq i hi t ht
    change IsConnected (neg i t) at hcn
    change IsConnected (pos i t) at hcpSide
    have hzero {x : M} (hx : x ∈ U) : H i x = t ↔ (P0 x).2 = f (P0 x).1 := by
      constructor
      · intro hxt
        have hxS : x ∈ S i t := hlevel ▸ ⟨hx, hxt⟩
        obtain ⟨q, hq⟩ := hgraph ▸ (mem_image_of_mem P0 hxS)
        rw [← hq]
      · intro hxt
        have hxg : P0 x ∈ range (fun q : UnitTwoSphere => (q, f q)) :=
          ⟨(P0 x).1, Prod.ext rfl hxt.symm⟩
        obtain ⟨y, hy, hyx⟩ := hgraph.symm ▸ hxg
        have hyU : y ∈ U := (hlevel.symm ▸ hy).1
        have hyEq : y = x := P0.injOn (hP0s.symm ▸ hyU) (hP0s.symm ▸ hx) hyx
        exact hyEq ▸ (hlevel.symm ▸ hy).2
    let G : M → ℝ := fun x => (P0 x).2 - f (P0 x).1
    have hGc : ContinuousOn G U := hP0cont.snd.sub (hf.comp_continuousOn hP0cont.fst)
    have hnU : neg i t ⊆ U := hn ▸ inter_subset_left
    have hpU : pos i t ⊆ U := hpSide ▸ inter_subset_left
    have hgn : ∀ x ∈ neg i t, G x < 0 := by
      apply hcn.isPreconnected.gt_of_ne (hGc.mono hnU)
      · intro x hx hg
        have heq := (hzero (hnU hx)).mpr (sub_eq_zero.mp hg)
        exact (ne_of_lt (hn ▸ hx).2) heq
      · obtain ⟨x, hx, hxt, hxf⟩ := hm
        exact ⟨x, hn.symm ▸ ⟨hx, hxt⟩, sub_neg.mpr hxf⟩
    have hgp : ∀ x ∈ pos i t, 0 < G x := by
      apply hcpSide.isPreconnected.lt_of_ne (hGc.mono hpU)
      · intro x hx hg
        have heq := (hzero (hpU hx)).mpr (sub_eq_zero.mp hg)
        exact (ne_of_gt (hpSide ▸ hx).2) heq
      · obtain ⟨x, hx, hxt, hxf⟩ := hp
        exact ⟨x, hpSide.symm ▸ ⟨hx, hxt⟩, sub_pos.mpr hxf⟩
    intro x hx
    rcases lt_trichotomy (H i x) t with hm' | heq | hp'
    · have hs := sub_neg.mp (hgn x (hn.symm ▸ ⟨hx, hm'⟩))
      exact ⟨iff_of_true hm' hs, iff_of_false (not_lt_of_ge hm'.le) (not_lt_of_ge hs.le)⟩
    · have hs := (hzero hx).mp heq
      simp only [heq, hs, lt_self_iff_false, iff_self, and_self]
    · have hs := sub_pos.mp (hgp x (hpSide.symm ▸ ⟨hx, hp'⟩))
      exact ⟨iff_of_false (not_lt_of_ge hp'.le) (not_lt_of_ge hs.le), iff_of_true hp' hs⟩
  have hlastanchors :
      (∃ x ∈ U, H b x < d ∧ (P0 x).2 < beta (P0 x).1) ∧
      (∃ x ∈ U, d < H b x ∧ beta (P0 x).1 < (P0 x).2) := by
    let q := q0 b
    have hline : ContinuousAt (fun s : ℝ => e b (q, s)) d :=
      ((he b hb).2.2.1.continuousOn.continuousAt
        ((e b).open_source.mem_nhds (hedom b hb hd))).comp
          (continuous_const.prodMk continuous_id).continuousAt
    have hnear : {s : ℝ | e b (q, s) ∈ W b} ∈ nhds d :=
      hline.preimage_mem_nhds ((hWopen b hb).mem_nhds ((he b hb).2.2.2.2.2.2 q))
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
    let v := min r (L / 8) / 2
    have hv : 0 < v := by dsimp only [v]; positivity
    have hvr : v < r := by dsimp only [v]; linarith [min_le_left r (L / 8)]
    have hvL : v < L / 8 := by dsimp only [v]; linarith [min_le_right r (L / 8)]
    have hret (s : ℝ) (hs : s = d - v ∨ s = d + v) :
        s ∈ Ioo (-L) L ∧ e b (q, s) ∈ W b := by
      rcases hs with rfl | rfl
      · refine ⟨by dsimp only [d]; constructor <;> linarith, hball ?_⟩
        rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
        linarith
      · refine ⟨by dsimp only [d]; constructor <;> linarith, hball ?_⟩
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
        linarith
    have hval (s : ℝ) (hs : s = d - v ∨ s = d + v) :
        H b (e b (q, s)) = s ∧ P0 (e b (q, s)) = F b (q, s) := by
      have h := hret s hs
      have hx : e b (q, s) ∈ (C.neck b).carrier :=
        (he b hb).2.1 ▸ (e b).map_source (hedom b hb h.1)
      refine ⟨((hH b hb).2.1 _ hx).trans ((he b hb).2.2.2.2.1 _ (hedom b hb h.1)), ?_⟩
      exact hPformula b (hedom b hb h.1) h.2
    constructor
    · refine ⟨e b (q, d - v), hWsub b hb (hret _ (Or.inl rfl)).2, ?_, ?_⟩
      · rw [(hval _ (Or.inl rfl)).1]; linarith
      · rw [(hval _ (Or.inl rfl)).2, (hfirst b _).1]
        simpa only [beta, (B b).symm_apply_apply] using hmono b q (show d - v < d by linarith)
    · refine ⟨e b (q, d + v), hWsub b hb (hret _ (Or.inr rfl)).2, ?_, ?_⟩
      · rw [(hval _ (Or.inr rfl)).1]; linarith
      · rw [(hval _ (Or.inr rfl)).2, (hfirst b _).1]
        simpa only [beta, (B b).symm_apply_apply] using hmono b q (show d < d + v by linarith)
  have hlast := hclassify b hb d hd beta hbeta.continuous hSpimage
    hlastanchors.1 hlastanchors.2
  let tau : ℝ := 3 * L / 5
  have htau : tau ∈ Ioo (-L) c := by dsimp only [tau, c]; constructor <;> linarith
  have hTauImage : P0 '' S a tau = range (fun q : UnitTwoSphere => (q, tau)) := by
    rw [hslice a ha ⟨htau.1, htau.2.trans hc.2⟩]
    ext z
    constructor
    · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
      exact ⟨q, (hinitial q htau).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨e a (q, tau), ⟨q, rfl⟩, hinitial q htau⟩
  have hinitanchors :
      (∃ x ∈ U, H a x < tau ∧ (P0 x).2 < tau) ∧
      (∃ x ∈ U, tau < H a x ∧ tau < (P0 x).2) := by
    have hval (s : ℝ) (hs : s ∈ Ioo (-L) c) :
        e a (q0 a, s) ∈ U ∧ H a (e a (q0 a, s)) = s := by
      have hx : e a (q0 a, s) ∈ N.carrier :=
        (he a ha).2.1 ▸ (e a).map_source (hedom a ha ⟨hs.1, hs.2.trans hc.2⟩)
      exact ⟨hNU a ha hx, ((hH a ha).2.1 _ hx).trans
        ((he a ha).2.2.2.2.1 _ (hedom a ha ⟨hs.1, hs.2.trans hc.2⟩))⟩
    have hz : (0 : ℝ) ∈ Ioo (-L) c := by dsimp only [c]; constructor <;> linarith
    have hv : (tau + c) / 2 ∈ Ioo (-L) c := by constructor <;> linarith [htau.1, htau.2]
    constructor
    · refine ⟨e a (q0 a, 0), (hval 0 hz).1, ?_, ?_⟩
      · rw [(hval 0 hz).2]; dsimp only [tau]; positivity
      · rw [hinitial _ hz]; dsimp only [tau]; positivity
    · refine ⟨e a (q0 a, (tau + c) / 2), (hval _ hv).1, ?_, ?_⟩
      · rw [(hval _ hv).2]; linarith [htau.2]
      · rw [hinitial _ hv]; dsimp only; linarith [htau.2]
  have hinitside := hclassify a ha tau ⟨htau.1, htau.2.trans hc.2⟩
    (fun _ => tau) continuous_const hTauImage hinitanchors.1 hinitanchors.2
  have hbetalow (q : UnitTwoSphere) : L / 2 < beta q := by
    rcases eq_or_lt_of_le hab with heq | hlt
    · have hf : F b = Diffeomorph.refl ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace ∞ :=
        heq ▸ hFa
      simp only [beta, hf, Diffeomorph.coe_refl, id_eq]
      dsimp only [d]
      linarith
    · obtain ⟨x, hxS, hpx⟩ := hSpimage.symm ▸
        (show (q, beta q) ∈ range (fun r : UnitTwoSphere => (r, beta r)) from ⟨q, rfl⟩)
      obtain ⟨hlevel, _, _, _, _, _, _, _, _, hclosed, _⟩ := hcuts b hb d hd
      have hxH : x ∈ U ∩ (H b) ⁻¹' {d} := hlevel.symm ▸ hxS
      have hxcl : x ∈ U ∩ closure (pos b d) := hclosed.symm ▸ ⟨hxH.1, hxH.2.ge⟩
      have hxpos := (horder a ha b hb hlt tau
        (by dsimp only [tau]; constructor <;> linarith) d
        (by dsimp only [d]; constructor <;> linarith)).2 hxcl
      have hxt : tau < H a x := ((hcuts a ha tau ⟨htau.1, htau.2.trans hc.2⟩).2.2.1 ▸ hxpos).2
      have ht := ((hinitside x hxH.1).2.mp hxt)
      rw [hpx] at ht
      dsimp only [tau] at ht
      linarith
  let Sp := S b d
  let Pplus : Set M := connectedComponentIn (U \ Sp)
    ((C.neck b).coordinate_map (q0 b, 7 * L / 8))
  have hPplus : Pplus = pos b d := by
    have ht : (d + L) / 2 = 7 * L / 8 := by dsimp only [d]; ring
    dsimp only [Pplus, pos, Sp]
    rw [ht]
  have hplusimage : P0 '' Pplus = {z : RoundCylinderSpace |
      beta z.1 < z.2 ∧ z.2 < upper z.1} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxH : x ∈ U ∩ (H b) ⁻¹' Ioi d := hposEq b hb d hd ▸ (hPplus ▸ hx)
      exact ⟨(hlast x hxH.1).2.mp hxH.2,
        (hP0target ▸ P0.map_source (hP0s.symm ▸ hxH.1)).2⟩
    · intro hz
      change beta z.1 < z.2 ∧ z.2 < upper z.1 at hz
      have hzV : z ∈ P0.target := hP0target.symm ▸
        ⟨by linarith [hbetalow z.1, hz.1], hz.2⟩
      have hxU : P0.symm z ∈ U := hP0s ▸ P0.map_target hzV
      refine ⟨P0.symm z, ?_, P0.right_inv hzV⟩
      rw [hPplus, hposEq b hb d hd]
      refine ⟨hxU, (hlast _ hxU).2.mpr ?_⟩
      rw [P0.right_inv hzV]
      exact hz.1
  obtain ⟨A, hAs, hAt, hAsmooth, hAinv, _, _, hAlow, hAhigh, hApreserve⟩ :=
    N.exists_relative_initial_angular_correction (e a)
      (by rw [(he a ha).1, EpsilonNeck.cylinderDomain, hNe])
      (he a ha).2.1 (he a ha).2.2.1 (he a ha).2.2.2.1
      (he a ha).2.2.2.2.1 (he a ha).2.2.2.2.2.1
  simp only [hNe] at hAs hAt hAsmooth hAinv hAlow hAhigh hApreserve
  let P := P0.trans A
  have hVhalf : V ⊆ univ ×ˢ Ioi (-L) := fun _ hz => ⟨mem_univ _, hz.1⟩
  have hPs : P.source = U := by
    change P0.source ∩ P0 ⁻¹' A.source = U
    apply Subset.antisymm
    · exact fun _ hx => hP0s ▸ hx.1
    · intro x hx
      exact ⟨hP0s.symm ▸ hx, hAs.symm ▸ hVhalf
        (hP0target ▸ P0.map_source (hP0s.symm ▸ hx))⟩
  have hPt : P.target = V := by
    change A.target ∩ A.symm ⁻¹' P0.target = V
    rw [hAt, hP0target]
    exact (hApreserve upper huL).2.2.2
  have hPsmooth : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ P P.source :=
    hAsmooth.comp (hP0smooth.mono inter_subset_left) (fun x hx => hAs ▸ hx.2)
  have hPinv : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ P.symm P.target :=
    hP0inv.comp (hAinv.mono (fun x hx => hAt ▸ hx.1)) (fun _ hx => hx.2)
  have hlow (z : RoundCylinderSpace) (hz : z ∈ N.cylinderDomain)
      (hs : z.2 ≤ -(3 * L / 4)) :
      P (N.coordinate_map z) = z ∧ P.symm z = N.coordinate_map z := by
    have hzL : z.2 ∈ Ioo (-L) L := by simpa only [hNe] using hz.2
    have hx := N.coordinate_map_mem hz
    have ht : (N.coordinate_inverse (N.coordinate_map z)).2 < c := by
      rw [N.coordinate_inverse_coordinate_map hz]
      dsimp only [c]
      linarith
    have hw : (e a).symm (N.coordinate_map z) ∈ N.cylinderDomain := by
      rw [EpsilonNeck.cylinderDomain, hNe, ← (he a ha).1]
      exact (e a).map_target ((he a ha).2.1.symm ▸ hx)
    have hws : ((e a).symm (N.coordinate_map z)).2 ≤ -(3 * L / 4) := by
      rw [heiheight a ha hx, N.coordinate_inverse_coordinate_map hz]
      exact hs
    have hforward : P (N.coordinate_map z) = z := by
      change A (P0 (N.coordinate_map z)) = z
      rw [hPinitial hx ht, (hAlow _ hw hws).1,
        (e a).right_inv ((he a ha).2.1.symm ▸ hx), N.coordinate_inverse_coordinate_map hz]
    refine ⟨hforward, ?_⟩
    calc
      P.symm z = P.symm (P (N.coordinate_map z)) := congrArg P.symm hforward.symm
      _ = N.coordinate_map z := P.left_inv (hPs.symm ▸ hNU a ha hx)
  have hAupper {z : RoundCylinderSpace} (hz : beta z.1 ≤ z.2)
      (hzV : z ∈ V) : A z = z :=
    (hAhigh z (hVhalf hzV) (by linarith [hbetalow z.1])).1
  have hSpimageP : P '' Sp = range (fun q : UnitTwoSphere => (q, beta q)) := by
    change (A ∘ P0) '' Sp = _
    rw [image_comp, hSpimage]
    ext z
    constructor
    · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
      have heq := hAupper (z := (q, beta q)) le_rfl
        ⟨by linarith [hbetalow q], hbetau q⟩
      exact ⟨q, heq.symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨(q, beta q), ⟨q, rfl⟩,
        hAupper le_rfl ⟨by linarith [hbetalow q], hbetau q⟩⟩
  have hplusimageP : P '' Pplus = {z : RoundCylinderSpace |
      beta z.1 < z.2 ∧ z.2 < upper z.1} := by
    change (A ∘ P0) '' Pplus = _
    rw [image_comp, hplusimage]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rwa [hAupper hw.1.le ⟨by linarith [hbetalow w.1, hw.1], hw.2⟩]
    · intro hz
      exact ⟨z, hz, hAupper hz.1.le ⟨by linarith [hbetalow z.1, hz.1], hz.2⟩⟩
  refine ⟨P, upper, beta, hu, hbeta, fun q => ⟨huL q, hbetalow q, hbetau q⟩,
    hPs, hPt, hPsmooth, hPinv, hlow, hSpimageP, hplusimageP, ?_⟩
  intro h hh hbound
  let Sm : Set M := range (fun q => N.coordinate_map (q, h q))
  let Dm : Set RoundCylinderSpace := {z | -L < z.2 ∧ z.2 < h z.1}
  let Gm : Set M := N.coordinate_map '' Dm
  let K : Set M := U \ (Gm ∪ Pplus)
  let D : Set RoundCylinderSpace := {z | h z.1 ≤ z.2 ∧ z.2 ≤ beta z.1}
  obtain ⟨_, _, _, _, _, _, hKcompact, _, _, hKint, hKfront, _⟩ :=
    cut C hshape (hepsilon.trans ((min_le_right _ _).trans (min_le_right _ _))) h hh hbound
  have hdom {z : RoundCylinderSpace} (hlo : -L < z.2) (hhi : z.2 ≤ h z.1) :
      z ∈ N.cylinderDomain ∧ z.2 ≤ -(3 * L / 4) := by
    refine ⟨?_, by linarith [(hbound z.1).2]⟩
    rw [EpsilonNeck.cylinderDomain, hNe]
    exact ⟨mem_univ _, hlo, by linarith [(hbound z.1).2]⟩
  have hSmimage : P '' Sm = range (fun q : UnitTwoSphere => (q, h q)) := by
    ext z
    constructor
    · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
      have hdq := hdom (z := (q, h q)) (by linarith [(hbound q).1]) le_rfl
      exact ⟨q, (hlow _ hdq.1 hdq.2).1.symm⟩
    · rintro ⟨q, rfl⟩
      have hdq := hdom (z := (q, h q)) (by linarith [(hbound q).1]) le_rfl
      exact ⟨N.coordinate_map (q, h q), ⟨q, rfl⟩, (hlow _ hdq.1 hdq.2).1⟩
  have hGimage : P '' Gm = Dm := by
    ext z
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      have hdw := hdom hw.1 hw.2.le
      rwa [(hlow _ hdw.1 hdw.2).1]
    · intro hz
      have hdz := hdom hz.1 hz.2.le
      exact ⟨N.coordinate_map z, ⟨z, hz, rfl⟩, (hlow _ hdz.1 hdz.2).1⟩
  have hDU : D ⊆ P.target := by
    intro z hz
    rw [hPt]
    exact ⟨by linarith [hz.1, (hbound z.1).1], hz.2.trans_lt (hbetau z.1)⟩
  have hGsub : Gm ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact hNU a ha (N.coordinate_map_mem (hdom hz.1 hz.2.le).1)
  have hPsub : Pplus ⊆ U := by
    rw [hPplus, hposEq b hb d hd]
    exact inter_subset_left
  have hSmSub : Sm ⊆ U := by
    rintro _ ⟨q, rfl⟩
    exact hNU a ha (N.coordinate_map_mem
      (hdom (z := (q, h q)) (by linarith [(hbound q).1]) le_rfl).1)
  have hSpSub : Sp ⊆ U := by
    intro x hx
    change x ∈ S b d at hx
    exact ((hlevelEq b hb d hd).symm ▸ hx).1
  have hmemImage (T : Set M) (hT : T ⊆ U) {x : M} (hx : x ∈ U) :
      P x ∈ P '' T ↔ x ∈ T := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact (P.injOn (hPs.symm ▸ hT hy) (hPs.symm ▸ hx) hyx) ▸ hy
    · exact mem_image_of_mem P
  have hKiff {x : M} (hx : x ∈ U) : x ∈ K ↔ P x ∈ D := by
    have hg := hmemImage Gm hGsub hx
    have hp := hmemImage Pplus hPsub hx
    rw [hGimage] at hg
    rw [hplusimageP] at hp
    have hv : P x ∈ V := hPt ▸ P.map_source (hPs.symm ▸ hx)
    change (x ∈ U ∧ ¬ (x ∈ Gm ∨ x ∈ Pplus)) ↔ _
    rw [← hg, ← hp]
    change (x ∈ U ∧ ¬ ((-L < (P x).2 ∧ (P x).2 < h (P x).1) ∨
      (beta (P x).1 < (P x).2 ∧ (P x).2 < upper (P x).1))) ↔
        (h (P x).1 ≤ (P x).2 ∧ (P x).2 ≤ beta (P x).1)
    constructor
    · rintro ⟨_, hn⟩
      exact ⟨le_of_not_gt (fun hlt => hn (Or.inl ⟨hv.1, hlt⟩)),
        le_of_not_gt (fun hlt => hn (Or.inr ⟨hlt, hv.2⟩))⟩
    · rintro ⟨hl, hu'⟩
      exact ⟨hx, fun hbad => hbad.elim (fun hm => (not_lt_of_ge hl) hm.2)
        (fun hp' => (not_lt_of_ge hu') hp'.1)⟩
  have hKimage : P '' K = D := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hKiff hx.1).mp hx
    · intro hz
      have hxU : P.symm z ∈ U := hPs ▸ P.map_target (hDU hz)
      exact ⟨P.symm z, (hKiff hxU).mpr (by rwa [P.right_inv (hDU hz)]),
        P.right_inv (hDU hz)⟩
  have hpreimage : P.source ∩ P ⁻¹' D = K := by
    ext x
    rw [hPs]
    exact ⟨fun hx => (hKiff hx.1).mpr hx.2, fun hx => ⟨hx.1, (hKiff hx.1).mp hx⟩⟩
  have hinvimage : P.symm '' D = K := by
    rw [← hKimage]
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rwa [P.left_inv (hPs.symm ▸ hy.1)]
    · intro hx
      exact ⟨P x, ⟨x, hx, rfl⟩, P.left_inv (hPs.symm ▸ hx.1)⟩
  refine ⟨hKcompact, hKfront, hSmimage, hGimage, hDU, hKimage, hpreimage, hinvimage, ?_⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ K \ (Sm ∪ Sp) := hKint ▸ hx
    have hD := (hKiff hx'.1.1).mp hx'.1
    have hm : (P x).2 ≠ h (P x).1 := by
      intro heq
      apply hx'.2
      left
      apply (hmemImage Sm hSmSub hx'.1.1).mp
      rw [hSmimage]
      exact ⟨(P x).1, Prod.ext rfl heq.symm⟩
    have hp : (P x).2 ≠ beta (P x).1 := by
      intro heq
      apply hx'.2
      right
      apply (hmemImage Sp hSpSub hx'.1.1).mp
      rw [hSpimageP]
      exact ⟨(P x).1, Prod.ext rfl heq.symm⟩
    exact ⟨lt_of_le_of_ne hD.1 (Ne.symm hm), lt_of_le_of_ne hD.2 hp⟩
  · intro hz
    have hzD : z ∈ D := ⟨hz.1.le, hz.2.le⟩
    obtain ⟨x, hx, hpx⟩ := hKimage.symm ▸ hzD
    refine ⟨x, ?_, hpx⟩
    rw [hKint]
    refine ⟨hx, ?_⟩
    intro hbad
    rcases hbad with hm | hp
    · obtain ⟨q, hq⟩ := hSmimage ▸ mem_image_of_mem P hm
      rw [hpx] at hq
      rw [← hq] at hz
      exact (lt_irrefl _ hz.1)
    · obtain ⟨q, hq⟩ := hSpimageP ▸ mem_image_of_mem P hp
      rw [hpx] at hq
      rw [← hq] at hz
      exact (lt_irrefl _ hz.2)

end PoincareConjecture.BalancedNeckChain
