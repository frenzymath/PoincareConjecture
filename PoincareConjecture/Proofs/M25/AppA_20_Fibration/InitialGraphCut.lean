import PoincareConjecture.Proofs.M25.AppA_20_Fibration.IntrinsicCuts
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.RetainedFiniteChainCore

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem BalancedNeckChain.exists_compact_cut_between_initial_graph_and_last_slice :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon) {a b : ℤ},
      C.shape = ChainShape.finite a b → epsilon ≤ epsilon0 →
      let L := epsilon⁻¹
      let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
      let N := C.neck a
      let B := C.neck b
      ∀ (h : UnitTwoSphere → ℝ), Continuous h →
        (∀ q, -(9 * L / 10) < h q ∧ h q < -(4 * L / 5)) →
        let Sminus : Set M := Set.range (fun q => N.coordinate_map (q, h q))
        let Splus : Set M := Set.range (fun q => B.coordinate_map (q, 3 * L / 4))
        let Gminus : Set M := N.coordinate_map ''
          {z : RoundCylinderSpace | -L < z.2 ∧ z.2 < h z.1}
        let Pplus : Set M := connectedComponentIn (U \ Splus)
          (B.coordinate_map ((B.coordinate_inverse B.center).1, 7 * L / 8))
        let K : Set M := U \ (Gminus ∪ Pplus)
        IsOpen U ∧ IsOpen Gminus ∧ IsOpen Pplus ∧
        U ∩ closure Gminus = Gminus ∪ Sminus ∧
        U ∩ closure Pplus = Pplus ∪ Splus ∧
        Disjoint (U ∩ closure Gminus) (U ∩ closure Pplus) ∧
        IsCompact K ∧ K ⊆ U ∧
        closure (interior K) = K ∧
        interior K = K \ (Sminus ∪ Splus) ∧
        frontier K = Sminus ∪ Splus ∧ Disjoint Sminus Splus ∧
        K ∩ N.region (-L) (-L / 2) = N.coordinate_map ''
          {z : RoundCylinderSpace | -L < z.2 ∧ h z.1 ≤ z.2 ∧ z.2 < -L / 2} ∧
        interior K ∩ N.region (-L) (-L / 2) = N.coordinate_map ''
          {z : RoundCylinderSpace | -L < z.2 ∧ h z.1 < z.2 ∧ z.2 < -L / 2} ∧
        K ∩ B.region (5 * L / 8) L = B.coordinate_map ''
          (Set.univ ×ˢ Set.Ioc (5 * L / 8) (3 * L / 4)) ∧
        interior K ∩ B.region (5 * L / 8) L =
          B.region (5 * L / 8) (3 * L / 4) := by
  obtain ⟨epsilonH, hHpos, hHcap, hheights⟩ :=
    BalancedNeckChain.exists_finite_relative_saturated_heights.{u}
  obtain ⟨epsilonK, hKpos, _, hcore⟩ :=
    BalancedNeckChain.exists_finite_retained_core_cover.{u}
  refine ⟨min epsilonH epsilonK, lt_min hHpos hKpos,
    (min_le_left _ _).trans hHcap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C a b hshape heps
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L := epsilon⁻¹
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let N := C.neck a
  let B := C.neck b
  change ∀ (h : UnitTwoSphere → ℝ), Continuous h →
    (∀ q, -(9 * L / 10) < h q ∧ h q < -(4 * L / 5)) → _
  intro h hh hbound
  let T := 3 * L / 4
  let tau := 3 * L / 5
  let nu := 5 * L / 8
  let Sm : Set M := range (fun q => N.coordinate_map (q, h q))
  let Sp : Set M := range (fun q : UnitTwoSphere => B.coordinate_map (q, T))
  let Dm : Set RoundCylinderSpace := {z | -L < z.2 ∧ z.2 < h z.1}
  let G : Set M := N.coordinate_map '' Dm
  let P : Set M := connectedComponentIn (U \ Sp)
    (B.coordinate_map ((B.coordinate_inverse B.center).1, 7 * L / 8))
  let K : Set M := U \ (G ∪ P)
  change IsOpen U ∧ IsOpen G ∧ IsOpen P ∧ _
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by
    rw [hshape]
    rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact ((hactive i).mp hi).1.trans ((hactive i).mp hi).2
  have ha : a ∈ C.shape.active := (hactive a).mpr ⟨le_rfl, hab⟩
  have hb : b ∈ C.shape.active := (hactive b).mpr ⟨hab, le_rfl⟩
  have hNe : N.epsilon = epsilon := C.epsilon_eq a ha
  have hBe : B.epsilon = epsilon := C.epsilon_eq b hb
  have hepos : 0 < epsilon := hNe ▸ N.epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepos
  have hNU (i : ℤ) (hi : i ∈ C.shape.active) : (C.neck i).carrier ⊆ U :=
    fun _ hx => mem_iUnion₂.mpr ⟨i, hi, hx⟩
  have hNheight (x : M) (hx : x ∈ N.carrier) :
      (N.coordinate_inverse x).2 ∈ Ioo (-L) L := by
    simpa only [hNe] using (N.coordinate_inverse_mem x hx).2
  have hdom (D : EpsilonNeck g) (he : D.epsilon = epsilon)
      {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-L) L) :
      z ∈ D.cylinderDomain := by
    rw [EpsilonNeck.cylinderDomain, he]
    exact ⟨mem_univ _, hz⟩
  have hline (D : EpsilonNeck g) (he : D.epsilon = epsilon)
      (q : UnitTwoSphere) {t : ℝ} (ht : t ∈ Ioo (-L) L) :
      ContinuousAt (fun s : ℝ => D.coordinate_map (q, s)) t := by
    have hc : ContinuousAt D.coordinate_map (q, t) :=
      D.coordinate_map_smooth.continuousOn.continuousAt
        (D.cylinderDomain_open.mem_nhds (hdom D he (z := (q, t)) ht))
    exact hc.comp (continuous_const.prodMk continuous_id).continuousAt
  have hhdom (q : UnitTwoSphere) : h q ∈ Ioo (-L) L := by
    constructor <;> linarith only [hL, (hbound q).1, (hbound q).2]
  have htau : tau ∈ Ioo (L / 2) L := by
    dsimp only [tau]
    constructor <;> linarith only [hL]
  have hnu : nu ∈ Ioo (L / 2) L := by
    dsimp only [nu]
    constructor <;> linarith only [hL]
  have hT : T ∈ Ioo (L / 2) L := by
    dsimp only [T]
    constructor <;> linarith only [hL]
  have hret {t : ℝ} (ht : t ∈ Ioo (L / 2) L) : t ∈ Ioo (-L) L :=
    ⟨by linarith only [hL, ht.1], ht.2⟩
  obtain ⟨F, hF⟩ := hheights C hshape (heps.trans (min_le_left _ _))
  obtain ⟨hUopen, _, _, hcuts, horder⟩ :=
    C.intrinsic_ordered_cuts_of_relative_heights hshape F hF
  let q : ℤ → UnitTwoSphere := fun i =>
    ((C.neck i).coordinate_inverse (C.neck i).center).1
  let S : ℤ → ℝ → Set M := fun i t =>
    range (fun v : UnitTwoSphere => (C.neck i).coordinate_map (v, t))
  let Am : ℤ → ℝ → Set M := fun i t =>
    connectedComponentIn (U \ S i t) ((C.neck i).coordinate_map (q i, (t - L) / 2))
  let Bp : ℤ → ℝ → Set M := fun i t =>
    connectedComponentIn (U \ S i t) ((C.neck i).coordinate_map (q i, (t + L) / 2))
  have hPdef : P = Bp b T := by
    change connectedComponentIn (U \ Sp)
        (B.coordinate_map ((B.coordinate_inverse B.center).1, 7 * L / 8)) =
      connectedComponentIn (U \ Sp)
        (B.coordinate_map ((B.coordinate_inverse B.center).1, (T + L) / 2))
    rw [show (T + L) / 2 = 7 * L / 8 by dsimp only [T]; ring]
  obtain ⟨hlevelT, _, hposT, _, hPopen0, _, _, _, _, hclT, _, _, _, htail, _⟩ :=
    hcuts b hb T (hret hT)
  have hPopen : IsOpen P := hPdef.symm ▸ hPopen0
  have hPmem (x : M) : x ∈ P ↔ x ∈ U ∧ T < F b x := by
    have hpos : Bp b T = U ∩ (F b) ⁻¹' Ioi T := hposT
    rw [hPdef, hpos]
    rfl
  have hPclmem (x : M) : x ∈ U ∩ closure P ↔ x ∈ U ∧ T ≤ F b x := by
    rw [hPdef, hclT]
    rfl
  have hSpmem (x : M) : x ∈ Sp ↔ x ∈ U ∧ F b x = T := by
    change x ∈ S b T ↔ _
    have hlevel : U ∩ (F b) ⁻¹' {T} = S b T := hlevelT
    rw [← hlevel]
    rfl
  have hSpcl : Sp ⊆ closure P := by
    intro x hx
    have hs := (hSpmem x).mp hx
    exact ((hPclmem x).mpr ⟨hs.1, hs.2.ge⟩).2
  have hPclosure : U ∩ closure P = P ∪ Sp := by
    ext x
    rw [hPclmem, mem_union, hPmem, hSpmem]
    constructor
    · rintro ⟨hx, hs⟩
      rcases lt_or_eq_of_le hs with hs | hs
      · exact Or.inl ⟨hx, hs⟩
      · exact Or.inr ⟨hx, hs.symm⟩
    · rintro (⟨hx, hs⟩ | ⟨hx, hs⟩)
      · exact ⟨hx, hs.le⟩
      · exact ⟨hx, hs.ge⟩
  have hDm : Dm ⊆ N.cylinderDomain := by
    intro z hz
    exact hdom N hNe ⟨hz.1, hz.2.trans (hhdom z.1).2⟩
  have hGopen : IsOpen G :=
    N.coordinatePartialHomeomorph.isOpen_image_of_subset_source
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt continuous_snd (hh.comp continuous_fst))) hDm
  have hGmem (x : M) :
      x ∈ G ↔ x ∈ N.carrier ∧ (N.coordinate_inverse x).2 <
        h (N.coordinate_inverse x).1 := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨N.coordinate_map_mem (hDm hz), ?_⟩
      rw [N.coordinate_inverse_coordinate_map (hDm hz)]
      exact hz.2
    · rintro ⟨hx, hs⟩
      exact ⟨N.coordinate_inverse x, ⟨(hNheight x hx).1, hs⟩,
        N.coordinate_map_coordinate_inverse hx⟩
  have hSmem (x : M) :
      x ∈ Sm ↔ x ∈ N.carrier ∧
        (N.coordinate_inverse x).2 = h (N.coordinate_inverse x).1 := by
    constructor
    · rintro ⟨v, rfl⟩
      have hd := hdom N hNe (z := (v, h v)) (hhdom v)
      refine ⟨N.coordinate_map_mem hd, ?_⟩
      rw [N.coordinate_inverse_coordinate_map hd]
    · rintro ⟨hx, hs⟩
      refine ⟨(N.coordinate_inverse x).1, ?_⟩
      change N.coordinate_map
        ((N.coordinate_inverse x).1, h (N.coordinate_inverse x).1) = x
      rw [← hs]
      exact N.coordinate_map_coordinate_inverse hx
  have hGU : G ⊆ U := fun x hx => hNU a ha ((hGmem x).mp hx).1
  have hSmU : Sm ⊆ U := fun x hx => hNU a ha ((hSmem x).mp hx).1
  have hSmcl : Sm ⊆ closure G := by
    rintro x ⟨v, rfl⟩
    let l := (h v - L) / 2
    have hl : -L < l := by dsimp only [l]; linarith only [(hhdom v).1]
    have hlh : l < h v := by dsimp only [l]; linarith only [(hhdom v).1]
    have hc : ContinuousWithinAt (fun t : ℝ => N.coordinate_map (v, t))
        (Ioo l (h v)) (h v) := (hline N hNe v (hhdom v)).continuousWithinAt
    apply hc.mem_closure
    · rw [closure_Ioo (ne_of_lt hlh)]
      exact ⟨hlh.le, le_rfl⟩
    · intro t ht
      exact ⟨(v, t), ⟨hl.trans ht.1, ht.2⟩, rfl⟩

  let H0 : M → ℝ := fun x => if x ∈ N.carrier then
    (N.coordinate_inverse x).2 else L
  have hH0 : ContinuousOn H0 U := (C.continuousOn_initial_height_of_finite hshape).1
  have hclN (x : M) (hx : x ∈ U ∩ closure G) : x ∈ N.carrier := by
    by_contra hxN
    let O : Set M := U ∩ H0 ⁻¹' Ioi (-(4 * L / 5))
    have hO : IsOpen O := hH0.isOpen_inter_preimage hUopen isOpen_Ioi
    have hxO : x ∈ O := by
      refine ⟨hx.1, ?_⟩
      change -(4 * L / 5) < H0 x
      rw [show H0 x = L from if_neg hxN]
      linarith only [hL]
    obtain ⟨y, hyO, hyG⟩ := mem_closure_iff.mp hx.2 O hO hxO
    obtain ⟨hyN, hylt⟩ := (hGmem y).mp hyG
    have hyH : -(4 * L / 5) < H0 y := hyO.2
    rw [show H0 y = (N.coordinate_inverse y).2 from if_pos hyN] at hyH
    linarith only [hyH, hylt, (hbound (N.coordinate_inverse y).1).2]
  let Dp : Set RoundCylinderSpace := {z | h z.1 < z.2 ∧ z.2 < L}
  let Gp : Set M := N.coordinate_map '' Dp
  have hDp : Dp ⊆ N.cylinderDomain := by
    intro z hz
    exact hdom N hNe ⟨(hhdom z.1).1.trans hz.1, hz.2⟩
  have hGpopen : IsOpen Gp :=
    N.coordinatePartialHomeomorph.isOpen_image_of_subset_source
      ((isOpen_lt (hh.comp continuous_fst) continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const)) hDp
  have hGpmem (x : M) :
      x ∈ Gp ↔ x ∈ N.carrier ∧ h (N.coordinate_inverse x).1 <
        (N.coordinate_inverse x).2 := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨N.coordinate_map_mem (hDp hz), ?_⟩
      rw [N.coordinate_inverse_coordinate_map (hDp hz)]
      exact hz.1
    · rintro ⟨hx, hs⟩
      exact ⟨N.coordinate_inverse x, ⟨hs, (hNheight x hx).2⟩,
        N.coordinate_map_coordinate_inverse hx⟩
  have hclHeight (x : M) (hx : x ∈ U ∩ closure G) :
      (N.coordinate_inverse x).2 ≤ h (N.coordinate_inverse x).1 := by
    by_contra hn
    have hxGp := (hGpmem x).mpr ⟨hclN x hx, lt_of_not_ge hn⟩
    obtain ⟨y, hyGp, hyG⟩ := mem_closure_iff.mp hx.2 Gp hGpopen hxGp
    exact (not_lt_of_ge ((hGmem y).mp hyG).2.le) ((hGpmem y).mp hyGp).2
  have hGclosure : U ∩ closure G = G ∪ Sm := by
    apply Subset.antisymm
    · intro x hx
      rcases lt_or_eq_of_le (hclHeight x hx) with hs | hs
      · exact Or.inl ((hGmem x).mpr ⟨hclN x hx, hs⟩)
      · exact Or.inr ((hSmem x).mpr ⟨hclN x hx, hs⟩)
    · rintro x (hx | hx)
      · exact ⟨hGU hx, subset_closure hx⟩
      · exact ⟨hSmU hx, hSmcl hx⟩
  have hnegA : Am a tau = U ∩ (F a) ⁻¹' Iio tau :=
    (hcuts a ha tau (hret htau)).2.1
  have hposA : Bp a tau = U ∩ (F a) ⁻¹' Ioi tau :=
    (hcuts a ha tau (hret htau)).2.2.1
  have hnegB : Am b nu = U ∩ (F b) ⁻¹' Iio nu :=
    (hcuts b hb nu (hret hnu)).2.1
  have hNlowP (x : M) (hx : x ∈ N.carrier)
      (hs : (N.coordinate_inverse x).2 < -L / 2) : x ∉ closure P := by
    intro hc
    have hxU := hNU a ha hx
    rcases hab.eq_or_lt with heq | hlt
    · have hFb : F b x = (N.coordinate_inverse x).2 := by
        rw [← heq]
        exact (hF a ha).2.1 x hx
      have hle := ((hPclmem x).mp ⟨hxU, hc⟩).2
      rw [hFb] at hle
      dsimp only [T] at hle
      linarith only [hL, hs, hle]
    · have ho := (horder a ha b hb hlt tau htau T hT).2
      have hxclosed : x ∈ U ∩ closure (Bp b T) := by
        rw [← hPdef]
        exact ⟨hxU, hc⟩
      have hxA : x ∈ Bp a tau := ho hxclosed
      rw [hposA] at hxA
      have ht : tau < F a x := hxA.2
      rw [(hF a ha).2.1 x hx] at ht
      dsimp only [tau] at ht
      linarith only [hL, hs, ht]
  have hBhighG (x : M) (hx : x ∈ B.region nu L) : x ∉ closure G := by
    intro hc
    have hxU := hNU b hb hx.1
    have hxN := hclN x ⟨hxU, hc⟩
    have hs := (hclHeight x ⟨hxU, hc⟩).trans_lt (hbound (N.coordinate_inverse x).1).2
    rcases hab.eq_or_lt with heq | hlt
    · have hNB : N = B := congrArg C.neck heq
      rw [hNB] at hs
      have hn := hx.2.1
      dsimp only [nu] at hn
      linarith only [hL, hs, hn]
    · have hxAm : x ∈ Am a tau := by
        rw [hnegA]
        refine ⟨hxU, ?_⟩
        change F a x < tau
        rw [(hF a ha).2.1 x hxN]
        dsimp only [tau]
        linarith only [hL, hs]
      have ho := (horder a ha b hb hlt tau htau nu hnu).1
      have hxBm : x ∈ Am b nu := ho ⟨hxU, subset_closure hxAm⟩
      rw [hnegB] at hxBm
      have hn : F b x < nu := hxBm.2
      rw [(hF b hb).2.1 x hx.1] at hn
      exact (not_lt_of_ge hn.le) hx.2.1
  have hclosedDisjoint : Disjoint (U ∩ closure G) (U ∩ closure P) := by
    apply disjoint_left.mpr
    intro x hxG hxP
    have hs := (hclHeight x hxG).trans_lt (hbound (N.coordinate_inverse x).1).2
    exact hNlowP x (hclN x hxG) (by linarith only [hL, hs]) hxP.2
  have hSmK : Sm ⊆ K := by
    intro x hx
    refine ⟨hSmU hx, ?_⟩
    rintro (hxG | hxP)
    · have hg := ((hGmem x).mp hxG).2
      rw [((hSmem x).mp hx).2] at hg
      exact (lt_irrefl _ hg)
    · exact disjoint_left.mp hclosedDisjoint ⟨hSmU hx, hSmcl hx⟩
        ⟨((hPmem x).mp hxP).1, subset_closure hxP⟩
  have hSpK : Sp ⊆ K := by
    intro x hx
    have hxU := ((hSpmem x).mp hx).1
    refine ⟨hxU, ?_⟩
    rintro (hxG | hxP)
    · exact disjoint_left.mp hclosedDisjoint ⟨hGU hxG, subset_closure hxG⟩
        ⟨hxU, hSpcl hx⟩
    · have hp := ((hPmem x).mp hxP).2
      rw [((hSpmem x).mp hx).2] at hp
      exact (lt_irrefl _ hp)
  have hSdisjoint : Disjoint Sm Sp := by
    apply disjoint_left.mpr
    intro x hm hp
    exact disjoint_left.mp hclosedDisjoint ⟨hSmU hm, hSmcl hm⟩
      ⟨((hSpmem x).mp hp).1, hSpcl hp⟩

  obtain ⟨lo, _, hloa, hK0compact, hcover⟩ :=
    hcore C (heps.trans (min_le_right _ _)) a b hshape
  let K0 : Set M := ⋃ i ∈ C.shape.active,
    (C.neck i).coordinate_map '' (univ ×ˢ Icc (lo i) T)
  change IsCompact K0 at hK0compact
  change U = (K0 ∪ N.region (-L) (lo a)) ∪ B.region T L at hcover
  rw [hloa] at hcover
  let J : Set M := N.coordinate_map '' (univ ×ˢ Icc (-(9 * L / 10)) (-L / 2))
  have hJcompact : IsCompact J := by
    apply N.isCompact_coordinate_slab
    · rw [hNe]
      change -L < -(9 * L / 10)
      linarith only [hL]
    · rw [hNe]
      change -L / 2 < L
      linarith only [hL]
  have hJU : J ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    apply hNU a ha
    apply N.coordinate_map_mem
    apply hdom N hNe
    constructor <;> linarith only [hL, hz.2.1, hz.2.2]
  have hK0U : K0 ⊆ U := by
    intro x hx
    rw [hcover]
    exact Or.inl (Or.inl hx)
  have hKbound : K ⊆ K0 ∪ J := by
    intro x hx
    have hxcover : x ∈ (K0 ∪ N.region (-L) (-L / 2)) ∪ B.region T L := by
      rw [← hcover]
      exact hx.1
    rcases hxcover with (hx0 | hxm) | hxp
    · exact Or.inl hx0
    · apply Or.inr
      have hs : h (N.coordinate_inverse x).1 ≤ (N.coordinate_inverse x).2 := by
        apply le_of_not_gt
        intro ht
        exact hx.2 (Or.inl ((hGmem x).mpr ⟨hxm.1, ht⟩))
      refine ⟨N.coordinate_inverse x, ⟨mem_univ _, ?_, hxm.2.2.le⟩,
        N.coordinate_map_coordinate_inverse hxm.1⟩
      exact (hbound (N.coordinate_inverse x).1).1.le.trans hs
    · have hxP : x ∈ P := by
        rw [hPdef]
        exact htail hxp
      exact (hx.2 (Or.inr hxP)).elim
  have hKform : K = (K0 ∪ J) ∩ (G ∪ P)ᶜ := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨hKbound hx, hx.2⟩
    · rintro x ⟨hx0 | hxJ, hxout⟩
      · exact ⟨hK0U hx0, hxout⟩
      · exact ⟨hJU hxJ, hxout⟩
  have hKcompact : IsCompact K := by
    rw [hKform]
    exact (hK0compact.union hJcompact).inter_right (hGopen.union hPopen).isClosed_compl
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hKU : K ⊆ U := fun _ hx => hx.1
  have hID : Disjoint (interior K) (closure (G ∪ P)) := by
    apply Disjoint.closure_right _ isOpen_interior
    apply disjoint_left.mpr
    intro x hx hxd
    exact (interior_subset hx).2 hxd
  have hSmclD : Sm ⊆ closure (G ∪ P) :=
    fun _ hx => closure_mono (fun _ hy => Or.inl hy) (hSmcl hx)
  have hSpclD : Sp ⊆ closure (G ∪ P) :=
    fun _ hx => closure_mono (fun _ hy => Or.inr hy) (hSpcl hx)
  have hInterior : interior K = K \ (Sm ∪ Sp) := by
    apply Subset.antisymm
    · intro x hx
      refine ⟨interior_subset hx, ?_⟩
      rintro (hm | hp)
      · exact disjoint_left.mp hID hx (hSmclD hm)
      · exact disjoint_left.mp hID hx (hSpclD hp)
    · rintro x ⟨hxK, hxS⟩
      have hxG : x ∉ closure G := by
        intro hc
        have hm : x ∈ G ∪ Sm := hGclosure ▸ ⟨hxK.1, hc⟩
        rcases hm with hg | hs
        · exact hxK.2 (Or.inl hg)
        · exact hxS (Or.inl hs)
      have hxP : x ∉ closure P := by
        intro hc
        have hm : x ∈ P ∪ Sp := hPclosure ▸ ⟨hxK.1, hc⟩
        rcases hm with hp | hs
        · exact hxK.2 (Or.inr hp)
        · exact hxS (Or.inr hs)
      let O := (U ∩ (closure G)ᶜ) ∩ (closure P)ᶜ
      have hOopen : IsOpen O :=
        (hUopen.inter isClosed_closure.isOpen_compl).inter isClosed_closure.isOpen_compl
      have hOK : O ⊆ K := by
        rintro y ⟨⟨hyU, hyG⟩, hyP⟩
        refine ⟨hyU, ?_⟩
        rintro (hg | hp)
        · exact hyG (subset_closure hg)
        · exact hyP (subset_closure hp)
      exact interior_maximal hOK hOopen ⟨⟨hxK.1, hxG⟩, hxP⟩
  have hfront : frontier K = Sm ∪ Sp := by
    rw [hKclosed.frontier_eq, hInterior]
    apply Subset.antisymm
    · rintro x ⟨hxK, hx⟩
      by_contra hn
      exact hx ⟨hxK, hn⟩
    · intro x hx
      refine ⟨hx.elim (fun hm => hSmK hm) (fun hp => hSpK hp), ?_⟩
      exact fun hi => hi.2 hx
  have hKN (x : M) (hx : x ∈ N.region (-L) (-L / 2)) :
      x ∈ K ↔ h (N.coordinate_inverse x).1 ≤ (N.coordinate_inverse x).2 := by
    constructor
    · intro hxK
      apply le_of_not_gt
      intro hs
      exact hxK.2 (Or.inl ((hGmem x).mpr ⟨hx.1, hs⟩))
    · intro hs
      refine ⟨hNU a ha hx.1, ?_⟩
      rintro (hg | hp)
      · exact not_lt_of_ge hs ((hGmem x).mp hg).2
      · exact hNlowP x hx.1 hx.2.2 (subset_closure hp)
  have hIN (x : M) (hx : x ∈ N.region (-L) (-L / 2)) :
      x ∈ interior K ↔ h (N.coordinate_inverse x).1 < (N.coordinate_inverse x).2 := by
    rw [hInterior]
    constructor
    · rintro ⟨hxK, hxS⟩
      have hs := (hKN x hx).mp hxK
      by_contra hn
      have heq := le_antisymm (le_of_not_gt hn) hs
      exact hxS (Or.inl ((hSmem x).mpr ⟨hx.1, heq⟩))
    · intro hs
      refine ⟨(hKN x hx).mpr hs.le, ?_⟩
      rintro (hm | hp)
      · have heq := ((hSmem x).mp hm).2
        exact (ne_of_lt hs) heq.symm
      · exact hNlowP x hx.1 hx.2.2 (hSpcl hp)
  have hKB (x : M) (hx : x ∈ B.region nu L) :
      x ∈ K ↔ (B.coordinate_inverse x).2 ≤ T := by
    constructor
    · intro hxK
      apply le_of_not_gt
      intro hs
      apply hxK.2
      apply Or.inr
      apply (hPmem x).mpr
      exact ⟨hNU b hb hx.1, by rwa [(hF b hb).2.1 x hx.1]⟩
    · intro hs
      refine ⟨hNU b hb hx.1, ?_⟩
      rintro (hg | hp)
      · exact hBhighG x hx (subset_closure hg)
      · have ht := ((hPmem x).mp hp).2
        rw [(hF b hb).2.1 x hx.1] at ht
        exact not_lt_of_ge hs ht
  have hIB (x : M) (hx : x ∈ B.region nu L) :
      x ∈ interior K ↔ (B.coordinate_inverse x).2 < T := by
    rw [hInterior]
    constructor
    · rintro ⟨hxK, hxS⟩
      have hs := (hKB x hx).mp hxK
      by_contra hn
      have heq := le_antisymm hs (le_of_not_gt hn)
      apply hxS
      apply Or.inr
      apply (hSpmem x).mpr
      exact ⟨hNU b hb hx.1, ((hF b hb).2.1 x hx.1).trans heq⟩
    · intro hs
      refine ⟨(hKB x hx).mpr hs.le, ?_⟩
      rintro (hm | hp)
      · exact hBhighG x hx (hSmcl hm)
      · have ht := ((hSpmem x).mp hp).2
        rw [(hF b hb).2.1 x hx.1] at ht
        exact (ne_of_lt hs) ht
  have hNclosed : K ∩ N.region (-L) (-L / 2) = N.coordinate_map ''
      {z : RoundCylinderSpace | -L < z.2 ∧ h z.1 ≤ z.2 ∧ z.2 < -L / 2} := by
    apply Subset.antisymm
    · rintro x ⟨hxK, hxN⟩
      exact ⟨N.coordinate_inverse x, ⟨hxN.2.1, (hKN x hxN).mp hxK, hxN.2.2⟩,
        N.coordinate_map_coordinate_inverse hxN.1⟩
    · rintro x ⟨z, hz, rfl⟩
      have hd := hdom N hNe (z := z)
        (show z.2 ∈ Ioo (-L) L from ⟨hz.1, by linarith only [hL, hz.2.2]⟩)
      have hxN : N.coordinate_map z ∈ N.region (-L) (-L / 2) := by
        refine ⟨N.coordinate_map_mem hd, ?_⟩
        rw [N.coordinate_inverse_coordinate_map hd]
        exact ⟨hz.1, hz.2.2⟩
      refine ⟨(hKN _ hxN).mpr ?_, hxN⟩
      rw [N.coordinate_inverse_coordinate_map hd]
      exact hz.2.1
  have hNinterior : interior K ∩ N.region (-L) (-L / 2) = N.coordinate_map ''
      {z : RoundCylinderSpace | -L < z.2 ∧ h z.1 < z.2 ∧ z.2 < -L / 2} := by
    apply Subset.antisymm
    · rintro x ⟨hxK, hxN⟩
      exact ⟨N.coordinate_inverse x, ⟨hxN.2.1, (hIN x hxN).mp hxK, hxN.2.2⟩,
        N.coordinate_map_coordinate_inverse hxN.1⟩
    · rintro x ⟨z, hz, rfl⟩
      have hd := hdom N hNe (z := z)
        (show z.2 ∈ Ioo (-L) L from ⟨hz.1, by linarith only [hL, hz.2.2]⟩)
      have hxN : N.coordinate_map z ∈ N.region (-L) (-L / 2) := by
        refine ⟨N.coordinate_map_mem hd, ?_⟩
        rw [N.coordinate_inverse_coordinate_map hd]
        exact ⟨hz.1, hz.2.2⟩
      refine ⟨(hIN _ hxN).mpr ?_, hxN⟩
      rw [N.coordinate_inverse_coordinate_map hd]
      exact hz.2.1
  have hBclosed : K ∩ B.region nu L =
      B.coordinate_map '' (univ ×ˢ Ioc nu T) := by
    apply Subset.antisymm
    · rintro x ⟨hxK, hxB⟩
      exact ⟨B.coordinate_inverse x, ⟨mem_univ _, hxB.2.1, (hKB x hxB).mp hxK⟩,
        B.coordinate_map_coordinate_inverse hxB.1⟩
    · rintro x ⟨z, hz, rfl⟩
      have hd := hdom B hBe (z := z)
        (show z.2 ∈ Ioo (-L) L from
          ⟨(hret hnu).1.trans hz.2.1, hz.2.2.trans_lt hT.2⟩)
      have hxB : B.coordinate_map z ∈ B.region nu L := by
        refine ⟨B.coordinate_map_mem hd, ?_⟩
        rw [B.coordinate_inverse_coordinate_map hd]
        exact ⟨hz.2.1, hz.2.2.trans_lt hT.2⟩
      refine ⟨(hKB _ hxB).mpr ?_, hxB⟩
      rw [B.coordinate_inverse_coordinate_map hd]
      exact hz.2.2
  have hBinterior : interior K ∩ B.region nu L = B.region nu T := by
    apply Subset.antisymm
    · rintro x ⟨hxI, hxB⟩
      exact ⟨hxB.1, hxB.2.1, (hIB x hxB).mp hxI⟩
    · intro x hx
      have hxB : x ∈ B.region nu L := ⟨hx.1, hx.2.1, hx.2.2.trans hT.2⟩
      exact ⟨(hIB x hxB).mpr hx.2.2, hxB⟩
  have hSmclI : Sm ⊆ closure (interior K) := by
    rintro x ⟨v, rfl⟩
    let r := (h v - L / 2) / 2
    have hhr : h v < r := by
      dsimp only [r]
      linarith only [hL, (hbound v).2]
    have hr : r < -L / 2 := by
      dsimp only [r]
      linarith only [hL, (hbound v).2]
    have hc : ContinuousWithinAt (fun s : ℝ => N.coordinate_map (v, s))
        (Ioo (h v) r) (h v) := (hline N hNe v (hhdom v)).continuousWithinAt
    apply hc.mem_closure
    · rw [closure_Ioo (ne_of_lt hhr)]
      exact ⟨le_rfl, hhr.le⟩
    · intro s hs
      have hd := hdom N hNe (z := (v, s))
        (show s ∈ Ioo (-L) L from
          ⟨(hhdom v).1.trans hs.1, by linarith only [hL, hs.2, hr]⟩)
      have hxN : N.coordinate_map (v, s) ∈ N.region (-L) (-L / 2) := by
        refine ⟨N.coordinate_map_mem hd, ?_⟩
        rw [N.coordinate_inverse_coordinate_map hd]
        exact ⟨(hhdom v).1.trans hs.1, hs.2.trans hr⟩
      apply (hIN _ hxN).mpr
      rw [N.coordinate_inverse_coordinate_map hd]
      exact hs.1
  have hSpclI : Sp ⊆ closure (interior K) := by
    rintro x ⟨v, rfl⟩
    let l := (nu + T) / 2
    have hnT : nu < T := by dsimp only [nu, T]; linarith only [hL]
    have hnl : nu < l := by dsimp only [l]; linarith only [hnT]
    have hlT : l < T := by dsimp only [l]; linarith only [hnT]
    have hc : ContinuousWithinAt (fun s : ℝ => B.coordinate_map (v, s))
        (Ioo l T) T := (hline B hBe v (hret hT)).continuousWithinAt
    apply hc.mem_closure
    · rw [closure_Ioo (ne_of_lt hlT)]
      exact ⟨hlT.le, le_rfl⟩
    · intro s hs
      have hd := hdom B hBe (z := (v, s))
        (show s ∈ Ioo (-L) L from
          ⟨(hret hnu).1.trans (hnl.trans hs.1), hs.2.trans hT.2⟩)
      have hxB : B.coordinate_map (v, s) ∈ B.region nu L := by
        refine ⟨B.coordinate_map_mem hd, ?_⟩
        rw [B.coordinate_inverse_coordinate_map hd]
        exact ⟨hnl.trans hs.1, hs.2.trans hT.2⟩
      apply (hIB _ hxB).mpr
      rw [B.coordinate_inverse_coordinate_map hd]
      exact hs.2
  have hregular : closure (interior K) = K := by
    apply Subset.antisymm hKclosed.closure_interior_subset
    intro x hx
    by_cases hs : x ∈ Sm ∪ Sp
    · exact hs.elim (fun hm => hSmclI hm) (fun hp => hSpclI hp)
    · apply subset_closure
      rw [hInterior]
      exact ⟨hx, hs⟩
  exact ⟨hUopen, hGopen, hPopen, hGclosure, hPclosure, hclosedDisjoint,
    hKcompact, hKU, hregular, hInterior, hfront, hSdisjoint,
    hNclosed, hNinterior, hBclosed, hBinterior⟩

end PoincareConjecture
