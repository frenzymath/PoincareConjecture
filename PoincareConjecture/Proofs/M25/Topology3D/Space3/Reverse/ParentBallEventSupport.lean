import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallEventContainment
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem RegularSurgeryEvent.exists_reunion_core_tube_buffer
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (j : Fin 2)
    (lo hi : ℝ) (hlo : -E.data.width < lo)
    (hhi : hi < E.data.width / 2 * (1 - E.radius)) :
    let T := E.reunionTube j
    let core := (fun q : UnitTwoSphere => parent (q, 0)) ''
      ((![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] j) ''
        closedBall (0 : E2) E.radius)
    ∃ ε : ℝ, 0 < ε ∧
      closedBall (0 : E2) (1 + ε) ×ˢ Icc lo hi ⊆ T.source ∧
      Disjoint core (T '' (closedBall (0 : E2) (1 + ε) ×ˢ Icc lo hi)) := by
  let T := E.reunionTube j
  let core := (fun q : UnitTwoSphere => parent (q, 0)) ''
    ((![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] j) ''
      closedBall (0 : E2) E.radius)
  let K := closedBall (0 : E2) 1 ×ˢ Icc lo hi
  let V := T.source ∩ T ⁻¹' coreᶜ
  have hV : IsOpen V :=
    T.isOpen_inter_preimage (E.reunion_core_isCompact j).isClosed.isOpen_compl
  have hKV : K ⊆ V := by
    intro p hp
    refine ⟨(E.reunionTube_spec j).2.2.2.2.1 ⟨hp.1, mem_univ _⟩, ?_⟩
    intro hcore
    exact disjoint_left.mp (E.reunion_core_disjoint_strip j) hcore
      ⟨p, ⟨hp.1, hlo.trans_le hp.2.1, hp.2.2.trans_lt hhi⟩, rfl⟩
  obtain ⟨δ, hδ, hthick⟩ :=
    ((isCompact_closedBall (0 : E2) 1).prod isCompact_Icc).exists_thickening_subset_open
      hV hKV
  have hbuffer : closedBall (0 : E2) (1 + δ / 2) ×ˢ Icc lo hi ⊆ V := by
    intro p hp
    have hnorm := mem_closedBall_zero_iff.mp hp.1
    have hx : p.1 ∈ thickening δ (closedBall (0 : E2) 1) := by
      rw [thickening_closedBall hδ (by norm_num), mem_ball_zero_iff]
      linarith only [hnorm, hδ]
    obtain ⟨x, hx, hdist⟩ := mem_thickening_iff.mp hx
    apply hthick
    refine mem_thickening_iff.mpr ⟨(x, p.2), ⟨hx, hp.2⟩, ?_⟩
    simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg : 0 ≤ dist p.1 x)]
      using hdist
  refine ⟨δ / 2, half_pos hδ, fun p hp => (hbuffer hp).1, ?_⟩
  apply disjoint_left.mpr
  rintro y hy ⟨p, hp, rfl⟩
  exact (hbuffer hp).2 hy

theorem RegularSurgeryEvent.closedAnnulus_inter_closedRegion_subset_cap
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (j : Fin 2)
    (B : BallNeighborhoodChart E3 E3)
    (hboundary : B.boundary = E.child j '' (univ ×ˢ ({0} : Set ℝ)))
    (hmid : E.data.tube (0, E.cutHeight) ∉ B.closedRegion) :
    let a := E.data.width / 2 * (1 - E.radius)
    let annulusClosed := E.data.tube ''
      (sphere (0 : E2) 1 ×ˢ Icc (E.cutHeight - a) (E.cutHeight + a))
    B.closedRegion ∩ annulusClosed ⊆ (E.newCap j).cap := by
  let a := E.data.width / 2 * (1 - E.radius)
  let T := E.reunionTube j
  let core := (fun q : UnitTwoSphere => parent (q, 0)) ''
    ((![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] j) ''
      closedBall (0 : E2) E.radius)
  obtain ⟨_hd, ha, hak, hkd, hl, hsmall⟩ := E.parameter_bounds
  change 0 < a at ha
  change a < E.data.width / 2 at hak
  change E.scale * E.profile.heightBound < a / 4 at hsmall
  have had : a < E.data.width := hak.trans hkd
  obtain ⟨hcap, hseam, _hotherSeam, _hs, _hos, _hopen, hclosed, _hrest⟩ :=
    E.reunion_region_identities j
  obtain ⟨hTf, _hTs, _hTt, _hTi, hsource, _hTsm, _hTism, _hTh⟩ :=
    E.reunionTube_spec j
  have hcapBounds (p : E2 × ℝ) (hp : p ∈ T.source)
      (hc : T p ∈ (E.newCap j).cap) : ‖p.1‖ ≤ 1 ∧ 0 < p.2 := by
    rw [← hcap] at hc
    obtain ⟨q, _hq, heq⟩ := hc
    rw [SurgeryCapProfile.capMap_apply] at heq
    simp only [zero_add, one_mul] at heq
    have hqs : ((E.profile.model q).1, a + E.scale * (E.profile.model q).2) ∈
        T.source :=
      hsource ⟨mem_closedBall_zero_iff.mpr (E.profile.model_fst_norm_le q), mem_univ _⟩
    have hpq := T.injOn hqs hp heq
    have hx := congrArg Prod.fst hpq
    have hz := congrArg Prod.snd hpq
    refine ⟨hx ▸ E.profile.model_fst_norm_le q, ?_⟩
    have hlo := mul_le_mul_of_nonneg_left
      (abs_le.mp (E.profile.height_bound q)).1 hl.le
    change E.scale * (-E.profile.heightBound) ≤ E.scale * (E.profile.model q).2 at hlo
    change a + E.scale * (E.profile.model q).2 = p.2 at hz
    nlinarith only [hlo, hsmall, ha, hz]
  change B.closedRegion ∩ (E.data.tube ''
    (sphere (0 : E2) 1 ×ˢ Icc (E.cutHeight - a) (E.cutHeight + a))) ⊆ (E.newCap j).cap
  intro y hy
  by_contra hnot
  have hyAnn := hy.2
  rw [← hclosed] at hyAnn
  obtain ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩ := hyAnn
  change -a ≤ z ∧ z ≤ a at hz
  have hxn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
  have hza : z < a := by
    apply lt_of_le_of_ne hz.2
    intro heq
    have hs : T (x, z) ∈ (E.newCap j).seam := by
      rw [← hseam]
      exact ⟨(x, z), ⟨hx, heq⟩, rfl⟩
    rw [← (E.region_identities).2.2.2.2.1 j] at hs
    exact hnot hs.2
  let lo := min z 0
  let hi := max z 0
  have hlo : -E.data.width < lo := lt_min (by linarith only [hz.1, had])
    (neg_neg_of_pos E.data.width_pos)
  have hhi : hi < a := max_lt hza ha
  obtain ⟨ε, hε, hbuffer, havoid⟩ := E.exists_reunion_core_tube_buffer j lo hi hlo hhi
  let v := (1 + ε / 2) • x
  let p1 : ℝ → E2 × ℝ := fun s => ((1 + s * ε / 2) • x, z)
  let p2 : ℝ → E2 × ℝ := fun s => (v, (1 - s) * z)
  let p3 : ℝ → E2 × ℝ := fun s => ((1 - s) • v, 0)
  have hvn : ‖v‖ = 1 + ε / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith only [hε]), hxn, mul_one]
  have hp1 (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      p1 s ∈ closedBall (0 : E2) (1 + ε) ×ˢ Icc lo hi := by
    refine ⟨mem_closedBall_zero_iff.mpr ?_, min_le_left _ _, le_max_left _ _⟩
    change ‖(1 + s * ε / 2) • x‖ ≤ 1 + ε
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by nlinarith only [hs.1, hε]),
      hxn, mul_one]
    nlinarith only [hs.2, hε]
  have hp2 (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      p2 s ∈ closedBall (0 : E2) (1 + ε) ×ˢ Icc lo hi := by
    refine ⟨mem_closedBall_zero_iff.mpr (by change ‖v‖ ≤ _; rw [hvn]; linarith), ?_⟩
    change min z 0 ≤ (1 - s) * z ∧ (1 - s) * z ≤ max z 0
    rcases le_total z 0 with hz0 | hz0
    · rw [min_eq_left hz0, max_eq_right hz0]
      constructor <;> nlinarith only [hs.1, hs.2, hz0]
    · rw [min_eq_right hz0, max_eq_left hz0]
      constructor <;> nlinarith only [hs.1, hs.2, hz0]
  have hp3 (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      p3 s ∈ closedBall (0 : E2) (1 + ε) ×ˢ Icc lo hi := by
    refine ⟨mem_closedBall_zero_iff.mpr ?_, min_le_right _ _, le_max_right _ _⟩
    change ‖(1 - s) • v‖ ≤ 1 + ε
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2), hvn]
    nlinarith only [hs.1, hs.2, hε]
  have hp1cap (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : T (p1 s) ∉ (E.newCap j).cap := by
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · subst s
      simpa only [p1, zero_mul, zero_div, add_zero, one_smul] using hnot
    · intro hc
      have hn := (hcapBounds (p1 s) (hbuffer (hp1 s hs)) hc).1
      change ‖(1 + s * ε / 2) • x‖ ≤ 1 at hn
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by nlinarith only [hs0, hε]),
        hxn, mul_one] at hn
      nlinarith only [hs0, hε, hn]
  have hp2cap (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : T (p2 s) ∉ (E.newCap j).cap := by
    intro hc
    have hn := (hcapBounds (p2 s) (hbuffer (hp2 s hs)) hc).1
    change ‖v‖ ≤ 1 at hn
    rw [hvn] at hn
    linarith only [hn, hε]
  have hp3cap (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : T (p3 s) ∉ (E.newCap j).cap := by
    intro hc
    exact lt_irrefl (0 : ℝ) ((hcapBounds (p3 s) (hbuffer (hp3 s hs)) hc).2)
  let P1 := (fun s => T (p1 s)) '' Icc (0 : ℝ) 1
  let P2 := (fun s => T (p2 s)) '' Icc (0 : ℝ) 1
  let P3 := (fun s => T (p3 s)) '' Icc (0 : ℝ) 1
  have hconnected (p : ℝ → E2 × ℝ) (hc : Continuous p)
      (hp : ∀ s ∈ Icc (0 : ℝ) 1,
        p s ∈ closedBall (0 : E2) (1 + ε) ×ˢ Icc lo hi) :
      IsPreconnected ((fun s => T (p s)) '' Icc (0 : ℝ) 1) :=
    isPreconnected_Icc.image _ (T.continuousOn.comp hc.continuousOn
      (fun s hs => hbuffer (hp s hs)))
  have hc1 : IsPreconnected P1 := hconnected p1 (by fun_prop) hp1
  have hc2 : IsPreconnected P2 := hconnected p2 (by fun_prop) hp2
  have hc3 : IsPreconnected P3 := hconnected p3 (by fun_prop) hp3
  have h12 : (P1 ∩ P2).Nonempty := by
    refine ⟨T (v, z), ⟨1, by norm_num, ?_⟩, ⟨0, by norm_num, ?_⟩⟩
    · simp only [p1, v, one_mul]
    · simp only [p2, sub_zero, one_mul]
  have h23 : ((P1 ∪ P2) ∩ P3).Nonempty := by
    refine ⟨T (v, 0), Or.inr ⟨1, by norm_num, ?_⟩, ⟨0, by norm_num, ?_⟩⟩
    · simp only [p2, sub_self, zero_mul]
    · simp only [p3, sub_zero, one_smul]
  have hconn : IsPreconnected (P1 ∪ P2 ∪ P3) :=
    IsPreconnected.union' h23 (IsPreconnected.union' h12 hc1 hc2) hc3
  have hdisPath (p : ℝ → E2 × ℝ)
      (hp : ∀ s ∈ Icc (0 : ℝ) 1,
        p s ∈ closedBall (0 : E2) (1 + ε) ×ˢ Icc lo hi)
      (hc : ∀ s ∈ Icc (0 : ℝ) 1, T (p s) ∉ (E.newCap j).cap) :
      Disjoint ((fun s => T (p s)) '' Icc (0 : ℝ) 1) B.boundary := by
    apply disjoint_left.mpr
    rintro y ⟨s, hs, rfl⟩ hyB
    rw [hboundary, (E.region_identities).2.2.2.1 j] at hyB
    rcases hyB with hyCore | hyCap
    · exact disjoint_left.mp havoid hyCore ⟨p s, hp s hs, rfl⟩
    · exact hc s hs hyCap
  have hdis : Disjoint (P1 ∪ P2 ∪ P3) B.boundary :=
    ((hdisPath p1 hp1 hp1cap).union_left (hdisPath p2 hp2 hp2cap)).union_left
      (hdisPath p3 hp3 hp3cap)
  have hmidP : E.data.tube (0, E.cutHeight) ∈ P1 ∪ P2 ∪ P3 := by
    refine Or.inr ⟨1, by norm_num, ?_⟩
    simp only [p3, sub_self, zero_smul]
    simpa only [mul_zero, add_zero] using hTf (0, 0)
  have hyP : T (x, z) ∈ P1 ∪ P2 ∪ P3 := by
    refine Or.inl (Or.inl ⟨0, by norm_num, ?_⟩)
    simp only [p1, zero_mul, zero_div, add_zero, one_smul]
  rcases B.preconnected_subset_inside_or_outside hconn hdis with hin | hout
  · exact hmid (image_mono ball_subset_closedBall (hin hmidP))
  · exact hout hyP hy.1

theorem RegularSurgeryEvent.mid_outside_of_movable_child
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u)
    (A : Fin 2 → BallNeighborhoodChart E3 E3)
    (hboundary : ∀ k : Fin 2,
      (A k).boundary = E.child k '' (univ ×ˢ ({0} : Set ℝ)))
    (i : Fin 2)
    (hregions : Disjoint (A i).closedRegion (A (![1, 0] i)).closedRegion ∨
      (A (![1, 0] i)).closedRegion ⊆ (A i).inside) :
    E.data.tube (0, E.cutHeight) ∉ (A (![1, 0] i)).closedRegion := by
  let a := E.data.width / 2 * (1 - E.radius)
  let j : Fin 2 := ![1, 0] i
  let sigma : ℝ := ![1, -1] j
  let T := E.reunionTube j
  let D := nativeCapAmbientDiffeomorph (E.child j) u (E.newCap j)
  let core := (fun p : UnitTwoSphere => parent (p, 0)) ''
    ((![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] j) ''
      closedBall (0 : E2) E.radius)
  let q0 := southSpherePoint (0 : E2)
  obtain ⟨_hd, ha, hak, hkd, hl, hsmall⟩ := E.parameter_bounds
  change 0 < a at ha
  change a < E.data.width / 2 at hak
  change E.scale * E.profile.heightBound < a / 4 at hsmall
  have had : a < E.data.width := hak.trans hkd
  have hlM : E.scale ≤ E.scale * E.profile.heightBound := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left E.profile.one_le_heightBound hl.le
  have hal : 0 < a - E.scale := by linarith only [ha, hlM, hsmall]
  have hq0 : heightCoordinates (q0 : E3) = (0, -1) := by
    simpa [q0] using southSpherePoint_coordinates (0 : E2) (by norm_num)
  have hsigma : sigma ≠ 0 := by fin_cases i <;> norm_num [sigma, j]
  have hsigns : (![1, -1] i : ℝ) = -sigma := by
    fin_cases i <;> norm_num [sigma, j]
  obtain ⟨hP, hTube, ht, hc, hScale, hSign⟩ := E.newCap_spec j
  obtain ⟨hDformula, _hDinv, hDsphere, _hDray⟩ :=
    nativeCapAmbientDiffeomorph_spec (E.child j) u (E.newCap j)
  obtain ⟨hTformula, _hTs, _hTt, _hTi, hTsource, _hTsm, _hTism, _hTheight⟩ :=
    E.reunionTube_spec j
  have haxisSource (z : ℝ) : (0, z) ∈ T.source :=
    hTsource ⟨by simp, mem_univ _⟩
  have hsegment : IsPreconnected (T '' (({0} : Set E2) ×ˢ Icc (-(a - E.scale)) 0)) := by
    apply (isPreconnected_singleton.prod isPreconnected_Icc).image T
    apply T.continuousOn.mono
    intro p hp
    have hp0 : p.1 = 0 := hp.1
    simpa only [← hp0] using haxisSource p.2
  have hcoreOutside (z : ℝ) (hz : z ∈ Ioo (-E.data.width) a) : T (0, z) ∉ core := by
    intro hcore
    exact disjoint_left.mp (E.reunion_core_disjoint_strip j) hcore
      ⟨(0, z), ⟨by simp, hz⟩, rfl⟩
  have hnegativeCap (z : ℝ) (hz : z ≤ 0) : T (0, z) ∉ (E.newCap j).cap := by
    intro hcap
    rw [(E.newCap j).cap_eq_image] at hcap
    obtain ⟨q, _hq, hqz⟩ := hcap
    have hsource := (hDsphere q).1
    rw [hTube] at hsource
    have heq := (hDsphere q).2.trans hqz
    rw [hTube, hTformula] at heq
    have hq := E.data.tube.injOn hsource (E.data.tube_source ⟨by simp, mem_univ _⟩) heq
    have hcoord := congrArg Prod.snd hq
    have hformula := congrArg Prod.snd (hDformula (q : E3))
    simp only [hP, ht, hc, hScale, hSign] at hformula
    have hheight : (D (q : E3)).2 =
        E.cutHeight + sigma * (a + E.scale * (E.profile.model q).2) := hformula
    rw [hheight] at hcoord
    have hmodel : a + E.scale * (E.profile.model q).2 = z :=
      mul_left_cancel₀ hsigma (add_left_cancel hcoord)
    have hlow := mul_le_mul_of_nonneg_left
      (abs_le.mp (E.profile.height_bound q)).1 hl.le
    change E.scale * (-E.profile.heightBound) ≤ E.scale * (E.profile.model q).2 at hlow
    nlinarith only [hlow, hsmall, ha, hmodel, hz]
  have hnegativeOutside (z : ℝ) (hz : z ∈ Icc (-(a - E.scale)) 0) :
      T (0, z) ∉ (A j).boundary := by
    rw [hboundary j, (E.region_identities).2.2.2.1 j]
    intro hy
    rcases hy with hcore | hcap
    · exact hcoreOutside z
        ⟨by linarith only [hz.1, had, hl], by linarith only [hz.2, ha]⟩ hcore
    · exact hnegativeCap z hz.2 hcap
  have hcenter :
      E.data.tube (0, E.cutHeight + (![1, -1] i : ℝ) * (a - E.scale)) ∈
        (A i).boundary := by
    obtain ⟨hPk, hTk, htk, hck, hlk, hsk⟩ := E.newCap_spec i
    obtain ⟨_hf, _hi, hq, hr⟩ :=
      nativeCapAmbientDiffeomorph_spec (E.child i) u (E.newCap i)
    have hpoint := (hq q0).2
    have hrone := hr 1
    simp only [one_smul, htk, hck, hlk, hsk, mul_one] at hrone
    rw [hrone, hTk, hPk, htk, hck, hlk, hsk] at hpoint
    rw [hboundary i, (E.region_identities).2.2.2.1 i]
    right
    rw [(E.newCap i).cap_eq_image, hPk, hTk, htk, hck, hlk, hsk]
    refine ⟨q0, ?_, hpoint.symm⟩
    change (heightCoordinates (q0 : E3)).2 ≤ 0
    rw [hq0]
    norm_num
  let ni := E.data.tube (0, E.cutHeight + (![1, -1] i : ℝ) * (a - E.scale))
  have hni : ni ∉ (A j).closedRegion := by
    intro hy
    rcases hregions with hd | hn
    · exact disjoint_left.mp hd (image_mono sphere_subset_closedBall hcenter) hy
    · exact disjoint_left.mp (A i).inside_disjoint_boundary (hn hy) hcenter
  have hniT : T (0, -(a - E.scale)) = ni := by
    rw [hTformula]
    dsimp only [ni]
    rw [hsigns]
    apply congrArg E.data.tube
    apply Prod.ext
    · rfl
    · ring
  let L := T '' (({0} : Set E2) ×ˢ Icc (-(a - E.scale)) 0)
  have hLdis : Disjoint L (A j).boundary := by
    apply disjoint_left.mpr
    rintro y ⟨p, hp, rfl⟩ hy
    have hp0 : p.1 = 0 := hp.1
    have hp' : p = (0, p.2) := Prod.ext hp0 rfl
    rw [hp'] at hy
    exact hnegativeOutside p.2 hp.2 hy
  have hLout : L ⊆ (A j).closedRegionᶜ := by
    rcases (A j).preconnected_subset_inside_or_outside hsegment hLdis with hin | hout
    · have hniL : ni ∈ L :=
        ⟨(0, -(a - E.scale)), ⟨rfl, le_rfl, by linarith only [hal]⟩, hniT⟩
      exact False.elim (hni (image_mono ball_subset_closedBall (hin hniL)))
    · exact hout
  have hmid : T (0, 0) ∉ (A j).closedRegion :=
    hLout ⟨(0, 0), ⟨rfl, by linarith only [hal], le_rfl⟩, rfl⟩
  simpa only [T, hTformula, mul_zero, add_zero] using hmid

theorem RegularSurgeryEvent.exists_compression_support_domain
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u)
    (A : Fin 2 → BallNeighborhoodChart E3 E3)
    (hboundary : ∀ k : Fin 2,
      (A k).boundary = E.child k '' (univ ×ˢ ({0} : Set ℝ)))
    (i : Fin 2)
    (hregions : Disjoint (A i).closedRegion (A (![1, 0] i)).closedRegion ∨
      (A (![1, 0] i)).closedRegion ⊆ (A i).inside) :
    let j : Fin 2 := ![1, 0] i
    let a := E.data.width / 2 * (1 - E.radius)
    let annulusClosed := E.data.tube ''
      (sphere (0 : E2) 1 ×ˢ Icc (E.cutHeight - a) (E.cutHeight + a))
    IsCompact annulusClosed ∧
      (A j).closedRegion ∩ annulusClosed ⊆ (E.newCap j).cap ∧
      ∃ Ω : Set E3, IsOpen Ω ∧
        (Disjoint (A i).closedRegion (A j).closedRegion →
          Ω = ((A i).closedRegion ∪ annulusClosed)ᶜ) ∧
        (¬Disjoint (A i).closedRegion (A j).closedRegion →
          Ω = (A i).inside \ annulusClosed) ∧
        (A j).closedRegion \ (E.newCap j).cap ⊆ Ω ∧
        Disjoint Ω ((A i).boundary ∪ annulusClosed) := by
  classical
  let j : Fin 2 := ![1, 0] i
  let a := E.data.width / 2 * (1 - E.radius)
  let annulusClosed := E.data.tube ''
    (sphere (0 : E2) 1 ×ˢ Icc (E.cutHeight - a) (E.cutHeight + a))
  have hc : IsCompact annulusClosed :=
    ((isCompact_sphere (0 : E2) 1).prod isCompact_Icc).image_of_continuousOn
      (E.data.tube.continuousOn.mono (fun _ hp =>
        E.data.tube_source ⟨sphere_subset_closedBall hp.1, mem_univ _⟩))
  have hcap : (A j).closedRegion ∩ annulusClosed ⊆ (E.newCap j).cap :=
    E.closedAnnulus_inter_closedRegion_subset_cap j (A j) (hboundary j)
      (E.mid_outside_of_movable_child A hboundary i hregions)
  have hnotAnn (y : E3) (hy : y ∈ (A j).closedRegion \ (E.newCap j).cap) :
      y ∉ annulusClosed := fun h => hy.2 (hcap ⟨hy.1, h⟩)
  refine ⟨hc, hcap, ?_⟩
  by_cases hd : Disjoint (A i).closedRegion (A j).closedRegion
  · refine ⟨((A i).closedRegion ∪ annulusClosed)ᶜ,
      ((A i).closedRegion_compact.isClosed.union hc.isClosed).isOpen_compl,
      fun _ => rfl, fun hn => (hn hd).elim, ?_, ?_⟩
    · intro y hy hmem
      exact hmem.elim (fun hi => disjoint_left.mp hd hi hy.1) (hnotAnn y hy)
    · apply disjoint_left.mpr
      intro y hy hmem
      exact hmem.elim
        (fun hi => hy (Or.inl (image_mono sphere_subset_closedBall hi)))
        (fun ha => hy (Or.inr ha))
  · have hn : (A j).closedRegion ⊆ (A i).inside := hregions.resolve_left hd
    refine ⟨(A i).inside \ annulusClosed, (A i).inside_open.sdiff hc.isClosed,
      fun h => (hd h).elim, fun _ => rfl, ?_, ?_⟩
    · intro y hy
      exact ⟨hn hy.1, hnotAnn y hy⟩
    · apply disjoint_left.mpr
      intro y hy hmem
      exact hmem.elim
        (fun hi => disjoint_left.mp (A i).inside_disjoint_boundary hy.1 hi) hy.2

end PoincareConjecture.M25.Topology3D
