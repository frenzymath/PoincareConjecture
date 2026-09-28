import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallEventReferenceModel
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallEventGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhoodNesting
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarOrientation

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem BallNeighborhoodChart.closedRegion_trichotomy
    (A B : BallNeighborhoodChart E3 E3)
    (hdis : Disjoint A.boundary B.boundary) :
    Disjoint A.closedRegion B.closedRegion ∨
      A.closedRegion ⊆ B.inside ∨ B.closedRegion ⊆ A.inside := by
  have hdim : 1 < Module.rank ℝ E3 :=
    Module.one_lt_rank_of_one_lt_finrank (by simp [E3])
  have hAc := A.boundary_connected hdim
  have hBc := B.boundary_connected hdim
  rcases B.preconnected_subset_inside_or_outside hAc.isPreconnected hdis with hAB | hAo
  · exact Or.inr (Or.inl (B.closedRegion_subset_inside_of_boundary_subset A
      hBc.isPreconnected hAc hdis.symm hAB))
  rcases A.preconnected_subset_inside_or_outside hBc.isPreconnected hdis.symm with
      hBA | hBo
  · exact Or.inr (Or.inr (A.closedRegion_subset_inside_of_boundary_subset B
      hAc.isPreconnected hBc hdis hBA))
  have hinsideDisjoint : Disjoint A.inside B.boundary := by
    apply disjoint_left.mpr
    intro y hyA hyB
    exact hBo hyB (image_mono ball_subset_closedBall hyA)
  have hout : A.inside ⊆ B.closedRegionᶜ := by
    rcases B.preconnected_subset_inside_or_outside
        A.inside_connected.isPreconnected hinsideDisjoint with hin | ho
    · have hclosed := closure_mono hin
      rw [A.closure_inside, B.closure_inside] at hclosed
      obtain ⟨y, hy⟩ := hAc.nonempty
      exact False.elim (hAo hy (hclosed (image_mono sphere_subset_closedBall hy)))
    · exact ho
  left
  apply disjoint_left.mpr
  intro y hyA hyB
  rw [← A.inside_union_boundary] at hyA
  exact hyA.elim (fun hy => hout hy hyB) (fun hy => hAo hy hyB)

theorem RegularSurgeryEvent.exists_movable_child_axis_outside
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u)
    (A : Fin 2 → BallNeighborhoodChart E3 E3)
    (hboundary : ∀ j : Fin 2,
      (A j).boundary = E.child j '' (univ ×ˢ ({0} : Set ℝ))) :
    ∃ i : Fin 2,
      let j : Fin 2 := ![1, 0] i
      let a := E.data.width / 2 * (1 - E.radius)
      let sigma : ℝ := ![1, -1] j
      (Disjoint (A i).closedRegion (A j).closedRegion ∨
        (A j).closedRegion ⊆ (A i).inside) ∧
      ∀ z ∈ Ico (0 : ℝ) (a - E.scale),
        E.data.tube (0, E.cutHeight + sigma * z) ∉ (A j).closedRegion := by
  let a := E.data.width / 2 * (1 - E.radius)
  obtain ⟨_hd, ha, hak, hkd, hl, hsmall⟩ := E.parameter_bounds
  change 0 < a at ha
  change a < E.data.width / 2 at hak
  change E.scale * E.profile.heightBound < a / 4 at hsmall
  have had : a < E.data.width := hak.trans hkd
  have hlM : E.scale ≤ E.scale * E.profile.heightBound := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left E.profile.one_le_heightBound hl.le
  have hal : 0 < a - E.scale := by linarith only [ha, hlM, hsmall]
  obtain ⟨_hparent, _hcoreAnn, _hcores, hcover, _hinter, hchildren⟩ := E.region_identities
  have hdis : Disjoint (A 0).boundary (A 1).boundary := by
    rw [hboundary 0, hboundary 1]
    exact hchildren
  have hchoose : ∃ i : Fin 2,
      Disjoint (A i).closedRegion (A (![1, 0] i)).closedRegion ∨
        (A (![1, 0] i)).closedRegion ⊆ (A i).inside := by
    rcases (A 0).closedRegion_trichotomy (A 1) hdis with hd | h01 | h10
    · refine ⟨0, Or.inl ?_⟩
      simpa using hd
    · refine ⟨1, Or.inr ?_⟩
      simpa using h01
    · refine ⟨0, Or.inr ?_⟩
      simpa using h10
  obtain ⟨i, hregions⟩ := hchoose
  let j : Fin 2 := ![1, 0] i
  let sigma : ℝ := ![1, -1] j
  let T := E.reunionTube j
  let D := nativeCapAmbientDiffeomorph (E.child j) u (E.newCap j)
  let core := (fun p : UnitTwoSphere => parent (p, 0)) ''
    ((![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] j) ''
      closedBall (0 : E2) E.radius)
  let q0 := southSpherePoint (0 : E2)
  have hq0 : heightCoordinates (q0 : E3) = (0, -1) := by
    simpa [q0] using southSpherePoint_coordinates (0 : E2) (by norm_num)
  have hsigma : sigma ≠ 0 := by fin_cases i <;> norm_num [sigma, j]
  have hsigns : (![1, -1] i : ℝ) = -sigma := by
    fin_cases i <;> norm_num [sigma, j]
  obtain ⟨hP, hTube, ht, hc, hScale, hSign⟩ := E.newCap_spec j
  obtain ⟨hDformula, _hDinv, hDsphere, hDray⟩ :=
    nativeCapAmbientDiffeomorph_spec (E.child j) u (E.newCap j)
  obtain ⟨hTformula, _hTs, _hTt, _hTi, hTsource, _hTsm, _hTism, _hTheight⟩ :=
    E.reunionTube_spec j
  have haxisSource (z : ℝ) : (0, z) ∈ T.source :=
    hTsource ⟨by simp, mem_univ _⟩
  have hsegment (lo hi : ℝ) :
      IsPreconnected (T '' (({0} : Set E2) ×ˢ Icc lo hi)) := by
    apply (isPreconnected_singleton.prod isPreconnected_Icc).image T
    apply T.continuousOn.mono
    intro p hp
    have hp0 : p.1 = 0 := hp.1
    simpa only [← hp0] using haxisSource p.2
  have hcoreOutside (z : ℝ) (hz : z ∈ Ioo (-E.data.width) a) : T (0, z) ∉ core := by
    intro hcore
    exact disjoint_left.mp (E.reunion_core_disjoint_strip j) hcore
      ⟨(0, z), ⟨by simp, hz⟩, rfl⟩
  have hcapCoordinates (z : ℝ) (hz : T (0, z) ∈ (E.newCap j).cap) :
      ∃ q : UnitTwoSphere, D (q : E3) = (0, E.cutHeight + sigma * z) := by
    rw [(E.newCap j).cap_eq_image] at hz
    obtain ⟨q, _hq, hqz⟩ := hz
    have hsource := (hDsphere q).1
    rw [hTube] at hsource
    have heq := (hDsphere q).2.trans hqz
    rw [hTube, hTformula] at heq
    exact ⟨q, E.data.tube.injOn hsource (E.data.tube_source ⟨by simp, mem_univ _⟩) heq⟩
  have hnegativeCap (z : ℝ) (hz : z ≤ 0) : T (0, z) ∉ (E.newCap j).cap := by
    intro hcap
    obtain ⟨q, hq⟩ := hcapCoordinates z hcap
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
    rw [hboundary j, hcover j]
    intro hy
    rcases hy with hcore | hcap
    · exact hcoreOutside z
        ⟨by linarith only [hz.1, had, hl], by linarith only [hz.2, ha]⟩ hcore
    · exact hnegativeCap z hz.2 hcap
  have hcenter (k : Fin 2) :
      E.data.tube (0, E.cutHeight + (![1, -1] k : ℝ) * (a - E.scale)) ∈
        (A k).boundary := by
    obtain ⟨hPk, hTk, htk, hck, hlk, hsk⟩ := E.newCap_spec k
    obtain ⟨_hf, _hi, hq, hr⟩ :=
      nativeCapAmbientDiffeomorph_spec (E.child k) u (E.newCap k)
    have hpoint := (hq q0).2
    have hrone := hr 1
    simp only [one_smul, htk, hck, hlk, hsk, mul_one] at hrone
    rw [hrone, hTk, hPk, htk, hck, hlk, hsk] at hpoint
    rw [hboundary k, hcover k]
    right
    rw [(E.newCap k).cap_eq_image, hPk, hTk, htk, hck, hlk, hsk]
    refine ⟨q0, ?_, hpoint.symm⟩
    change (heightCoordinates (q0 : E3)).2 ≤ 0
    rw [hq0]
    norm_num
  let ni := E.data.tube (0, E.cutHeight + (![1, -1] i : ℝ) * (a - E.scale))
  have hni : ni ∉ (A j).closedRegion := by
    intro hy
    rcases hregions with hd | hn
    · exact disjoint_left.mp hd (image_mono sphere_subset_closedBall (hcenter i)) hy
    · exact disjoint_left.mp (A i).inside_disjoint_boundary (hn hy) (hcenter i)
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
    rcases (A j).preconnected_subset_inside_or_outside
        (hsegment (-(a - E.scale)) 0) hLdis with hin | hout
    · have hniL : ni ∈ L :=
        ⟨(0, -(a - E.scale)), ⟨rfl, le_rfl, by linarith only [hal]⟩, hniT⟩
      exact False.elim (hni (image_mono ball_subset_closedBall (hin hniL)))
    · exact hout
  have hmid : T (0, 0) ∉ (A j).closedRegion :=
    hLout ⟨(0, 0), ⟨rfl, by linarith only [hal], le_rfl⟩, rfl⟩
  have haxis (z : ℝ) (hz : z ∈ Ico (0 : ℝ) (a - E.scale)) :
      T (0, z) ∉ (A j).boundary := by
    rw [hboundary j, hcover j]
    intro hy
    rcases hy with hcore | hcap
    · exact hcoreOutside z
        ⟨by linarith only [hz.1, E.data.width_pos], by linarith only [hz.2, hl]⟩ hcore
    · obtain ⟨q, hq⟩ := hcapCoordinates z hcap
      let r := (a - z) / E.scale
      have hr : 1 < r := (lt_div_iff₀ hl).mpr (by linarith only [hz.2])
      have hradius : a - E.scale * r = z := by
        dsimp only [r]
        field_simp [hl.ne']
        ring
      have hDr : D (r • (q0 : E3)) = (0, E.cutHeight + sigma * z) := by
        rw [hDray r, ht, hc, hScale, hSign, hradius]
      have heq := D.injective (hq.trans hDr.symm)
      have hnorm := congrArg norm heq
      rw [mem_sphere_zero_iff_norm.mp q.property, norm_smul, Real.norm_eq_abs,
        abs_of_pos (zero_lt_one.trans hr), mem_sphere_zero_iff_norm.mp q0.property,
        mul_one] at hnorm
      linarith only [hr, hnorm]
  refine ⟨i, hregions, ?_⟩
  intro z hz
  let Lz := T '' (({0} : Set E2) ×ˢ Icc (0 : ℝ) z)
  have hLzdis : Disjoint Lz (A j).boundary := by
    apply disjoint_left.mpr
    rintro y ⟨p, hp, rfl⟩ hy
    have hp0 : p.1 = 0 := hp.1
    have hp' : p = (0, p.2) := Prod.ext hp0 rfl
    rw [hp'] at hy
    exact haxis p.2 ⟨hp.2.1, hp.2.2.trans_lt hz.2⟩ hy
  have hLzout : Lz ⊆ (A j).closedRegionᶜ := by
    rcases (A j).preconnected_subset_inside_or_outside (hsegment 0 z) hLzdis with
        hin | hout
    · have hzero : T (0, 0) ∈ Lz := ⟨(0, 0), ⟨rfl, le_rfl, hz.1⟩, rfl⟩
      exact False.elim (hmid (image_mono ball_subset_closedBall (hin hzero)))
    · exact hout
  have hzout := hLzout ⟨(0, z), ⟨rfl, hz.1, le_rfl⟩, rfl⟩
  simpa only [T, hTformula, j, mem_compl_iff] using hzout

theorem RegularSurgeryEvent.exists_canonical_child_containment
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u)
    (A : Fin 2 → BallNeighborhoodChart E3 E3)
    (hboundary : ∀ j : Fin 2,
      (A j).boundary = E.child j '' (univ ×ˢ ({0} : Set ℝ))) :
    ∃ i : Fin 2,
      let j : Fin 2 := ![1, 0] i
      (Disjoint (A i).closedRegion (A j).closedRegion ∨
        (A j).closedRegion ⊆ (A i).inside) ∧
      E.data.tube (0, E.cutHeight) ∉ (A j).closedRegion ∧
      ∃ side : ℝ, side * side = 1 ∧
        (fun p : UnitTwoSphere × ℝ => E.child j (p.1, side * p.2)) ''
          (univ ×ˢ Ioo (-1) 0) ⊆ (A j).inside ∧
        (fun p : UnitTwoSphere × ℝ => E.child j (p.1, side * p.2)) ''
          (univ ×ˢ Ioo 0 1) ⊆ (A j).closedRegionᶜ ∧
        (E.newCap j).sign * (E.newCap j).beta * side < 0 ∧
        (E.canonicalCapBall j).inside ⊆ (A j).inside ∧
        (E.canonicalCapBall j).closedRegion ⊆ (A j).closedRegion := by
  obtain ⟨i, hregions, haxis⟩ := E.exists_movable_child_axis_outside A hboundary
  let j : Fin 2 := ![1, 0] i
  let a := E.data.width / 2 * (1 - E.radius)
  let sigma : ℝ := ![1, -1] j
  let beta := (E.newCap j).beta
  let B := E.canonicalCapBall j
  let D := nativeCapAmbientDiffeomorph (E.child j) u (E.newCap j)
  let q0 := southSpherePoint (0 : E2)
  obtain ⟨_hd, ha, _hak, _hkd, hl, hsmall⟩ := E.parameter_bounds
  change 0 < a at ha
  change E.scale * E.profile.heightBound < a / 4 at hsmall
  have hlM : E.scale ≤ E.scale * E.profile.heightBound := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left E.profile.one_le_heightBound hl.le
  have hal : 0 < a - E.scale := by linarith only [ha, hlM, hsmall]
  have hmid : E.data.tube (0, E.cutHeight) ∉ (A j).closedRegion := by
    simpa only [mul_zero, add_zero] using haxis 0 ⟨le_rfl, hal⟩
  obtain ⟨side, hside, hin, hout⟩ :=
    exists_ball_collar_orientation (E.child j) (E.child_embedding j) (A j) (hboundary j)
  have hsideabs : |side| = 1 := by nlinarith only [hside, sq_abs side, abs_nonneg side]
  have hsidenz : side ≠ 0 := by intro hz; rw [hz, zero_mul] at hside; norm_num at hside
  have hsigma : sigma * sigma = 1 := by fin_cases i <;> norm_num [sigma, j]
  have hsigmanz : sigma ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hsigma
    norm_num at hsigma
  let b := sigma * beta * side
  have hbnz : b ≠ 0 := mul_ne_zero (mul_ne_zero hsigmanz (E.newCap j).beta_ne) hsidenz
  have hab : 0 < |b| := abs_pos.mpr hbnz
  obtain ⟨_hP, hTube, ht, hc, hScale, hSign⟩ := E.newCap_spec j
  have htime (R : ℝ) (hR : 0 < R) : ∃ eta : ℝ,
      0 < eta ∧ eta < (E.newCap j).collarWidth ∧ eta < 1 ∧ |b| * eta < R := by
    let eta := min ((E.newCap j).collarWidth / 2) (min (1 / 2) (R / (2 * |b|)))
    have heta : 0 < eta := lt_min
      (div_pos (E.newCap j).collar_pos (by norm_num))
      (lt_min (by norm_num) (div_pos hR (mul_pos (by norm_num) hab)))
    have hleW : eta ≤ (E.newCap j).collarWidth / 2 := min_le_left _ _
    have hleOne : eta ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hleR : eta ≤ R / (2 * |b|) := (min_le_right _ _).trans (min_le_right _ _)
    have hmul := mul_le_mul_of_nonneg_left hleR hab.le
    have hcancel : |b| * (R / (2 * |b|)) = R / 2 := by
      field_simp [hab.ne']
    rw [hcancel] at hmul
    exact ⟨eta, heta, by linarith only [hleW, (E.newCap j).collar_pos],
      by linarith only [hleOne], by linarith only [hmul, hR]⟩
  have hflat (eta : ℝ) (heta : 0 < eta) (hetaw : eta < (E.newCap j).collarWidth) :
      E.child j ((E.newCap j).flatChart 0, side * (-eta)) =
        E.data.tube (0, E.cutHeight + sigma * (a - E.scale - b * eta)) := by
    have htime' : |side * (-eta)| < (E.newCap j).collarWidth := by
      rw [abs_mul, hsideabs, one_mul, abs_neg, abs_of_pos heta]
      exact hetaw
    rw [(E.newCap j).collar_eq 0 (by norm_num) (side * (-eta)) htime',
      hTube, ht, hc, hScale, hSign]
    apply congrArg E.data.tube
    apply Prod.ext
    · rfl
    · change E.cutHeight + sigma * (a - E.scale) + beta * (side * (-eta)) =
        E.cutHeight + sigma * (a - E.scale - b * eta)
      dsimp only [b]
      calc
        _ = E.cutHeight + sigma * (a - E.scale) -
            (sigma * sigma) * (beta * side * eta) := by rw [hsigma]; ring
        _ = _ := by ring
  have hnegativeInside (eta : ℝ) (heta : 0 < eta) (hetaOne : eta < 1) :
      E.child j ((E.newCap j).flatChart 0, side * (-eta)) ∈ (A j).inside :=
    hin ⟨((E.newCap j).flatChart 0, -eta),
      ⟨mem_univ _, by linarith only [hetaOne], by linarith only [heta]⟩, rfl⟩
  have hbneg : b < 0 := by
    rcases lt_or_gt_of_ne hbnz with hneg | hpos
    · exact hneg
    · obtain ⟨eta, heta, hetaw, hetaOne, hetaR⟩ := htime (a - E.scale) hal
      have hz : a - E.scale - b * eta ∈ Ico (0 : ℝ) (a - E.scale) := by
        rw [abs_of_pos hpos] at hetaR
        exact ⟨by linarith only [hetaR],
          by linarith only [mul_pos hpos heta]⟩
      have hinside := hnegativeInside eta heta hetaOne
      rw [hflat eta heta hetaw] at hinside
      exact False.elim (haxis _ hz (image_mono ball_subset_closedBall hinside))
  obtain ⟨eta, heta, hetaw, hetaOne, hetaR⟩ := htime E.scale hl
  let r0 := 1 + b * eta / E.scale
  have hr0 : 0 < r0 ∧ r0 < 1 := by
    rw [abs_of_neg hbneg] at hetaR
    have hquot : -1 < b * eta / E.scale := (lt_div_iff₀ hl).mpr (by
      linarith only [hetaR])
    have hquotneg : b * eta / E.scale < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hbneg heta) hl
    exact ⟨by dsimp only [r0]; linarith only [hquot],
      by dsimp only [r0]; linarith only [hquotneg]⟩
  have hradius : a - E.scale * r0 = a - E.scale - b * eta := by
    dsimp only [r0]
    field_simp [hl.ne']
    ring
  have hmodelPoint : B.chart (r0 • (q0 : E3)) =
      E.data.tube (0, E.cutHeight + sigma * (a - E.scale - b * eta)) := by
    obtain ⟨_hf, _hi, _hq, hr⟩ :=
      nativeCapAmbientDiffeomorph_spec (E.child j) u (E.newCap j)
    change E.data.tube (D (r0 • (q0 : E3))) = _
    rw [hr r0, ht, hc, hScale, hSign, hradius]
  let Y := E.child j ((E.newCap j).flatChart 0, side * (-eta))
  have hYA : Y ∈ (A j).inside := hnegativeInside eta heta hetaOne
  have hYB : Y ∈ B.inside := by
    refine ⟨r0 • (q0 : E3), ?_, hmodelPoint.trans (hflat eta heta hetaw).symm⟩
    apply mem_ball_zero_iff.mpr
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0.1,
      mem_sphere_zero_iff_norm.mp q0.property, mul_one]
    exact hr0.2
  have hdis : Disjoint B.inside (A j).boundary := by
    rw [hboundary j]
    exact (E.canonicalCapBall_spec j).2.2.2.2.2.2.2.2.2.2.2.2.2
  have hinside : B.inside ⊆ (A j).inside := by
    rcases (A j).preconnected_subset_inside_or_outside B.inside_connected.isPreconnected
        hdis with hi | ho
    · exact hi
    · exact False.elim (ho hYB (image_mono ball_subset_closedBall hYA))
  refine ⟨i, hregions, hmid, side, hside, hin, hout, ?_, hinside, ?_⟩
  · change (E.newCap j).sign * beta * side < 0
    rw [hSign]
    exact hbneg
  · have hclosed := closure_mono hinside
    rw [B.closure_inside, (A j).closure_inside] at hclosed
    exact hclosed

end PoincareConjecture.M25.Topology3D
