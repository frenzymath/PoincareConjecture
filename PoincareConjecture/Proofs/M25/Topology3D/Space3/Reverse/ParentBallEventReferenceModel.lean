import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryEventRegions
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallNativeCapRadial
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem SurgeryCapProfile.closedBall_model_bounds
    (P : SurgeryCapProfile) :
    let G := heightCoordinates.toDiffeomorph.trans
      (flatCapDiffeomorph P.horizontal P.vertical
        P.horizontal_smooth P.vertical_smooth
        (fun z => (P.horizontal_pos z).ne')
        (fun x => (P.vertical_pos x).ne'))
    (∀ y ∈ closedBall (0 : E3) 1,
      ‖(G y).1‖ ≤ 1 ∧ |(G y).2| ≤ P.heightBound) ∧
      ∀ y ∈ ball (0 : E3) 1, ‖(G y).1‖ < 1 := by
  let G := heightCoordinates.toDiffeomorph.trans
    (flatCapDiffeomorph P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne')
      (fun x => (P.vertical_pos x).ne'))
  let K := G '' closedBall (0 : E3) 1
  let O := G '' ball (0 : E3) 1
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : E3) 1).image G.contMDiff_toFun.continuous
  have hKne : K.Nonempty := ⟨G 0, 0, by simp, rfl⟩
  have hO : IsOpen O := G.toHomeomorph.isOpenMap _ isOpen_ball
  have hOK : O ⊆ K := image_mono ball_subset_closedBall
  have hshift (p : E2 × ℝ) (s : ℝ) : dist (p.1, p.2 + s) p = |s| := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq]
    have heq : p.2 + s - p.2 = s := by ring
    rw [heq, max_eq_right (abs_nonneg s)]
  obtain ⟨pmax, hpmax, hmax⟩ := hK.exists_isMaxOn hKne continuous_snd.continuousOn
  obtain ⟨pmin, hpmin, hmin⟩ := hK.exists_isMinOn hKne continuous_snd.continuousOn
  have hmaxOutside : pmax ∉ O := by
    intro hp
    obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hO pmax hp
    have hnear : (pmax.1, pmax.2 + eps / 2) ∈ ball pmax eps := by
      rw [mem_ball, hshift, abs_of_pos (div_pos heps (by norm_num))]
      linarith only [heps]
    have hle := hmax (hOK (hball hnear))
    change pmax.2 + eps / 2 ≤ pmax.2 at hle
    linarith only [heps, hle]
  have hminOutside : pmin ∉ O := by
    intro hp
    obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hO pmin hp
    have hnear : (pmin.1, pmin.2 + (-eps / 2)) ∈ ball pmin eps := by
      rw [mem_ball, hshift, abs_of_neg (by linarith only [heps] : -eps / 2 < 0)]
      linarith only [heps]
    have hle := hmin (hOK (hball hnear))
    change pmin.2 ≤ pmin.2 + (-eps / 2) at hle
    linarith only [heps, hle]
  have hboundaryBound (p : E2 × ℝ) (hp : p ∈ K) (hout : p ∉ O) :
      |p.2| ≤ P.heightBound := by
    obtain ⟨y, hy, rfl⟩ := hp
    have hynorm : ‖y‖ = 1 := by
      apply le_antisymm (mem_closedBall_zero_iff.mp hy)
      by_contra hn
      exact hout ⟨y, mem_ball_zero_iff.mpr (lt_of_not_ge hn), rfl⟩
    let q : UnitTwoSphere := ⟨y, mem_sphere_zero_iff_norm.mpr hynorm⟩
    exact P.height_bound q
  have hupper := (abs_le.mp (hboundaryBound pmax hpmax hmaxOutside)).2
  have hlower := (abs_le.mp (hboundaryBound pmin hpmin hminOutside)).1
  constructor
  · intro y hy
    have hsq : ‖(heightCoordinates y).1‖ ^ 2 + (heightCoordinates y).2 ^ 2 ≤ 1 := by
      rw [← heightCoordinates_norm_sq]
      nlinarith only [mem_closedBall_zero_iff.mp hy, norm_nonneg y]
    refine ⟨flatCapDiffeomorph_fst_norm_le P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
      P.horizontal_pos P.horizontal_bound (heightCoordinates y) hsq, ?_⟩
    exact abs_le.mpr ⟨hlower.trans (hmin ⟨y, hy, rfl⟩),
      (hmax ⟨y, hy, rfl⟩).trans hupper⟩
  · intro y hy
    let p := heightCoordinates y
    have hsq : ‖p.1‖ ^ 2 + p.2 ^ 2 < 1 := by
      rw [← heightCoordinates_norm_sq]
      nlinarith only [mem_ball_zero_iff.mp hy, norm_nonneg y]
    have hz : |p.2| < 1 := by
      nlinarith only [hsq, sq_abs p.2, abs_nonneg p.2, sq_nonneg ‖p.1‖]
    have hrad : 0 < 1 - p.2 ^ 2 := by linarith only [hsq, sq_nonneg ‖p.1‖]
    have hs : 0 < Real.sqrt (1 - p.2 ^ 2) := Real.sqrt_pos.mpr hrad
    have hx : ‖p.1‖ < Real.sqrt (1 - p.2 ^ 2) := by
      nlinarith only [Real.sq_sqrt hrad.le, hsq, norm_nonneg p.1, hs]
    change ‖P.horizontal p.2 • p.1‖ < 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (P.horizontal_pos p.2)]
    calc
      P.horizontal p.2 * ‖p.1‖ <
          P.horizontal p.2 * Real.sqrt (1 - p.2 ^ 2) :=
        mul_lt_mul_of_pos_left hx (P.horizontal_pos p.2)
      _ ≤ (Real.sqrt (1 - p.2 ^ 2))⁻¹ * Real.sqrt (1 - p.2 ^ 2) :=
        mul_le_mul_of_nonneg_right (P.horizontal_bound p.2 hz) hs.le
      _ = 1 := inv_mul_cancel₀ hs.ne'

noncomputable def RegularSurgeryEvent.canonicalCapBall
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (j : Fin 2) :
    BallNeighborhoodChart E3 E3 := by
  let D := nativeCapAmbientDiffeomorph (E.child j) u (E.newCap j)
  refine {
    chart := D.toHomeomorph.toOpenPartialHomeomorph.trans E.data.tube
    closedBall_subset_source := ?_
    smooth := E.data.tube_smooth.comp D.contMDiff_toFun.contDiff.contDiffOn
      (fun _ hp => hp.2)
    smooth_symm := D.contMDiff_invFun.contDiff.comp_contDiffOn
      (E.data.tube_inverse.mono (fun _ hy => hy.1)) }
  intro y hy
  have hbound := ((E.newCap j).profile.closedBall_model_bounds).1 y hy
  have hfirst : ‖(D y).1‖ ≤ 1 := hbound.1
  exact ⟨mem_univ _, E.data.tube_source
    ⟨mem_closedBall_zero_iff.mpr hfirst, mem_univ _⟩⟩

theorem RegularSurgeryEvent.canonicalCapBall_spec
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (j : Fin 2) :
    let a := E.data.width / 2 * (1 - E.radius)
    let sigma : ℝ := ![1, -1] j
    let D := nativeCapAmbientDiffeomorph (E.child j) u (E.newCap j)
    let B := E.canonicalCapBall j
    let south := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    let north := {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
    let N := E.profile.capMap E.data.tube E.cutHeight sigma a E.scale '' north
    B.chart = D.toHomeomorph.toOpenPartialHomeomorph.trans E.data.tube ∧
      B.chart.source = D ⁻¹' E.data.tube.source ∧
      B.chart.target = E.data.tube.target ∧
      (∀ y : E3, B.chart y = E.data.tube (D y)) ∧
      (∀ Y : E3, B.chart.symm Y = D.symm (E.data.tube.symm Y)) ∧
      (∀ q : UnitTwoSphere, B.chart (q : E3) =
        E.profile.capMap E.data.tube E.cutHeight sigma a E.scale q) ∧
      (fun q : UnitTwoSphere => B.chart (q : E3)) '' south = (E.newCap j).cap ∧
      (fun q : UnitTwoSphere => B.chart (q : E3)) '' north = N ∧
      B.boundary = (E.newCap j).cap ∪ N ∧
      (E.newCap j).cap ∩ N = (E.newCap j).seam ∧
      B.closedRegion ⊆ E.data.tube ''
        (closedBall (0 : E2) 1 ×ˢ
          Icc (E.cutHeight - (a + E.scale * E.profile.heightBound))
            (E.cutHeight + (a + E.scale * E.profile.heightBound))) ∧
      B.inside ⊆ E.data.tube ''
        (ball (0 : E2) 1 ×ˢ
          Ioo (E.cutHeight - E.data.width) (E.cutHeight + E.data.width)) ∧
      Disjoint B.inside (parent '' (univ ×ˢ ({0} : Set ℝ))) ∧
      Disjoint B.inside (E.child j '' (univ ×ˢ ({0} : Set ℝ))) := by
  let a := E.data.width / 2 * (1 - E.radius)
  let sigma : ℝ := ![1, -1] j
  let D := nativeCapAmbientDiffeomorph (E.child j) u (E.newCap j)
  let B := E.canonicalCapBall j
  let south := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let north := {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
  let N := E.profile.capMap E.data.tube E.cutHeight sigma a E.scale '' north
  let G := heightCoordinates.toDiffeomorph.trans
    (flatCapDiffeomorph E.profile.horizontal E.profile.vertical
      E.profile.horizontal_smooth E.profile.vertical_smooth
      (fun z => (E.profile.horizontal_pos z).ne')
      (fun x => (E.profile.vertical_pos x).ne'))
  obtain ⟨hP, hT, ht, hc, hlambda, hs⟩ := E.newCap_spec j
  obtain ⟨hDformula, _hDinv, hDsphere, _hDray⟩ :=
    nativeCapAmbientDiffeomorph_spec (E.child j) u (E.newCap j)
  obtain ⟨_hd, ha, hak, _hkd, hl, hsmall⟩ := E.parameter_bounds
  change 0 < a at ha
  change a < E.data.width / 2 at hak
  change E.scale * E.profile.heightBound < a / 4 at hsmall
  have habs : |sigma| = 1 := by fin_cases j <;> norm_num [sigma]
  have hband : a + E.scale * E.profile.heightBound < E.data.width := by
    linarith only [hsmall, hak, E.data.width_pos]
  have hD (y : E3) : D y = ((G y).1,
      E.cutHeight + sigma * (a + E.scale * (G y).2)) := by
    have h := hDformula y
    simp only [hP, ht, hc, hlambda, hs] at h
    exact h
  have hq (q : UnitTwoSphere) : B.chart (q : E3) =
      E.profile.capMap E.data.tube E.cutHeight sigma a E.scale q := by
    have h := (hDsphere q).2
    rw [hT, hP, ht, hc, hlambda, hs] at h
    exact h
  have hsouth : (fun q : UnitTwoSphere => B.chart (q : E3)) '' south =
      (E.newCap j).cap := by
    rw [(E.newCap j).cap_eq_image, hP, hT, ht, hc, hlambda, hs]
    exact image_congr (fun q _ => hq q)
  have hnorth : (fun q : UnitTwoSphere => B.chart (q : E3)) '' north = N :=
    image_congr (fun q _ => hq q)
  have hseam : (E.newCap j).seam =
      (fun q : UnitTwoSphere => B.chart (q : E3)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 = 0} := by
    rw [(E.newCap j).seam_eq_image, hP, hT, ht, hc, hlambda, hs]
    exact image_congr (fun q _ => (hq q).symm)
  have hboundary : B.boundary = (E.newCap j).cap ∪ N := by
    rw [← hsouth, ← hnorth]
    ext Y
    constructor
    · rintro ⟨y, hy, rfl⟩
      let q : UnitTwoSphere := ⟨y, hy⟩
      rcases le_total (heightCoordinates y).2 0 with h | h
      · exact Or.inl ⟨q, h, rfl⟩
      · exact Or.inr ⟨q, h, rfl⟩
    · rintro (⟨q, _hq, rfl⟩ | ⟨q, _hq, rfl⟩)
      · exact ⟨(q : E3), q.property, rfl⟩
      · exact ⟨(q : E3), q.property, rfl⟩
  have hinter : (E.newCap j).cap ∩ N = (E.newCap j).seam := by
    rw [← hsouth, ← hnorth, hseam]
    ext Y
    constructor
    · rintro ⟨⟨q, hqs, hqY⟩, ⟨r, hrn, hrY⟩⟩
      have hqr : q = r := Subtype.ext (B.chart.injOn
        (B.closedBall_subset_source (sphere_subset_closedBall q.property))
        (B.closedBall_subset_source (sphere_subset_closedBall r.property))
        (hqY.trans hrY.symm))
      subst r
      exact ⟨q, le_antisymm hqs hrn, hqY⟩
    · rintro ⟨q, hqzero, rfl⟩
      exact ⟨⟨q, hqzero.le, rfl⟩, ⟨q, hqzero.symm.le, rfl⟩⟩
  have hsolid (y : E3) (hy : y ∈ closedBall (0 : E3) 1) :
      ‖(D y).1‖ ≤ 1 ∧
        |(D y).2 - E.cutHeight| ≤ a + E.scale * E.profile.heightBound := by
    have hb := E.profile.closedBall_model_bounds.1 y hy
    rw [hD]
    refine ⟨hb.1, ?_⟩
    simp only [add_sub_cancel_left]
    calc
      |sigma * (a + E.scale * (G y).2)| = |a + E.scale * (G y).2| := by
        rw [abs_mul, habs, one_mul]
      _ ≤ |a| + |E.scale * (G y).2| := abs_add_le _ _
      _ = a + E.scale * |(G y).2| := by
        rw [abs_of_pos ha, abs_mul, abs_of_pos hl]
      _ ≤ a + E.scale * E.profile.heightBound :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hb.2 hl.le)
  have hclosed : B.closedRegion ⊆ E.data.tube ''
      (closedBall (0 : E2) 1 ×ˢ
        Icc (E.cutHeight - (a + E.scale * E.profile.heightBound))
          (E.cutHeight + (a + E.scale * E.profile.heightBound))) := by
    rintro Y ⟨y, hy, rfl⟩
    obtain ⟨hx, hz⟩ := hsolid y hy
    obtain ⟨hlo, hhi⟩ := abs_le.mp hz
    exact ⟨D y, ⟨mem_closedBall_zero_iff.mpr hx,
      by linarith only [hlo], by linarith only [hhi]⟩, rfl⟩
  have hinside : B.inside ⊆ E.data.tube ''
      (ball (0 : E2) 1 ×ˢ
        Ioo (E.cutHeight - E.data.width) (E.cutHeight + E.data.width)) := by
    rintro Y ⟨y, hy, rfl⟩
    have hx : ‖(D y).1‖ < 1 := by
      rw [hD]
      exact E.profile.closedBall_model_bounds.2 y hy
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hsolid y (ball_subset_closedBall hy)).2
    exact ⟨D y, ⟨mem_ball_zero_iff.mpr hx,
      by linarith only [hlo, hband], by linarith only [hhi, hband]⟩, rfl⟩
  have hparent : Disjoint B.inside (parent '' (univ ×ˢ ({0} : Set ℝ))) := by
    apply disjoint_left.mpr
    rintro Y hY ⟨⟨q, s⟩, hqs, hqY⟩
    have hs0 : s = 0 := hqs.2
    subst s
    obtain ⟨p, hp, hpY⟩ := hinside hY
    have hcircle := (E.data.surface_mem p.1 (ball_subset_closedBall hp.1) p.2 hp.2).mp
      ⟨q, hqY.trans hpY.symm⟩
    exact (ne_of_lt (mem_ball_zero_iff.mp hp.1)) (mem_sphere_zero_iff_norm.mp hcircle)
  have hchild : Disjoint B.inside (E.child j '' (univ ×ˢ ({0} : Set ℝ))) := by
    obtain ⟨_hparent, _hcoreAnn, _hcores, hcover, _hinter, _hchildren⟩ := E.region_identities
    apply disjoint_left.mpr
    intro Y hY hchildY
    rw [hcover j] at hchildY
    rcases hchildY with hcore | hcap
    · obtain ⟨q, _hq, hqY⟩ := hcore
      exact disjoint_left.mp hparent hY ⟨(q, 0), ⟨mem_univ _, rfl⟩, hqY⟩
    · exact disjoint_left.mp B.inside_disjoint_boundary hY
        (hboundary.symm ▸ Or.inl hcap)
  refine ⟨rfl, ?_, ?_, fun _ => rfl, fun _ => rfl, hq, hsouth, hnorth,
    hboundary, hinter, hclosed, hinside, hparent, hchild⟩
  · ext y
    change (y ∈ (univ : Set E3) ∧ D y ∈ E.data.tube.source) ↔
      D y ∈ E.data.tube.source
    simp only [mem_univ, true_and]
  · ext Y
    change (Y ∈ E.data.tube.target ∧
      E.data.tube.symm Y ∈ (univ : Set (E2 × ℝ))) ↔ _
    simp only [mem_univ, and_true]

end PoincareConjecture.M25.Topology3D
