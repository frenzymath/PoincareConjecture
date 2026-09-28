import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularSurgeryData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryPairImage
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapIntersection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.NorthSphereCoordinates










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem surgery_parent_region_identities
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (t : ℝ) (D : RegularSurgeryData psi u t)
    {delta r : ℝ} (hr : 0 < r) (hr1 : r < 1) (hrdelta : 1 - r < delta)
    (hnear : ∀ (i : Fin 2) (x : E2), |‖x‖ - 1| < delta →
      x ∈ (![D.sourceDiscs.positive, D.sourceDiscs.negative] i).source ∧
        (![D.sourceDiscs.positive, D.sourceDiscs.negative] i) x =
          D.sourceCollar (circleDirection x,
            (![1, -1] i) * (D.width / 2 * (1 - ‖x‖)))) :
    let c := D.width / 2 * (1 - r)
    let core : Fin 2 → Set E3 := fun i =>
      (fun p : UnitTwoSphere => psi (p, 0)) ''
        ((![D.sourceDiscs.positive, D.sourceDiscs.negative] i) ''
          closedBall (0 : E2) r)
    let annulus := D.tube '' (sphere (0 : E2) 1 ×ˢ Ioo (t - c) (t + c))
    range (fun p : UnitTwoSphere => psi (p, 0)) =
      core 0 ∪ core 1 ∪ annulus ∧
      (∀ i : Fin 2, Disjoint (core i) annulus) ∧
      Disjoint (core 0) (core 1) := by
  let k : ℝ := D.width / 2
  let c : ℝ := k * (1 - r)
  let e : Fin 2 → OpenPartialHomeomorph E2 UnitTwoSphere :=
    ![D.sourceDiscs.positive, D.sourceDiscs.negative]
  let sigma : Fin 2 → ℝ := ![1, -1]
  let K : Fin 2 → Set UnitTwoSphere := fun i => e i '' closedBall (0 : E2) r
  let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
  let annulus := D.tube '' (sphere (0 : E2) 1 ×ˢ Ioo (t - c) (t + c))
  change range j = j '' K 0 ∪ j '' K 1 ∪ annulus ∧
    (∀ i : Fin 2, Disjoint (j '' K i) annulus) ∧ Disjoint (j '' K 0) (j '' K 1)
  have hk : 0 < k := div_pos D.width_pos (by norm_num)
  have hc : 0 < c := mul_pos hk (sub_pos.mpr hr1)
  have hck : c < k := by dsimp only [c]; nlinarith
  have hcwidth : c < D.width := hck.trans (by dsimp only [k]; linarith [D.width_pos])
  have hcentral : Function.Injective j := by
    intro p q hpq
    exact congrArg Prod.fst (hpsi.2.1 (by simp) (by simp) hpq)
  have hsigma (i : Fin 2) : |sigma i| = 1 := by fin_cases i <;> norm_num [sigma]
  have hnear' (i : Fin 2) (x : E2) (hx : |‖x‖ - 1| < delta) :
      x ∈ (e i).source ∧ e i x =
        D.sourceCollar (circleDirection x, sigma i * (k * (1 - ‖x‖))) := hnear i x hx
  have hsmall : closedBall (0 : E2) r ⊆ ball 0 1 := fun x hx =>
    mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx).trans_lt hr1)
  have hKdisjoint : Disjoint (K 0) (K 1) :=
    D.sourceDiscs.open_disjoint.mono (image_mono hsmall) (image_mono hsmall)
  have hexclude (i : Fin 2) (theta : UnitCircle) (s : ℝ) (hs : |s| < c) :
      D.sourceCollar (theta, s) ∉ K i := by
    have hsband := abs_lt.mp (hs.trans hcwidth)
    have hsc := abs_lt.mp hs
    fin_cases i
    · intro hmem
      change D.sourceCollar (theta, s) ∈
        D.sourceDiscs.positive '' closedBall (0 : E2) r at hmem
      by_cases hs0 : 0 ≤ s
      · have heq : s = c :=
          (sourceDisc_collar_mem_retained_iff D.sourceDiscs.positive
            D.sourceDiscs.positive_source D.sourceCollar 1 hr hr1 hrdelta hk
            (hnear' 0) theta hs0 hsc.2.le).mp (by simpa only [one_mul] using hmem)
        exact hsc.2.ne heq
      · have hneg := D.sourceDiscs.negative_side
          (show D.sourceCollar (theta, s) ∈
            D.sourceCollar '' (univ ×ˢ Ioo (-D.width) 0) from
              ⟨(theta, s), ⟨mem_univ _, hsband.1, lt_of_not_ge hs0⟩, rfl⟩)
        exact disjoint_left.mp D.sourceDiscs.open_disjoint (image_mono hsmall hmem) hneg
    · intro hmem
      change D.sourceCollar (theta, s) ∈
        D.sourceDiscs.negative '' closedBall (0 : E2) r at hmem
      by_cases hs0 : s ≤ 0
      · have heq : -s = c :=
          (sourceDisc_collar_mem_retained_iff D.sourceDiscs.negative
            D.sourceDiscs.negative_source D.sourceCollar (-1) hr hr1 hrdelta hk
            (hnear' 1) theta (neg_nonneg.mpr hs0) (by linarith only [hsc.1])).mp
              (by simpa only [neg_mul, one_mul, neg_neg] using hmem)
        linarith only [heq, hsc.1]
      · have hpos := D.sourceDiscs.positive_side
          (show D.sourceCollar (theta, s) ∈
            D.sourceCollar '' (univ ×ˢ Ioo 0 D.width) from
              ⟨(theta, s), ⟨mem_univ _, lt_of_not_ge hs0, hsband.2⟩, rfl⟩)
        exact disjoint_left.mp D.sourceDiscs.open_disjoint hpos (image_mono hsmall hmem)
  have hreconstruct (x : E2) (hx : x ∈ sphere (0 : E2) 1)
      (z : ℝ) (hz : z ∈ Ioo (t - c) (t + c)) :
      j (D.sourceCollar (⟨x, hx⟩, z - t)) = D.tube (x, z) := by
    have hs : z - t ∈ Ioo (-D.width) D.width :=
      ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hzt : t + (z - t) = z := by ring
    simpa only [hzt] using D.reconstruction ⟨x, hx⟩ (z - t) hs
  refine ⟨?_, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨p, rfl⟩
      have hp : p ∈ D.sourceDiscs.positive '' closedBall (0 : E2) 1 ∪
          D.sourceDiscs.negative '' closedBall (0 : E2) 1 := by
        rw [D.sourceDiscs.closed_cover]
        exact mem_univ _
      have hex : ∃ i : Fin 2, p ∈ e i '' closedBall (0 : E2) 1 :=
        hp.elim (fun h => ⟨0, h⟩) (fun h => ⟨1, h⟩)
      obtain ⟨i, x, hx, rfl⟩ := hex
      have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
      by_cases hxr : ‖x‖ ≤ r
      · have hi : j (e i x) ∈ j '' K i :=
          ⟨e i x, ⟨x, mem_closedBall_zero_iff.mpr hxr, rfl⟩, rfl⟩
        fin_cases i
        · exact Or.inl (Or.inl hi)
        · exact Or.inl (Or.inr hi)
      · have hrx : r < ‖x‖ := lt_of_not_ge hxr
        have hwindow : |‖x‖ - 1| < delta := by
          rw [abs_of_nonpos (sub_nonpos.mpr hx1)]
          linarith
        have hstime : |sigma i * (k * (1 - ‖x‖))| < c := by
          rw [abs_mul, hsigma i, one_mul,
            abs_of_nonneg (mul_nonneg hk.le (sub_nonneg.mpr hx1))]
          dsimp only [c]
          nlinarith
        have hst := abs_lt.mp hstime
        right
        refine ⟨((circleDirection x : E2), t + sigma i * (k * (1 - ‖x‖))),
          ⟨(circleDirection x).property, by constructor <;> linarith only [hst.1, hst.2]⟩,
          ?_⟩
        exact (D.reconstruction (circleDirection x) _
          (abs_lt.mp (hstime.trans hcwidth))).symm.trans
            (congrArg j (hnear' i x hwindow).2).symm
    · rintro y ((hy | hy) | hy)
      · obtain ⟨p, _, rfl⟩ := hy
        exact ⟨p, rfl⟩
      · obtain ⟨p, _, rfl⟩ := hy
        exact ⟨p, rfl⟩
      · obtain ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩ := hy
        exact ⟨D.sourceCollar (⟨x, hx⟩, z - t), hreconstruct x hx z hz⟩
  · intro i
    apply disjoint_left.mpr
    rintro y ⟨p, hp, hpy⟩ ⟨⟨x, z⟩, ⟨hx, hz⟩, hxy⟩
    have heq : p = D.sourceCollar (⟨x, hx⟩, z - t) :=
      hcentral (hpy.trans (hxy.symm.trans (hreconstruct x hx z hz).symm))
    apply hexclude i ⟨x, hx⟩ (z - t)
      (abs_lt.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩)
    exact heq ▸ hp
  · apply disjoint_left.mpr
    rintro y ⟨p, hp, hpy⟩ ⟨q, hq, hqy⟩
    have hpq : p = q := hcentral (hpy.trans hqy.symm)
    subst q
    exact disjoint_left.mp hKdisjoint hp hq


theorem surgery_cap_equator_image (P : SurgeryCapProfile)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (t sigma c l : ℝ) :
    P.capMap T t sigma c l ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 = 0} =
        T '' (sphere (0 : E2) 1 ×ˢ ({t + sigma * c} : Set ℝ)) := by
  have hformula (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 = 0) :
      P.capMap T t sigma c l q =
        T ((circleDirection (heightCoordinates (q : E3)).1 : E2), t + sigma * c) := by
    change surgeryCapMap P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
      T t sigma c l q = _
    rw [surgeryCapMap, surgeryCapCoordinates_cylinder
      P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
      P.horizontal_near P.vertical_far t sigma c l q (by rw [hq]; norm_num),
      hq, mul_zero, add_zero]
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [hformula q hq]
    exact ⟨((circleDirection (heightCoordinates (q : E3)).1 : E2), t + sigma * c),
      ⟨(circleDirection (heightCoordinates (q : E3)).1).property, rfl⟩, rfl⟩
  · rintro ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
    have hz' : z = t + sigma * c := hz
    subst z
    let theta : UnitCircle := ⟨x, hx⟩
    have hcoords := northSpherePoint_equator theta
    have hzero : (heightCoordinates (northSpherePoint x : E3)).2 = 0 :=
      congrArg Prod.snd hcoords
    refine ⟨northSpherePoint x, hzero, ?_⟩
    rw [hformula _ hzero, hcoords]
    change T ((circleDirection (theta : E2) : E2), t + sigma * c) = _
    rw [circleDirection_coe_unit]


theorem surgery_retained_cap_intersection (P : SurgeryCapProfile)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (t : ℝ) (D : RegularSurgeryData psi u t)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : closedBall 0 1 ⊆ e.source)
    (sigma : ℝ) (hsigma : |sigma| = 1) {delta r k l : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hrdelta : 1 - r < delta) (hk : 0 < k)
    (hcwidth : k * (1 - r) < D.width)
    (hnear : ∀ x : E2, |‖x‖ - 1| < delta →
      x ∈ e.source ∧ e x = D.sourceCollar
        (circleDirection x, sigma * (k * (1 - ‖x‖))))
    (hl : 0 < l) (hlM : l * P.heightBound < k * (1 - r) / 4) :
    ((fun p : UnitTwoSphere => psi (p, 0)) '' (e '' closedBall 0 r)) ∩
      (P.capMap D.tube t sigma (k * (1 - r)) l ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}) =
      D.tube ''
        (sphere (0 : E2) 1 ×ˢ ({t + sigma * (k * (1 - r))} : Set ℝ)) := by
  have hiff (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 ≤ 0) :
      P.capMap D.tube t sigma (k * (1 - r)) l q ∈
          (fun p : UnitTwoSphere => psi (p, 0)) '' (e '' closedBall 0 r) ↔
        (heightCoordinates (q : E3)).2 = 0 :=
    surgeryCapMap_mem_retained_iff P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
      P.horizontal_pos P.horizontal_bound P.vertical_pos P.horizontal_near P.vertical_far
      psi hpsi u t D e he sigma hsigma hr hr1 hrdelta hk hcwidth hnear hl hlM q hq
      (P.height_bound q)
  rw [← surgery_cap_equator_image P D.tube t sigma (k * (1 - r)) l]
  ext y
  constructor
  · rintro ⟨hy, q, hq, rfl⟩
    exact ⟨q, (hiff q hq).mp hy, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨(hiff q hq.le).mpr hq, ⟨q, hq.le, rfl⟩⟩

end PoincareConjecture.M25.Topology3D
