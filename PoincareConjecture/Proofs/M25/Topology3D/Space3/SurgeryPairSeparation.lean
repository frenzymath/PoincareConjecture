import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryPairImage











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D.SurgeryCapProfile



theorem replacementMap_disjoint_pair (P : SurgeryCapProfile)
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (u : UnitTwoSphere) (t : ℝ) (D : RegularSurgeryData ψ u t)
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞) {delta r l : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hrdelta : 1 - r < delta)
    (hcwidth : D.width / 2 * (1 - r) < D.width)
    (hl : 0 < l) (hlM : l * P.heightBound < D.width / 2 * (1 - r) / 4)
    (hRball : R '' closedBall 0 1 = closedBall 0 r)
    (hR : ∀ x ∈ sphere (0 : E2) 1, R x = r • x)
    (hpos : ∀ x : E2, |‖x‖ - 1| < delta → x ∈ D.sourceDiscs.positive.source ∧
      D.sourceDiscs.positive x =
        D.sourceCollar (circleDirection x, D.width / 2 * (1 - ‖x‖)))
    (hneg : ∀ x : E2, |‖x‖ - 1| < delta → x ∈ D.sourceDiscs.negative.source ∧
      D.sourceDiscs.negative x =
        D.sourceCollar (circleDirection x, -(D.width / 2 * (1 - ‖x‖)))) :
    Disjoint
      (range (P.replacementMap ψ R D.sourceDiscs.positive D.tube t 1 r (D.width / 2) l))
      (range (P.replacementMap ψ R D.sourceDiscs.negative D.tube t (-1) r (D.width / 2) l)) := by
  have hk : 0 < D.width / 2 := by linarith [D.width_pos]
  let c := D.width / 2 * (1 - r)
  have hc : 0 < c := mul_pos hk (sub_pos.mpr hr1)
  have hcw : c < D.width := hcwidth
  have hpos' : ∀ x : E2, |‖x‖ - 1| < delta → x ∈ D.sourceDiscs.positive.source ∧
      D.sourceDiscs.positive x =
        D.sourceCollar (circleDirection x, 1 * (D.width / 2 * (1 - ‖x‖))) := by
    simpa only [one_mul] using hpos
  have hneg' : ∀ x : E2, |‖x‖ - 1| < delta → x ∈ D.sourceDiscs.negative.source ∧
      D.sourceDiscs.negative x =
        D.sourceCollar (circleDirection x, -1 * (D.width / 2 * (1 - ‖x‖))) := by
    simpa only [neg_one_mul] using hneg
  rw [P.replacementMap_range ψ u t D R D.sourceDiscs.positive 1 (by norm_num)
    hr hr1 hrdelta hk hcwidth hRball hR hpos',
    P.replacementMap_range ψ u t D R D.sourceDiscs.negative (-1) (by norm_num)
      hr hr1 hrdelta hk hcwidth hRball hR hneg']
  have hcentral : Function.Injective (fun p : UnitTwoSphere => ψ (p, 0)) := by
    intro p q hpq
    exact congrArg Prod.fst (hψ.2.1 (by simp) (by simp) hpq)
  have hretpos : D.sourceDiscs.positive '' closedBall 0 r ⊆
      D.sourceDiscs.positive '' ball 0 1 := image_mono (closedBall_subset_ball hr1)
  have hretneg : D.sourceDiscs.negative '' closedBall 0 r ⊆
      D.sourceDiscs.negative '' ball 0 1 := image_mono (closedBall_subset_ball hr1)
  have hdis := Set.disjoint_left.mp D.sourceDiscs.open_disjoint
  apply Set.disjoint_left.mpr
  intro z hzpos hzneg
  rcases hzpos with hretp | hcapp <;> rcases hzneg with hretn | hcapn
  · rcases hretp with ⟨p, hp, hpz⟩
    rcases hretn with ⟨q, hq, hqz⟩
    have heq := hcentral (hpz.trans hqz.symm)
    exact hdis (hretpos hp) (heq.symm ▸ hretneg hq)
  · rcases hretp with ⟨p, hp, hpz⟩
    rcases hcapn with ⟨q, hq, hqz⟩
    obtain ⟨theta, s, hs, hsc, hps⟩ := P.capMap_old_surface_source
      ψ hψ u t D (-1) (by norm_num) hc hcwidth hl hlM q hq p (hqz.trans hpz.symm)
    have hpn : p ∈ D.sourceDiscs.negative '' ball 0 1 := by
      rw [hps]
      apply D.sourceDiscs.negative_side
      exact ⟨(theta, -1 * s), ⟨mem_univ _, by dsimp; linarith [hcw],
        by dsimp; linarith [hcw]⟩, rfl⟩
    exact hdis (hretpos hp) hpn
  · rcases hcapp with ⟨q, hq, hqz⟩
    rcases hretn with ⟨p, hp, hpz⟩
    obtain ⟨theta, s, hs, hsc, hps⟩ := P.capMap_old_surface_source
      ψ hψ u t D 1 (by norm_num) hc hcwidth hl hlM q hq p (hqz.trans hpz.symm)
    have hpp : p ∈ D.sourceDiscs.positive '' ball 0 1 := by
      rw [hps]
      apply D.sourceDiscs.positive_side
      exact ⟨(theta, 1 * s), ⟨mem_univ _, by dsimp; linarith,
        by dsimp; linarith⟩, rfl⟩
    exact hdis hpp (hretneg hp)
  · rcases hcapp with ⟨p, hp, hpz⟩
    rcases hcapn with ⟨q, hq, hqz⟩
    have hheight (a : UnitTwoSphere) (ha : (heightCoordinates (a : E3)).2 ≤ 0) :
        0 < c + l * (P.model a).2 := by
      have hb := surgeryCapCoordinates_south_height_bounds
        P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
        (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
        P.vertical_pos t 1 c l P.heightBound (by norm_num) hl hlM a ha (P.height_bound a)
      rw [surgeryCapCoordinates_signed_height P.horizontal P.vertical
        P.horizontal_smooth P.vertical_smooth
        (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
        t 1 c l (by norm_num) a] at hb
      change 3 * c / 4 < c + l * (P.model a).2 ∧ _ at hb
      linarith [hb.1]
    have heq := congrArg (fun x : E3 => ⟪(u : E3), x⟫_ℝ) (hpz.trans hqz.symm)
    simp only [P.capMap_apply, D.tube_height, one_mul, neg_one_mul] at heq
    change t + (c + l * (P.model p).2) = t + -(c + l * (P.model q).2) at heq
    linarith [hheight p hp, hheight q hq]

end PoincareConjecture.M25.Topology3D.SurgeryCapProfile
