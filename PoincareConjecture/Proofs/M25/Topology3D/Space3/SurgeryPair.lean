import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryPairParameters
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryPairSeparation
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgerySmoothReplacement

set_option autoImplicit false

open Set Metric Filter Topology
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem exists_smooth_surgery_pair (P : SurgeryCapProfile)
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (u : UnitTwoSphere) (t : ℝ) (D : RegularSurgeryData ψ u t) :
    ∃ delta r l : ℝ, ∃ R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞,
      0 < delta ∧ 0 < r ∧ r < 1 ∧ 1 - r < delta ∧
      0 < D.width / 2 * (1 - r) ∧ D.width / 2 * (1 - r) < D.width ∧
      0 < l ∧ l * P.heightBound < D.width / 2 * (1 - r) / 4 ∧
      R '' ball 0 1 = ball 0 r ∧ R '' closedBall 0 1 = closedBall 0 r ∧
      (∀ x ∈ sphere (0 : E2) 1, R x = r • x) ∧
      (∀ᶠ x in 𝓝ˢ (sphere (0 : E2) 1),
        R x = surgeryMatchingRadius r (l / (D.width / 2)) ‖x‖ •
          NormedSpace.normalize x) ∧
      (∀ x : E2, |‖x‖ - 1| < delta → x ∈ D.sourceDiscs.positive.source ∧
        D.sourceDiscs.positive x =
          D.sourceCollar (circleDirection x, D.width / 2 * (1 - ‖x‖))) ∧
      (∀ x : E2, |‖x‖ - 1| < delta → x ∈ D.sourceDiscs.negative.source ∧
        D.sourceDiscs.negative x =
          D.sourceCollar (circleDirection x, -(D.width / 2 * (1 - ‖x‖)))) ∧
      let jp := P.replacementMap ψ R D.sourceDiscs.positive D.tube t 1 r (D.width / 2) l
      let jn := P.replacementMap ψ R D.sourceDiscs.negative D.tube t (-1) r (D.width / 2) l
      (ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ jp ∧
        (∀ q, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) jp q)) ∧
        IsClosedEmbedding jp) ∧
      (ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ jn ∧
        (∀ q, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) jn q)) ∧
        IsClosedEmbedding jn) ∧
      range jp = (fun p : UnitTwoSphere => ψ (p, 0)) ''
          (D.sourceDiscs.positive '' closedBall 0 r) ∪
        P.capMap D.tube t 1 (D.width / 2 * (1 - r)) l ''
          {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
      range jn = (fun p : UnitTwoSphere => ψ (p, 0)) ''
          (D.sourceDiscs.negative '' closedBall 0 r) ∪
        P.capMap D.tube t (-1) (D.width / 2 * (1 - r)) l ''
          {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
      Disjoint (range jp) (range jn) := by
  obtain ⟨delta, r, l, R, hd, hr, hr1, hrd, hc, hcw, hl, hlM,
    hRo, hRc, hRs, hRn, hpos, hneg⟩ := exists_surgery_pair_parameters P ψ u t D
  have hk : 0 < D.width / 2 := by linarith [D.width_pos]
  have hpos' : ∀ x : E2, |‖x‖ - 1| < delta → x ∈ D.sourceDiscs.positive.source ∧
      D.sourceDiscs.positive x =
        D.sourceCollar (circleDirection x, 1 * (D.width / 2 * (1 - ‖x‖))) := by
    simpa only [one_mul] using hpos
  have hneg' : ∀ x : E2, |‖x‖ - 1| < delta → x ∈ D.sourceDiscs.negative.source ∧
      D.sourceDiscs.negative x =
        D.sourceCollar (circleDirection x, -1 * (D.width / 2 * (1 - ‖x‖))) := by
    simpa only [neg_one_mul] using hneg
  refine ⟨delta, r, l, R, hd, hr, hr1, hrd, hc, hcw, hl, hlM,
    hRo, hRc, hRs, hRn, hpos, hneg, ?_, ?_, ?_, ?_, ?_⟩
  · exact surgeryReplacementMap_smooth_closedEmbedding
      P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
      P.horizontal_pos P.horizontal_bound P.vertical_pos P.horizontal_near P.vertical_far
      ψ hψ u t D R D.sourceDiscs.positive D.sourceDiscs.positive_source
      D.sourceDiscs.positive_smooth D.sourceDiscs.positive_inverse
      1 (by norm_num) hr hr1 hrd hk hcw hRc hRs hRn hpos' hl hlM P.height_bound
  · exact surgeryReplacementMap_smooth_closedEmbedding
      P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
      P.horizontal_pos P.horizontal_bound P.vertical_pos P.horizontal_near P.vertical_far
      ψ hψ u t D R D.sourceDiscs.negative D.sourceDiscs.negative_source
      D.sourceDiscs.negative_smooth D.sourceDiscs.negative_inverse
      (-1) (by norm_num) hr hr1 hrd hk hcw hRc hRs hRn hneg' hl hlM P.height_bound
  · exact P.replacementMap_range ψ u t D R D.sourceDiscs.positive 1 (by norm_num)
      hr hr1 hrd hk hcw hRc hRs hpos'
  · exact P.replacementMap_range ψ u t D R D.sourceDiscs.negative (-1) (by norm_num)
      hr hr1 hrd hk hcw hRc hRs hneg'
  · exact P.replacementMap_disjoint_pair ψ hψ u t D R
      hr hr1 hrd hcw hl hlM hRc hRs hpos hneg

end PoincareConjecture.M25.Topology3D
