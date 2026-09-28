import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularSurgeryData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryMatchingProfile
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryNeighborhood











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D



theorem exists_surgery_pair_parameters (P : SurgeryCapProfile)
    (ψ : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere) (t : ℝ)
    (D : RegularSurgeryData ψ u t) :
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
          D.sourceCollar (circleDirection x, -(D.width / 2 * (1 - ‖x‖)))) := by
  obtain ⟨dp, hdp, hp⟩ := exists_circle_radial_band D.sourceDiscs.positive_near
  obtain ⟨dn, hdn, hn⟩ := exists_circle_radial_band D.sourceDiscs.negative_near
  let delta := min dp dn
  have hd : 0 < delta := lt_min hdp hdn
  let epsilon := min (delta / 2) (1 / 4)
  have he : 0 < epsilon := lt_min (by positivity) (by norm_num)
  have hed : epsilon < delta := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hequarter : epsilon ≤ 1 / 4 := min_le_right _ _
  let r := 1 - epsilon
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hrd : 1 - r < delta := by dsimp [r]; linarith
  have hk : 0 < D.width / 2 := by linarith [D.width_pos]
  let c := D.width / 2 * (1 - r)
  have hc : 0 < c := mul_pos hk (sub_pos.mpr hr1)
  have hcw : c < D.width := by
    have h := mul_lt_mul_of_pos_left (show 1 - r < 2 by linarith) hk
    dsimp [c]
    linarith
  have hM : 0 < P.heightBound := lt_of_lt_of_le zero_lt_one P.one_le_heightBound
  let l := c / (8 * P.heightBound)
  have hl : 0 < l := div_pos hc (by positivity)
  have hlM : l * P.heightBound = c / 8 := by
    dsimp [l]
    field_simp [hM.ne']
  have hsmall : l * P.heightBound < c / 4 := by rw [hlM]; linarith
  obtain ⟨R, hRo, hRc, hRs, hRn⟩ := exists_surgery_matching_diffeomorph
    (E := E2) hr (div_pos hl hk)
  refine ⟨delta, r, l, R, hd, hr, hr1, hrd, hc, hcw, hl, hsmall,
    hRo, hRc, hRs, hRn, ?_, ?_⟩
  · intro x hx
    exact hp x (lt_of_lt_of_le hx (min_le_left _ _))
  · intro x hx
    exact hn x (lt_of_lt_of_le hx (min_le_right _ _))

end PoincareConjecture.M25.Topology3D
