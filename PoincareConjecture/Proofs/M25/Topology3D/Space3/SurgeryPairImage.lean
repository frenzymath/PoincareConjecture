import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryReplacement

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D.SurgeryCapProfile

noncomputable def replacementMap (P : SurgeryCapProfile)
    (ψ : UnitTwoSphere × ℝ → E3)
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3) (t sigma r k l : ℝ) :
    UnitTwoSphere → E3 :=
  surgeryReplacementMap P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
    ψ R e T t sigma r k l

theorem replacementMap_range (P : SurgeryCapProfile)
    (ψ : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere) (t : ℝ)
    (D : RegularSurgeryData ψ u t)
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (sigma : ℝ) (hsigma : |sigma| = 1) {delta r k l : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hrdelta : 1 - r < delta) (hk : 0 < k)
    (hcwidth : k * (1 - r) < D.width)
    (hRball : R '' closedBall 0 1 = closedBall 0 r)
    (hR : ∀ x ∈ sphere (0 : E2) 1, R x = r • x)
    (hnear : ∀ x : E2, |‖x‖ - 1| < delta →
      x ∈ e.source ∧ e x = D.sourceCollar
        (circleDirection x, sigma * (k * (1 - ‖x‖)))) :
    range (P.replacementMap ψ R e D.tube t sigma r k l) =
      (fun p : UnitTwoSphere => ψ (p, 0)) '' (e '' closedBall 0 r) ∪
      P.capMap D.tube t sigma (k * (1 - r)) l ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} := by
  let height : UnitTwoSphere → ℝ := fun q => (heightCoordinates (q : E3)).2
  let f : UnitTwoSphere → E3 := fun q => ψ (surgeryNorthChart R e q, 0)
  let g := P.capMap D.tube t sigma (k * (1 - r)) l
  have hjoin : sigma * (k * (1 - r)) ∈ Ioo (-D.width) D.width := by
    apply abs_lt.mp
    rw [abs_mul, hsigma, one_mul, abs_of_pos (mul_pos hk (sub_pos.mpr hr1))]
    exact hcwidth
  have heq (q : UnitTwoSphere) (hq : height q = 0) : f q = g q := by
    change ψ (surgeryNorthChart R e q, 0) =
      surgeryCapMap P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
        (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
        D.tube t sigma (k * (1 - r)) l q
    rw [surgeryNorthChart_equator_formula R e D.sourceCollar sigma k
      hr hr1 hrdelta hR hnear q hq, D.reconstruction _ _ hjoin, surgeryCapMap,
      surgeryCapCoordinates_cylinder P.horizontal P.vertical
        P.horizontal_smooth P.vertical_smooth
        (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
        P.horizontal_near P.vertical_far t sigma (k * (1 - r)) l q
        (by change |height q| ≤ 1 / 4; rw [hq]; norm_num)]
    change D.tube (_, t + sigma * (k * (1 - r))) =
      D.tube (_, t + sigma * (k * (1 - r) + l * height q))
    rw [hq, mul_zero, add_zero]
  change range (levelPaste height f g) = _
  rw [levelPaste_range height f g heq]
  congr 1
  change (fun q : UnitTwoSphere => ψ (surgeryNorthChart R e q, 0)) ''
    {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} = _
  rw [← image_image (fun p : UnitTwoSphere => ψ (p, 0)),
    surgeryNorthChart_image_hemisphere R e hRball]

theorem capMap_old_surface_source (P : SurgeryCapProfile)
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (u : UnitTwoSphere) (t : ℝ) (D : RegularSurgeryData ψ u t)
    (sigma : ℝ) (hsigma : |sigma| = 1) {c l : ℝ}
    (hc : 0 < c) (hcwidth : c < D.width) (hl : 0 < l)
    (hlM : l * P.heightBound < c / 4)
    (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 ≤ 0)
    (p : UnitTwoSphere) (heq : P.capMap D.tube t sigma c l q = ψ (p, 0)) :
    ∃ theta : UnitCircle, ∃ s : ℝ,
      0 < s ∧ s ≤ c ∧ p = D.sourceCollar (theta, sigma * s) := by
  let s := c + l * (P.model q).2
  have hbounds : 3 * c / 4 < s ∧ s ≤ c := by
    have h := surgeryCapCoordinates_south_height_bounds
      P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
      P.vertical_pos t sigma c l P.heightBound hsigma hl hlM q hq (P.height_bound q)
    rw [surgeryCapCoordinates_signed_height P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
      t sigma c l hsigma q] at h
    exact h
  have hs : 0 < s := lt_trans (by positivity) hbounds.1
  have hband : sigma * s ∈ Ioo (-D.width) D.width := by
    apply abs_lt.mp
    rw [abs_mul, hsigma, one_mul, abs_of_pos hs]
    exact hbounds.2.trans_lt hcwidth
  let X := (P.model q).1
  have hX : X ∈ closedBall (0 : E2) 1 :=
    mem_closedBall_zero_iff.mpr (P.model_fst_norm_le q)
  have hz : t + sigma * s ∈ Ioo (t - D.width) (t + D.width) :=
    ⟨by linarith [hband.1], by linarith [hband.2]⟩
  have hXunit : X ∈ sphere (0 : E2) 1 :=
    (D.surface_mem X hX (t + sigma * s) hz).mp ⟨p, heq.symm⟩
  let theta : UnitCircle := ⟨X, hXunit⟩
  have hrec : ψ (D.sourceCollar (theta, sigma * s), 0) =
      P.capMap D.tube t sigma c l q := D.reconstruction theta (sigma * s) hband
  have hcentral : Function.Injective (fun p : UnitTwoSphere => ψ (p, 0)) := by
    intro p q hpq
    exact congrArg Prod.fst (hψ.2.1 (by simp) (by simp) hpq)
  exact ⟨theta, s, hs, hbounds.2, (hcentral (hrec.trans heq)).symm⟩

end PoincareConjecture.M25.Topology3D.SurgeryCapProfile
