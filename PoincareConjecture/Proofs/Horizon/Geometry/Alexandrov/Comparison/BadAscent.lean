import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Comparison.NearVertex
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Comparison.DistanceAscent

set_option autoImplicit false

open Set

namespace Poincare.Alexandrov

theorem CurvatureGEnegOne.exists_pos_comparisonAngle_gt_of_not_local_ascent
    {X : Type*} [MetricSpace X] (hX : CurvatureGEnegOne X)
    (hgeo : ∀ x y : X, ∃ γ : ℝ → X, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y)
    {p q : X} (hpq : p ≠ q) {θ c : ℝ}
    (hθ : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hc : 0 ≤ c) (hctheta : c < Real.cos (2 * θ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : X, 0 < dist p y → dist p y < ε →
      ¬ (∀ s : ℝ, 0 < s → ∃ z : X,
        dist y z < s ∧ c * dist y z < dist p z - dist p y) →
      θ < comparisonAngle (dist p y) (dist p q) (dist y q) := by
  have hb : 0 < dist p q := dist_pos.mpr hpq
  obtain ⟨r, hr, hnear⟩ := exists_pos_comparisonAngle_near_vertex hb hθ hθpi
  refine ⟨min r (dist p q / 2), lt_min hr (half_pos hb), ?_⟩
  intro y hypos hysmall hbad
  by_contra! hangle
  have hyr : dist p y < r := hysmall.trans_le (min_le_left _ _)
  have hyhalf : dist p y < dist p q / 2 :=
    hysmall.trans_le (min_le_right _ _)
  have hqy : q ≠ y := by
    intro heq
    subst y
    linarith
  have hlow : |dist p y - dist p q| ≤ dist y q := by
    simpa only [dist_comm y p, dist_comm q p] using abs_dist_sub_le y q p
  have hhigh : dist y q ≤ dist p y + dist p q := by
    simpa only [dist_comm y p] using dist_triangle y p q
  have hopposite : Real.pi - 2 * θ <
      comparisonAngle (dist y p) (dist y q) (dist p q) := by
    simpa only [dist_comm y p] using
      hnear (dist p y) (dist y q) hypos hyr hlow hhigh hangle
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
    (by linarith : 0 ≤ Real.pi - 2 * θ)
    (comparisonAngle_le_pi (dist y p) (dist y q) (dist p q)) hopposite
  rw [Real.cos_pi_sub] at hcos
  obtain ⟨γ, hγ0, hγ1, hγdist⟩ := hgeo y q
  apply hbad
  apply hX.exists_local_distance_ascent_of_comparisonAngle
    (dist_pos.mp hypos) hqy γ hγ0 hγ1 hγdist hc
  linarith only [hctheta, hcos]

end Poincare.Alexandrov
