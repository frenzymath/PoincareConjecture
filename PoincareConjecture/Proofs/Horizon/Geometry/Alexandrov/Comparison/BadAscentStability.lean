import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Comparison.BadAscent

set_option autoImplicit false

open Set Filter Topology

namespace Poincare.Alexandrov

theorem eventually_comparisonAngle_gt_of_not_local_ascent
    {ι : Type*} {l : Filter ι} {X : ι → Type*} [∀ j, MetricSpace (X j)]
    (hX : ∀ j, CurvatureGEnegOne (X j))
    (hgeo : ∀ j, ∀ x y : X j, ∃ γ : ℝ → X j, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y)
    (p y q : ∀ j, X j) {b θ c : ℝ}
    (hy : Tendsto (fun j => dist (p j) (y j)) l (𝓝 0))
    (hq : Tendsto (fun j => dist (p j) (q j)) l (𝓝 b)) (hb : 0 < b)
    (hθ : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hc : 0 ≤ c) (hctheta : c < Real.cos (2 * θ))
    (hypos : ∀ᶠ j in l, 0 < dist (p j) (y j))
    (hbad : ∀ᶠ j in l, ¬ (∀ s : ℝ, 0 < s → ∃ z : X j,
      dist (y j) z < s ∧ c * dist (y j) z < dist (p j) z - dist (p j) (y j))) :
    ∀ᶠ j in l,
      θ < comparisonAngle (dist (p j) (y j)) (dist (p j) (q j)) (dist (y j) (q j)) := by
  have hnear : Tendsto (fun j => dist (y j) (q j)) l (𝓝 b) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun j => dist (p j) (q j) - dist (p j) (y j)) l (𝓝 b) by
        simpa only [sub_zero] using hq.sub hy)
      (show Tendsto (fun j => dist (p j) (y j) + dist (p j) (q j)) l (𝓝 b) by
        simpa only [zero_add] using hy.add hq)
    · intro j
      linarith only [dist_triangle (p j) (y j) (q j)]
    · intro j
      simpa only [dist_comm (y j) (p j)] using dist_triangle (y j) (p j) (q j)
  let E : ι → ℝ := fun j =>
    (Real.sinh (dist (p j) (y j)) * Real.cosh (dist (p j) (q j)) -
      Real.cosh (dist (p j) (y j)) * Real.sinh (dist (p j) (q j)) * Real.cos θ) /
        Real.sinh (dist (y j) (q j))
  have hE : Tendsto E l (𝓝 (-Real.cos θ)) := by
    have h := (((Real.continuous_sinh.tendsto 0 |>.comp hy).mul
        (Real.continuous_cosh.tendsto b |>.comp hq)).sub
      (((Real.continuous_cosh.tendsto 0 |>.comp hy).mul
        (Real.continuous_sinh.tendsto b |>.comp hq)).mul_const (Real.cos θ))).div
      (Real.continuous_sinh.tendsto b |>.comp hnear) (Real.sinh_pos_iff.mpr hb).ne'
    convert h using 1
    · rfl
    · simp only [Real.sinh_zero, Real.cosh_zero, zero_mul, one_mul, zero_sub, neg_div]
      field_simp
  have hcosgap : Real.cos (2 * θ) < Real.cos θ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hθ.le (by linarith) (by linarith)
  have hEneg : ∀ᶠ j in l, E j < -c :=
    hE.eventually_lt_const (by linarith only [hctheta, hcosgap])
  filter_upwards [hypos, hq.eventually_const_lt hb, hnear.eventually_const_lt hb,
    hbad, hEneg] with j hyj hqj hnearj hbadj hEj
  by_contra! hangle
  have hlow : |dist (p j) (y j) - dist (p j) (q j)| ≤ dist (y j) (q j) := by
    simpa only [dist_comm (y j) (p j), dist_comm (q j) (p j)] using
      abs_dist_sub_le (y j) (q j) (p j)
  have hhigh : dist (y j) (q j) ≤ dist (p j) (y j) + dist (p j) (q j) := by
    simpa only [dist_comm (y j) (p j)] using dist_triangle (y j) (p j) (q j)
  have hcosangle : Real.cos θ ≤
      Real.cos (comparisonAngle (dist (p j) (y j)) (dist (p j) (q j))
        (dist (y j) (q j))) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (comparisonAngle_nonneg _ _ _)
      (by linarith [Real.pi_pos]) hangle
  have hupper : Real.cos (comparisonAngle (dist (y j) (p j)) (dist (y j) (q j))
      (dist (p j) (q j))) ≤ E j := by
    rw [dist_comm (y j) (p j), cos_comparisonAngle_change_vertex hyj hqj hnearj hlow hhigh]
    apply div_le_div_of_nonneg_right _ (Real.sinh_pos_iff.mpr hnearj).le
    have hmul := mul_le_mul_of_nonneg_left hcosangle
      (mul_nonneg (Real.cosh_pos (dist (p j) (y j))).le (Real.sinh_pos_iff.mpr hqj).le)
    linarith only [hmul]
  obtain ⟨γ, hγ0, hγ1, hγdist⟩ := hgeo j (y j) (q j)
  apply hbadj
  apply (hX j).exists_local_distance_ascent_of_comparisonAngle
    (dist_pos.mp hyj) (dist_pos.mp hnearj).symm γ hγ0 hγ1 hγdist hc
  linarith only [hupper, hEj]

end Poincare.Alexandrov
