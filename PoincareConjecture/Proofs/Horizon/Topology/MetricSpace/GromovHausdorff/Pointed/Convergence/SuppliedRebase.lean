import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.Rebase

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology

namespace Poincare.GromovHausdorff

theorem pointedGHConvergesUnbounded_rebase_of_expanding_realizations
    {X : ℕ → BasedMetricSpaceBundle.{0}} {Y : BasedMetricSpaceBundle.{0}}
    [∀ j, ProperSpace (X j).carrier] [ProperSpace Y.carrier]
    (hXgeo : ∀ j, ∀ x y : (X j).carrier,
      ∃ γ : ℝ → (X j).carrier, γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y)
    (hYgeo : ∀ x y : Y.carrier, ∃ γ : ℝ → Y.carrier,
      γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y)
    {s t : ℕ → ℝ} (hs : ∀ j, 0 < s j) (ht : ∀ j, 0 < t j)
    (hsTop : Tendsto s atTop atTop) (htTop : Tendsto t atTop atTop)
    (Q : ∀ j, PointedGHRealization (ballModel (X j) (s j) (hs j))
      (ballModel Y (t j) (ht j)))
    (hQ : Tendsto (fun j => pointedHausdorffDist (Q j)) atTop (𝓝 0))
    (a : ∀ j, (ballModel (X j) (s j) (hs j)).carrier)
    (b : ∀ j, (ballModel Y (t j) (ht j)).carrier)
    (y : Y.carrier) (hby : ∀ᶠ j in atTop, (b j).val = y)
    (hab : Tendsto (fun j => dist ((Q j).left (a j)) ((Q j).right (b j)))
      atTop (𝓝 0)) :
    PointedGHConvergesUnbounded (fun j => (X j).rebase (a j).val) (Y.rebase y) := by
  let ε (j : ℕ) := pointedHausdorffDist (Q j) +
    dist ((Q j).left (a j)) ((Q j).right (b j)) + 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by
    dsimp [ε]
    positivity [pointedHausdorffDist_nonneg (Q j)]
  have hQε (j : ℕ) : pointedHausdorffDist (Q j) < ε j := by
    dsimp [ε]
    linarith [dist_nonneg (x := (Q j).left (a j)) (y := (Q j).right (b j)),
      show 0 < 1 / ((j : ℝ) + 1) by positivity]
  have habε (j : ℕ) : dist ((Q j).left (a j)) ((Q j).right (b j)) < ε j := by
    dsimp [ε]
    linarith [pointedHausdorffDist_nonneg (Q j),
      show 0 < 1 / ((j : ℝ) + 1) by positivity]
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, add_zero] using
      (hQ.add hab).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hrad : Tendsto (fun j => dist (X j).base (a j).val) atTop
      (𝓝 (dist Y.base y)) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    filter_upwards [hby, hε0.eventually_lt_const hη] with j hj hεj
    have h := abs_dist_base_sub_dist_base_lt_of_corresponding
      (Q j) (a j) (b j) (habε j)
    change |dist (X j).base (a j).val - dist Y.base (b j).val| < ε j at h
    rw [hj] at h
    simpa only [Real.dist_eq] using h.trans hεj
  intro r hr
  refine ⟨fun _ => 0, tendsto_const_nhds, fun _ => by simpa using hr, ?_⟩
  simp only [add_zero]
  constructor
  · refine ⟨2*r, ?_⟩
    intro j x z
    change dist x.val z.val ≤ 2*r
    have hx : dist x.val (a j).val < r := Metric.mem_ball.mp x.property
    have hz : dist (a j).val z.val < r := Metric.mem_ball'.mp z.property
    have htr := dist_triangle x.val (a j).val z.val
    linarith
  · apply tendsto_order.mpr
    constructor
    · intro η hη
      exact Eventually.of_forall fun j => hη.trans_le (pointedGHDistance_nonneg _ _)
    · intro η hη
      filter_upwards [hby,
        hsTop.eventually (eventually_gt_atTop (dist Y.base y + r + 1)),
        htTop.eventually (eventually_gt_atTop (dist Y.base y + r)),
        hrad.eventually_lt_const (show dist Y.base y < dist Y.base y + 1 by linarith),
        hε0.eventually_lt_const (show 0 < η/8 by positivity)] with j hj hsj htj haj hεj
      have hmarginX : dist (X j).base (a j).val + r < s j := by linarith
      have hmarginY : dist Y.base (b j).val + r < t j := by rwa [hj]
      have hbound := pointedGHDistance_rebased_balls_le
        (hXgeo j) hYgeo (hs j) (ht j) (Q j) (a j) (b j)
        hr (hε j) (hQε j) (habε j) hmarginX hmarginY
      rw [hj] at hbound
      exact hbound.trans_lt (by linarith)

end Poincare.GromovHausdorff
