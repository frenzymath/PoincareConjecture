import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.MovingPoints

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
universe u v
namespace Poincare.GromovHausdorff

theorem ball_one_subset_iUnion_of_near_realization
    {X Y : BasedMetricSpaceBundle.{u}} {s t R ε : ℝ}
    (hs : 0 < s) (ht : 0 < t)
    (Q : PointedGHRealization (ballModel X s hs) (ballModel Y t ht))
    (hsone : 1 ≤ s) (hεR : 1 + ε ≤ R)
    {ι : Type v} (y : ι → (ballModel Y t ht).carrier) (r : ι → ℝ)
    (u : ι → (ballModel X s hs).carrier) (q : ι → X.carrier)
    (hu : ∀ i, dist (Q.left (u i)) (Q.right (y i)) < ε)
    (hq : ∀ i, dist (u i).val (q i) < ε)
    (hQ : pointedHausdorffDist Q < ε)
    (hcover : Metric.closedBall Y.base R ⊆
      ⋃ i, Metric.ball (y i).val (r i)) :
    Metric.ball X.base 1 ⊆ ⋃ i, Metric.ball (q i) (r i + 3 * ε) := by
  intro x hx
  have hx1 : dist X.base x < 1 := Metric.mem_ball'.mp hx
  let xj : (ballModel X s hs).carrier :=
    ⟨x, Metric.mem_ball'.mpr (hx1.trans_le hsone)⟩
  obtain ⟨w, hw⟩ := exists_right_point_lt_of_pointedHausdorffDist_lt Q hQ xj
  have hrad := (abs_lt.mp
    (abs_dist_base_sub_dist_base_lt_of_corresponding Q xj w hw)).1
  have hwR : w.val ∈ Metric.closedBall Y.base R := by
    rw [Metric.mem_closedBall, dist_comm]
    change -ε < dist X.base x - dist Y.base w.val at hrad
    linarith
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hwR)
  refine mem_iUnion.mpr ⟨i, Metric.mem_ball.mpr ?_⟩
  have hwi : dist w.val (y i).val < r i := Metric.mem_ball.mp hi
  have htr := dist_triangle4 (Q.left xj) (Q.right w) (Q.right (y i)) (Q.left (u i))
  rw [Q.left_isometry.dist_eq, Q.right_isometry.dist_eq,
    dist_comm (Q.right (y i)) (Q.left (u i))] at htr
  have hxq := dist_triangle x (u i).val (q i)
  have hui := hu i
  have hqi := hq i
  change dist x (u i).val ≤ dist (Q.left xj) (Q.right w) +
    dist w.val (y i).val + dist (Q.left (u i)) (Q.right (y i)) at htr
  linarith

theorem eventually_ball_one_subset_iUnion_of_pointConverges
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    {L R : ℝ} (hL : 0 < L) (hR : 1 < R) (hRL : R < L)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hpos : ∀ j, 0 < L + δ j)
    (S : VaryingRealizationSequence
      (fun j => (ballModel (X j) (L + δ j) (hpos j)).toBasedMetricSpaceBundle)
      (ballModel Y L hL).toBasedMetricSpaceBundle)
    {ι : Type v} [Finite ι]
    (y : ι → (ballModel Y L hL).carrier) (r : ι → ℝ)
    (u : ∀ j, ι → (ballModel (X j) (L + δ j) (hpos j)).carrier)
    (hu : ∀ i, S.PointConverges (fun j => u j i) (y i))
    (q : ∀ j, ι → (X j).carrier)
    (hq : ∀ i, Tendsto (fun j => dist (u j i).val (q j i)) atTop (𝓝 0))
    (hcover : Metric.closedBall Y.base R ⊆
      ⋃ i, Metric.ball (y i).val (r i))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ j in atTop, Metric.ball (X j).base 1 ⊆
      ⋃ i, Metric.ball (q j i) (r i + η) := by
  classical
  let A (j : ℕ) := ballModel (X j) (L + δ j) (hpos j)
  let B := ballModel Y L hL
  let Q (j : ℕ) : PointedGHRealization (A j) B :=
    { ambient := { carrier := (S.ambient j).carrier
                   metric := (S.ambient j).metric
                   base := S.left j (A j).base }
      left := S.left j
      right := S.right j
      left_isometry := S.left_isometry j
      right_isometry := S.right_isometry j
      left_base := rfl
      right_base := (S.base_agree j).symm }
  let ε : ℝ := min (η / 4) ((R - 1) / 2)
  have hε : 0 < ε := lt_min (by positivity) (by linarith)
  have hεR : 1 + ε ≤ R := by
    have h := min_le_right (η / 4) ((R - 1) / 2)
    dsimp [ε]
    linarith
  have hεη : 3 * ε < η := by
    have h := min_le_left (η / 4) ((R - 1) / 2)
    dsimp [ε]
    linarith
  have hQ0 : Tendsto (fun j => pointedHausdorffDist (Q j)) atTop (𝓝 0) :=
    S.hausdorff_tendsto_zero
  have huclose : ∀ᶠ j in atTop, ∀ i,
      dist (S.left j (u j i)) (S.right j (y i)) < ε :=
    eventually_all.mpr fun i => (hu i).eventually_lt_const hε
  have hqclose : ∀ᶠ j in atTop, ∀ i, dist (u j i).val (q j i) < ε :=
    eventually_all.mpr fun i => (hq i).eventually_lt_const hε
  filter_upwards [hδ.eventually_const_lt (show 1 - L < 0 by linarith),
    hQ0.eventually_lt_const hε, huclose, hqclose] with j hδj hQj huj hqj
  have hcov := ball_one_subset_iUnion_of_near_realization
    (hpos j) hL (Q j) (by linarith : 1 ≤ L + δ j) hεR
    y r (u j) (q j) huj hqj hQj hcover
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hx)
  refine mem_iUnion.mpr ⟨i, Metric.mem_ball.mpr ?_⟩
  have hxi := Metric.mem_ball.mp hi
  linarith

end Poincare.GromovHausdorff
