import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Coverage
import Mathlib.Topology.MetricSpace.UniformConvergence











set_option autoImplicit false
open Set Filter Metric
open scoped Topology

namespace PoincareConjecture.ChartDistance




theorem ball_subset_image_of_uniform_approximation
    {X M : Type*} [MetricSpace X] [MetricSpace M]
    {e f : X → M} {x : X} {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hcompact : IsCompact (closedBall x r))
    (hf : ContinuousOn f (closedBall x r))
    (hopen : IsOpen (f '' ball x r))
    (hlower : ∀ y ∈ closedBall x r, c * dist y x ≤ dist (e y) (e x))
    (hclose : ∀ y ∈ closedBall x r, dist (f y) (e y) < c * r / 4)
    (hconn : IsPreconnected (ball (e x) (c * r / 2))) :
    ball (e x) (c * r / 2) ⊆ f '' ball x r := by
  have hcr : 0 < c * r := mul_pos hc hr
  have hclosed : IsClosed (f '' closedBall x r) := (hcompact.image_of_continuousOn hf).isClosed
  have hclosure : closure (f '' ball x r) ⊆ f '' closedBall x r :=
    closure_minimal (image_mono ball_subset_closedBall) hclosed
  apply hconn.subset_of_closure_inter_subset hopen
  · refine ⟨f x, ?_, mem_image_of_mem f (mem_ball_self hr)⟩
    have hx := hclose x (mem_closedBall_self hr.le)
    change dist (f x) (e x) < c * r / 2
    linarith
  · rintro _ ⟨hz, hzball⟩
    obtain ⟨y, hy, rfl⟩ := hclosure hz
    apply mem_image_of_mem
    have hdist : c * dist y x < c * r := by
      have htri := dist_triangle (e y) (f y) (e x)
      have hnear := hclose y hy
      rw [dist_comm (e y) (f y)] at htri
      have hzdist : dist (f y) (e x) < c * r / 2 := hzball
      linarith [hlower y hy]
    exact (mul_lt_mul_iff_right₀ hc).mp hdist



theorem eventually_ball_subset_image_of_uniform_approximation
    {X : Type*} [MetricSpace X] {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e f : ∀ k, X → M k} {x : X} {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hcompact : IsCompact (closedBall x r))
    (hf : ∀ᶠ k in atTop, ContinuousOn (f k) (closedBall x r))
    (hopen : ∀ᶠ k in atTop, IsOpen (f k '' ball x r))
    (hlower : ∀ k y, y ∈ closedBall x r → c * dist y x ≤ dist (e k y) (e k x))
    (hclose : TendstoUniformlyOn (fun k y => dist (f k y) (e k y))
      (fun _ => 0) atTop (closedBall x r))
    (hconn : ∀ k, IsPreconnected (ball (e k x) (c * r / 2))) :
    ∀ᶠ k in atTop, ball (e k x) (c * r / 2) ⊆ f k '' ball x r := by
  have hsmall : ∀ᶠ k in atTop, ∀ y ∈ closedBall x r,
      dist (f k y) (e k y) < c * r / 4 := by
    have h := Metric.tendstoUniformlyOn_iff.mp hclose (c * r / 4)
      (div_pos (mul_pos hc hr) (by norm_num))
    filter_upwards [h] with k hk y hy
    simpa only [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hk y hy
  filter_upwards [hf, hopen, hsmall] with k hfk hok hsk
  exact ball_subset_image_of_uniform_approximation hr hc hcompact hfk hok
    (hlower k) hsk (hconn k)

end PoincareConjecture.ChartDistance
