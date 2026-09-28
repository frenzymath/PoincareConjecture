import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Horoball









set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.Riemannian.Soul

variable {M : Type*} [MetricSpace M]

theorem exists_far_distance_gap_of_singleton_horoball
    {o p q : M} {c : ℝ}
    (hlevel : horoballIntersection o c = {p}) (hqp : q ≠ p) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ L : ℝ, ∃ z : M,
      L ≤ dist z q ∧ δ < dist z p - dist z q := by
  have hp : p ∈ horoballIntersection o c := by rw [hlevel]; exact mem_singleton p
  have hq : q ∉ horoballIntersection o c := by simpa only [hlevel, mem_singleton_iff]
  change ¬ ∀ ray : ℝ → M, IsRay ray → ray 0 = o → -c ≤ busemann ray q at hq
  push Not at hq
  obtain ⟨ray, hray, hbase, hq⟩ := hq
  have hgap : 0 < busemann ray p - busemann ray q := by
    have := hp ray hray hbase
    linarith
  let δ := (busemann ray p - busemann ray q) / 2
  have hδ : 0 < δ := half_pos hgap
  refine ⟨δ, hδ, ?_⟩
  intro L
  have hlim := (tendsto_busemannApprox hray p).sub (tendsto_busemannApprox hray q)
  have hevent : ∀ᶠ T : ℝ in atTop,
      δ < busemannApprox ray T p - busemannApprox ray T q :=
    hlim.eventually (eventually_gt_nhds (by dsimp [δ]; linarith))
  obtain ⟨T, hTgap, hTzero, hTfar⟩ :=
    (hevent.and ((eventually_ge_atTop (0 : ℝ)).and
      (eventually_ge_atTop (L + dist (ray 0) q)))).exists
  refine ⟨ray T, ?_, ?_⟩
  · have hdist : dist (ray 0) (ray T) = T := by
      simpa only [zero_sub, abs_neg, abs_of_nonneg hTzero] using hray le_rfl hTzero
    have := dist_triangle (ray 0) q (ray T)
    rw [hdist, dist_comm q (ray T)] at this
    linarith
  · dsimp [busemannApprox] at hTgap
    linarith

theorem exists_squared_distance_gap_of_singleton_horoball
    {o p q : M} {c : ℝ}
    (hlevel : horoballIntersection o c = {p}) (hqp : q ≠ p) :
    ∃ z : M, 0 < dist z p ^ 2 - dist z q ^ 2 - dist q p ^ 2 := by
  obtain ⟨δ, hδ, hfar⟩ := exists_far_distance_gap_of_singleton_horoball hlevel hqp
  obtain ⟨z, hz, hgap⟩ := hfar (dist q p ^ 2 / (2 * δ) + 1)
  have hmul : dist q p ^ 2 < 2 * δ * dist z q := by
    have := (div_le_iff₀ (by positivity : 0 < 2 * δ)).mp (by linarith :
      dist q p ^ 2 / (2 * δ) ≤ dist z q - 1)
    nlinarith
  refine ⟨z, ?_⟩
  have hsum : 2 * dist z q ≤ dist z p + dist z q := by linarith
  have hproduct := mul_le_mul_of_nonneg_left hsum hδ.le
  have hstrict := mul_lt_mul_of_pos_right hgap (by
    have := dist_nonneg (x := z) (y := q)
    linarith : 0 < dist z p + dist z q)
  nlinarith

end Poincare.Riemannian.Soul
