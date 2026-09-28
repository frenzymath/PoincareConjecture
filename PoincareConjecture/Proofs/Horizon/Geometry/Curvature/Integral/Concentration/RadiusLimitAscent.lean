import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.AscentRestriction
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.Ascent








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open Poincare.GromovHausdorff

universe u

namespace Poincare.CurvatureIntegral

theorem local_distance_ascent_of_tendsto_badAscentRadius_zero
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    [∀ j, ProperSpace (X j).carrier] [ProperSpace Y.carrier]
    {L : ℝ} (hL : 0 < L) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hpos : ∀ j, 0 < L + δ j)
    (S : VaryingRealizationSequence
      (fun j => (ballModel (X j) (L + δ j) (hpos j)).toBasedMetricSpaceBundle)
      (ballModel Y L hL).toBasedMetricSpaceBundle)
    (u : ∀ j, (ballModel (X j) (L + δ j) (hpos j)).carrier)
    (u₀ : (ballModel Y L hL).carrier) (hu : S.PointConverges u u₀)
    {b c c' : ℝ} (hc : 0 ≤ c) (hcc' : c' < c)
    (hroom : dist Y.base u₀.val + b < L)
    (ha : Tendsto (fun j => badAscentRadius c b (u j).val) atTop (𝓝 0)) :
    ∀ y : Y.carrier, 0 < dist u₀.val y → dist u₀.val y < b →
      HasLocalDistanceAscent c' u₀.val y := by
  classical
  let A : ℕ → FiniteDiameterBasedMetricSpace.{u} := fun j =>
    ballModel (X j) (L + δ j) (hpos j)
  let B : FiniteDiameterBasedMetricSpace.{u} := ballModel Y L hL
  have hcompact₀ : IsCompact (Metric.closedBall B.base (L / 2)) :=
    isCompact_closedBall_ballModel Y hL B.base (by change dist Y.base Y.base + L / 2 < L; simp; linarith)
  obtain ⟨f, hf, _⟩ := exists_approximating_maps_and_subseq_pointConverges S
    (show (0 : ℝ) < L / 2 by positivity) hcompact₀
    (fun j => (A j).base) (fun j => by change dist (A j).base (A j).base ≤ 0; simp)
  intro y hypos hyb
  have hyL : y ∈ Metric.ball Y.base L := by
    rw [Metric.mem_ball, dist_comm]
    have ht := dist_triangle Y.base u₀.val y
    linarith
  let y₀ : B.carrier := ⟨y, hyL⟩
  let x : ∀ j, (A j).carrier := fun j => f j y₀
  have hx : S.PointConverges x y₀ := hf y₀
  let d := dist Y.base y
  let τ := (L - d) / 8
  let ρ := d + τ
  let σ := d + 4 * τ
  have hdL : d < L := by
    change dist Y.base y < L
    rw [dist_comm]
    exact hyL
  have hτ : 0 < τ := by dsimp [τ]; linarith
  have hroom' : ρ + τ < σ := by dsimp [ρ, σ]; linarith
  have hσL : σ < L := by dsimp [σ, τ]; linarith
  have hcompact : IsCompact (Metric.closedBall B.base σ) :=
    isCompact_closedBall_ballModel Y hL B.base
      (by change dist Y.base Y.base + σ < L; simpa only [dist_self, zero_add] using hσL)
  have hxBound : ∀ᶠ j in atTop, dist (A j).base (x j) < ρ :=
    (S.tendsto_dist_base x y₀ hx).eventually_lt_const (by change d < ρ; dsimp [ρ]; linarith)
  have hsourceRoom : ∀ᶠ j in atTop, ρ + τ < L + δ j := by
    have ht : Tendsto (fun j => L + δ j) atTop (𝓝 L) := by
      simpa using hδ.const_add L
    exact ht.eventually_const_lt (hroom'.trans hσL)
  have hsource : ∀ᶠ j in atTop, IsCompact (Metric.closedBall (x j) τ) := by
    filter_upwards [hxBound, hsourceRoom] with j hj hL'
    apply isCompact_closedBall_ballModel (X j) (hpos j) (x j)
    change dist (A j).base (x j) + τ < L + δ j
    linarith
  let a := dist u₀.val y / 2
  have hapos : 0 < a := half_pos hypos
  have hascent : ∀ᶠ j in atTop, ∀ z : (A j).carrier,
      a < dist (u j) z → dist (u j) z < b →
      HasLocalDistanceAscent c (u j) z := by
    filter_upwards [ha.eventually_lt_const hapos] with j hj z hz hzb
    apply (hasLocalDistanceAscent_ballModel_iff (X j) (hpos j) c (u j) z).mpr
    exact hasLocalDistanceAscent_of_badAscentRadius_lt (hj.trans hz) hzb.le
  have hresult := S.local_distance_ascent_of_eventually_annular_ascent hu hx hτ
    hroom' hc hcc' hcompact hsource (hxBound.mono (fun _ hj => hj.le)) hascent
    (show a < dist u₀ y₀ from half_lt_self hypos) (show dist u₀ y₀ < b from hyb)
  exact HasLocalDistanceAscent.of_subtype hresult

end Poincare.CurvatureIntegral
