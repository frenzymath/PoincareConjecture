import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Basic

set_option autoImplicit false

namespace PoincareConjecture

open Filter Set
open MeasureTheory
open scoped ENNReal NNReal Topology

theorem volterra_closedBall_fixedPoint
    {E : Type*} [MetricSpace E] [CompleteSpace E]
    (center : E) {radius : ℝ} (hr : 0 ≤ radius) (F : E → E)
    {K : ℝ≥0}
    (hF : MapsTo F (Metric.closedBall center radius)
      (Metric.closedBall center radius))
    (hK : ContractingWith K
      (Set.MapsTo.restrict F (Metric.closedBall center radius)
        (Metric.closedBall center radius) hF)) :
    ∃ y ∈ Metric.closedBall center radius, Function.IsFixedPt F y ∧
      Tendsto (fun m : ℕ ↦ F^[m] center) atTop (𝓝 y) ∧
        ∀ m : ℕ,
          edist (F^[m] center) y ≤
            edist center (F center) * (K : ℝ≥0∞) ^ m / (1 - K) := by
  have hcenter : center ∈ Metric.closedBall center radius := by
    rw [Metric.mem_closedBall]
    simpa using hr
  exact ContractingWith.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hF hK hcenter (edist_ne_top _ _)

theorem norm_intervalIntegral_sub_le_of_norm_sub_le_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b C : ℝ} {f g : ℝ → E}
    (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hbound : ∀ x ∈ Set.uIoc a b, ‖f x - g x‖ ≤ C) :
    ‖(∫ x in a..b, f x) - ∫ x in a..b, g x‖ ≤ C * |b - a| := by
  rw [← intervalIntegral.integral_sub hf hg]
  exact intervalIntegral.norm_integral_le_of_norm_le_const hbound

theorem continuousOn_uncurry_comp_time_path
    {T : ℝ} {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {q : ℝ → E → F}
    (hq : ContinuousOn (Function.uncurry q)
      ((Set.Ico (0 : ℝ) T) ×ˢ Set.univ))
    {u : ℝ → E} (hu : ContinuousOn u (Set.Ico (0 : ℝ) T)) :
    ContinuousOn (fun t ↦ q t (u t)) (Set.Ico (0 : ℝ) T) := by
  have hpair : ContinuousOn (fun t ↦ (t, u t)) (Set.Ico (0 : ℝ) T) :=
    continuousOn_id.prodMk hu
  have hmaps : Set.MapsTo (fun t ↦ (t, u t))
      (Set.Ico (0 : ℝ) T) ((Set.Ico (0 : ℝ) T) ×ˢ Set.univ) := by
    intro t ht
    exact ⟨ht, Set.mem_univ _⟩
  have hcomp := hq.comp hpair hmaps
  simpa only [Function.comp_def, Function.uncurry] using hcomp

end PoincareConjecture
