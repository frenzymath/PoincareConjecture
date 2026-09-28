import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.Link
import Mathlib.Topology.UniformSpace.Dini

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace Poincare.AncientVolume.ScalarRatio

open Splitting (segmentComparisonCosine)

variable {X : Type*} [MetricSpace X] {p : X}

theorem antitoneOn_normalized_ray_distance (hcomparison : RayComparison p)
    (γ η : basedMinimizingRays p) :
    AntitoneOn (fun L : ℝ => dist (rayExtension γ L) (rayExtension η L) / L) (Ioi 0) := by
  intro r hr L hL hrL
  change 0 < r at hr
  change 0 < L at hL
  have h := hcomparison γ η L L hL hL r ⟨hr.le, hrL⟩ r ⟨hr.le, hrL⟩
  have heq : r ^ 2 + r ^ 2 - 2 * r * r *
      segmentComparisonCosine (rayExtension γ) (rayExtension η) L L =
      (r * (dist (rayExtension γ L) (rayExtension η L) / L)) ^ 2 := by
    unfold segmentComparisonCosine
    field_simp [hL.ne']
    ring
  rw [heq] at h
  apply (le_div_iff₀ hr).mpr
  have hnonneg := mul_nonneg hr.le
    (div_nonneg (dist_nonneg (x := rayExtension γ L) (y := rayExtension η L)) hL.le)
  nlinarith [dist_nonneg (x := rayExtension γ r) (y := rayExtension η r)]

theorem asymptoticRayDistance_le_normalized_ray_distance (hcomparison : RayComparison p)
    (γ η : basedMinimizingRays p) {L : ℝ} (hL : 0 < L) :
    asymptoticRayDistance γ η ≤ dist (rayExtension γ L) (rayExtension η L) / L := by
  apply le_of_tendsto (tendsto_asymptoticRayDistance hcomparison γ η)
  filter_upwards [eventually_ge_atTop L] with r hr
  exact antitoneOn_normalized_ray_distance hcomparison γ η hL (hL.trans_le hr) hr

theorem continuous_asymptoticRayDistance (hcomparison : RayComparison p) :
    Continuous (fun q : basedMinimizingRays p × basedMinimizingRays p =>
      asymptoticRayDistance q.1 q.2) := by
  have h : Continuous (fun q : basedMinimizingRays p × basedMinimizingRays p =>
      asymptoticLinkProjection hcomparison q.1) :=
    (continuous_asymptoticLinkProjection hcomparison).comp continuous_fst
  have h' : Continuous (fun q : basedMinimizingRays p × basedMinimizingRays p =>
      asymptoticLinkProjection hcomparison q.2) :=
    (continuous_asymptoticLinkProjection hcomparison).comp continuous_snd
  simpa only [dist_asymptoticLinkProjection] using h.dist h'

theorem tendstoUniformly_asymptoticRayDistance [ProperSpace X]
    (hcomparison : RayComparison p) :
    TendstoUniformly
      (fun L : ℝ => fun q : basedMinimizingRays p × basedMinimizingRays p =>
        dist (rayExtension q.1 L) (rayExtension q.2 L) / L)
      (fun q => asymptoticRayDistance q.1 q.2) atTop := by
  let F := fun L : ℝ => fun q : basedMinimizingRays p × basedMinimizingRays p =>
    dist (rayExtension q.1 (max L 1)) (rayExtension q.2 (max L 1)) / max L 1
  have hcont (L : ℝ) : Continuous (F L) := by
    have h₁ : Continuous (fun q : basedMinimizingRays p × basedMinimizingRays p =>
        q.1.1 (max L 1).toNNReal) :=
      (continuous_apply _).comp (continuous_subtype_val.comp continuous_fst)
    have h₂ : Continuous (fun q : basedMinimizingRays p × basedMinimizingRays p =>
        q.2.1 (max L 1).toNNReal) :=
      (continuous_apply _).comp (continuous_subtype_val.comp continuous_snd)
    exact (h₁.dist h₂).div_const _
  have hanti : Antitone F := by
    intro a b hab q
    dsimp only [F]
    exact antitoneOn_normalized_ray_distance hcomparison q.1 q.2
      (zero_lt_one.trans_le (le_max_right a 1)) (zero_lt_one.trans_le (le_max_right b 1))
      (max_le_max_right 1 hab)
  have hpoint (q : basedMinimizingRays p × basedMinimizingRays p) :
      Tendsto (fun L => F L q) atTop (𝓝 (asymptoticRayDistance q.1 q.2)) := by
    apply (tendsto_asymptoticRayDistance hcomparison q.1 q.2).congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    simp only [F, max_eq_left hL]
  have huni := Antitone.tendstoUniformly_of_forall_tendsto hcont hanti
    (continuous_asymptoticRayDistance hcomparison) hpoint
  rw [Metric.tendstoUniformly_iff] at huni ⊢
  intro ε hε
  filter_upwards [huni ε hε, eventually_ge_atTop (1 : ℝ)] with L hL hLone q
  simpa only [F, max_eq_left hLone] using hL q

theorem exists_uniform_normalized_ray_distance_bound [ProperSpace X]
    (hcomparison : RayComparison p) {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ γ η : basedMinimizingRays p,
      0 ≤ dist (rayExtension γ L) (rayExtension η L) / L - asymptoticRayDistance γ η ∧
      dist (rayExtension γ L) (rayExtension η L) / L - asymptoticRayDistance γ η < ε := by
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp
    ((Metric.tendstoUniformly_iff.mp (tendstoUniformly_asymptoticRayDistance hcomparison)) ε hε)
  refine ⟨max L₀ 1, lt_max_of_lt_right zero_lt_one, ?_⟩
  intro L hL γ η
  have hLpos : 0 < L := (lt_max_of_lt_right zero_lt_one).trans_le hL
  refine ⟨sub_nonneg.mpr (asymptoticRayDistance_le_normalized_ray_distance
    hcomparison γ η hLpos), ?_⟩
  have h := hL₀ L ((le_max_left L₀ 1).trans hL) (γ, η)
  rw [Real.dist_eq, abs_sub_comm] at h
  exact (le_abs_self _).trans_lt h

end Poincare.AncientVolume.ScalarRatio
