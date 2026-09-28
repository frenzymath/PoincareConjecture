import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.Cone
import Mathlib.Topology.UniformSpace.Dini














noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace Poincare.AncientVolume.ScalarRatio

open Splitting (segmentComparisonCosine)

variable {X : Type*} [MetricSpace X] {p : X}



theorem continuous_basedMinimizingRay_evaluation :
    Continuous (fun a : ℝ≥0 × basedMinimizingRays p => a.2.1 a.1) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hr : ∀ᶠ b : ℝ≥0 × basedMinimizingRays p in 𝓝 a, dist b.1 a.1 < ε / 2 :=
    continuous_fst.continuousAt.eventually (Metric.ball_mem_nhds a.1 (half_pos hε))
  have heval : Continuous (fun b : ℝ≥0 × basedMinimizingRays p => b.2.1 a.1) :=
    (continuous_apply a.1).comp (continuous_subtype_val.comp continuous_snd)
  have hγ : ∀ᶠ b : ℝ≥0 × basedMinimizingRays p in 𝓝 a,
      dist (b.2.1 a.1) (a.2.1 a.1) < ε / 2 :=
    heval.continuousAt.eventually (Metric.ball_mem_nhds _ (half_pos hε))
  filter_upwards [hr, hγ] with b hbr hbγ
  have ht := dist_triangle (b.2.1 b.1) (b.2.1 a.1) (a.2.1 a.1)
  rw [b.2.2.2.dist_eq] at ht
  linarith

theorem continuous_rescaled_ray_evaluation (L : ℝ) :
    Continuous (fun a : ℝ≥0 × basedMinimizingRays p => rayExtension a.2 (a.1 * L)) := by
  have ht : Continuous (fun a : ℝ≥0 × basedMinimizingRays p =>
      (((a.1 : ℝ) * L).toNNReal, a.2)) := by fun_prop
  exact continuous_basedMinimizingRay_evaluation.comp ht


def asymptoticConeRayProjection (hcomparison : RayComparison p)
    (a : ℝ≥0 × basedMinimizingRays p) : AsymptoticCone p hcomparison :=
  asymptoticConeProjection hcomparison (a.1, asymptoticLinkProjection hcomparison a.2)

theorem continuous_asymptoticConeRayProjection (hcomparison : RayComparison p) :
    Continuous (asymptoticConeRayProjection hcomparison) := by
  exact (continuous_asymptoticConeProjection hcomparison).comp
    (continuous_fst.prodMk ((continuous_asymptoticLinkProjection hcomparison).comp continuous_snd))

private theorem normalized_ray_distance_left_zero (γ η : basedMinimizingRays p)
    (s : ℝ≥0) {L : ℝ} (hL : 0 < L) :
    dist (rayExtension γ ((0 : ℝ≥0) * L)) (rayExtension η (s * L)) / L = s := by
  simp only [NNReal.coe_zero, zero_mul, rayExtension_zero]
  have hd := rayExtension_dist η le_rfl (mul_nonneg s.coe_nonneg hL.le)
  rw [rayExtension_zero, zero_sub, abs_neg,
    abs_of_nonneg (mul_nonneg s.coe_nonneg hL.le)] at hd
  rw [hd]
  exact mul_div_cancel_right₀ (s : ℝ) hL.ne'

private theorem normalized_ray_distance_right_zero (γ η : basedMinimizingRays p)
    (r : ℝ≥0) {L : ℝ} (hL : 0 < L) :
    dist (rayExtension γ (r * L)) (rayExtension η ((0 : ℝ≥0) * L)) / L = r := by
  rw [dist_comm]
  exact normalized_ray_distance_left_zero η γ r hL



theorem antitoneOn_rescaled_ray_distance (hcomparison : RayComparison p)
    (γ η : basedMinimizingRays p) (r s : ℝ≥0) :
    AntitoneOn (fun L : ℝ => dist (rayExtension γ (r * L)) (rayExtension η (s * L)) / L)
      (Ioi 0) := by
  intro a ha b hb hab
  dsimp only
  change 0 < a at ha
  change 0 < b at hb
  by_cases hr : r = 0
  · subst r
    simp only [normalized_ray_distance_left_zero γ η s ha, normalized_ray_distance_left_zero γ η s hb,
      le_refl]
  by_cases hs : s = 0
  · subst s
    simp only [normalized_ray_distance_right_zero γ η r ha, normalized_ray_distance_right_zero γ η r hb,
      le_refl]
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hr)
  have hspos : 0 < (s : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hs)
  have h := hcomparison γ η (r * b) (s * b) (mul_pos hrpos hb) (mul_pos hspos hb)
    (r * a) ⟨mul_nonneg r.coe_nonneg ha.le, mul_le_mul_of_nonneg_left hab r.coe_nonneg⟩
    (s * a) ⟨mul_nonneg s.coe_nonneg ha.le, mul_le_mul_of_nonneg_left hab s.coe_nonneg⟩
  have heq : ((r : ℝ) * a) ^ 2 + ((s : ℝ) * a) ^ 2 - 2 * (r * a) * (s * a) *
      segmentComparisonCosine (rayExtension γ) (rayExtension η) (r * b) (s * b) =
      (a * (dist (rayExtension γ (r * b)) (rayExtension η (s * b)) / b)) ^ 2 := by
    unfold segmentComparisonCosine
    field_simp [hrpos.ne', hspos.ne', hb.ne']
    ring
  rw [heq] at h
  apply (le_div_iff₀ ha).mpr
  have hnonneg := mul_nonneg ha.le
    (div_nonneg (dist_nonneg (x := rayExtension γ (r * b))
      (y := rayExtension η (s * b))) hb.le)
  nlinarith [dist_nonneg (x := rayExtension γ (r * a)) (y := rayExtension η (s * a))]


theorem cone_distance_le_rescaled_ray_distance (hcomparison : RayComparison p)
    (γ η : basedMinimizingRays p) (r s : ℝ≥0) {L : ℝ} (hL : 0 < L) :
    dist (asymptoticConeRayProjection hcomparison (r, γ))
      (asymptoticConeRayProjection hcomparison (s, η)) ≤
        dist (rayExtension γ (r * L)) (rayExtension η (s * L)) / L := by
  apply le_of_tendsto (tendsto_dist_asymptoticConeProjection hcomparison γ η r s)
  filter_upwards [eventually_ge_atTop L] with a ha
  exact antitoneOn_rescaled_ray_distance hcomparison γ η r s hL (hL.trans_le ha) ha



theorem tendstoUniformlyOn_cone_distance [ProperSpace X]
    (hcomparison : RayComparison p) (R : ℝ≥0) :
    TendstoUniformlyOn
      (fun L : ℝ => fun q : (ℝ≥0 × basedMinimizingRays p) × (ℝ≥0 × basedMinimizingRays p) =>
        dist (rayExtension q.1.2 (q.1.1 * L)) (rayExtension q.2.2 (q.2.1 * L)) / L)
      (fun q => dist (asymptoticConeRayProjection hcomparison q.1)
        (asymptoticConeRayProjection hcomparison q.2)) atTop
      ((Icc (0 : ℝ≥0) R ×ˢ (univ : Set (basedMinimizingRays p))) ×ˢ
        (Icc (0 : ℝ≥0) R ×ˢ (univ : Set (basedMinimizingRays p)))) := by
  let F := fun L : ℝ => fun q :
      (ℝ≥0 × basedMinimizingRays p) × (ℝ≥0 × basedMinimizingRays p) =>
    dist (rayExtension q.1.2 (q.1.1 * max L 1))
      (rayExtension q.2.2 (q.2.1 * max L 1)) / max L 1
  have hcompact : IsCompact
      ((Icc (0 : ℝ≥0) R ×ˢ (univ : Set (basedMinimizingRays p))) ×ˢ
        (Icc (0 : ℝ≥0) R ×ˢ (univ : Set (basedMinimizingRays p)))) :=
    (isCompact_Icc.prod isCompact_univ).prod (isCompact_Icc.prod isCompact_univ)
  have hcont (L : ℝ) : Continuous (F L) :=
    (((continuous_rescaled_ray_evaluation (max L 1)).comp continuous_fst).dist
      ((continuous_rescaled_ray_evaluation (max L 1)).comp continuous_snd)).div_const _
  have hlimit : Continuous (fun q :
      (ℝ≥0 × basedMinimizingRays p) × (ℝ≥0 × basedMinimizingRays p) =>
      dist (asymptoticConeRayProjection hcomparison q.1)
        (asymptoticConeRayProjection hcomparison q.2)) :=
    ((continuous_asymptoticConeRayProjection hcomparison).comp continuous_fst).dist
      ((continuous_asymptoticConeRayProjection hcomparison).comp continuous_snd)
  have hanti (q : (ℝ≥0 × basedMinimizingRays p) × (ℝ≥0 × basedMinimizingRays p)) :
      Antitone (fun L => F L q) := by
    intro a b hab
    exact antitoneOn_rescaled_ray_distance hcomparison q.1.2 q.2.2 q.1.1 q.2.1
      (zero_lt_one.trans_le (le_max_right a 1)) (zero_lt_one.trans_le (le_max_right b 1))
      (max_le_max_right 1 hab)
  have hpoint (q : (ℝ≥0 × basedMinimizingRays p) × (ℝ≥0 × basedMinimizingRays p)) :
      Tendsto (fun L => F L q) atTop
        (𝓝 (dist (asymptoticConeRayProjection hcomparison q.1)
          (asymptoticConeRayProjection hcomparison q.2))) := by
    apply (tendsto_dist_asymptoticConeProjection hcomparison q.1.2 q.2.2 q.1.1 q.2.1).congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    simp only [F, max_eq_left hL]
  have huni := Antitone.tendstoUniformlyOn_of_forall_tendsto hcompact
    (fun L => (hcont L).continuousOn) (fun q _ => hanti q) hlimit.continuousOn
    (fun q _ => hpoint q)
  rw [Metric.tendstoUniformlyOn_iff] at huni ⊢
  intro ε hε
  filter_upwards [huni ε hε, eventually_ge_atTop (1 : ℝ)] with L hL hLone q hq
  simpa only [F, max_eq_left hLone] using hL q hq



theorem exists_uniform_cone_distance_bound [ProperSpace X]
    (hcomparison : RayComparison p) (R : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      ∀ r s : ℝ≥0, r ≤ R → s ≤ R → ∀ γ η : basedMinimizingRays p,
      0 ≤ dist (rayExtension γ (r * L)) (rayExtension η (s * L)) / L -
        dist (asymptoticConeRayProjection hcomparison (r, γ))
          (asymptoticConeRayProjection hcomparison (s, η)) ∧
      dist (rayExtension γ (r * L)) (rayExtension η (s * L)) / L -
        dist (asymptoticConeRayProjection hcomparison (r, γ))
          (asymptoticConeRayProjection hcomparison (s, η)) < ε := by
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp
    ((Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_cone_distance hcomparison R)) ε hε)
  refine ⟨max L₀ 1, lt_max_of_lt_right zero_lt_one, ?_⟩
  intro L hL r s hr hs γ η
  have hLpos : 0 < L := (lt_max_of_lt_right zero_lt_one).trans_le hL
  refine ⟨sub_nonneg.mpr (cone_distance_le_rescaled_ray_distance hcomparison γ η r s hLpos), ?_⟩
  have h := hL₀ L ((le_max_left L₀ 1).trans hL) ((r, γ), (s, η))
    ⟨⟨⟨zero_le, hr⟩, mem_univ _⟩, ⟨⟨zero_le, hs⟩, mem_univ _⟩⟩
  rw [Real.dist_eq, abs_sub_comm] at h
  exact (le_abs_self _).trans_lt h

end Poincare.AncientVolume.ScalarRatio
