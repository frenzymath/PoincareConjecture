import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false

open Set Filter
open scoped InnerProductSpace Topology NNReal

namespace Poincare.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def nearestPoint (K : Set E) (hne : K.Nonempty)
    (hclosed : IsClosed K) (hconv : Convex ℝ K) (v : E) : E := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact Classical.choose (exists_norm_eq_iInf_of_complete_convex
    hne hclosed.isComplete hconv v)

lemma nearestPoint_mem (K : Set E) (hne : K.Nonempty)
    (hclosed : IsClosed K) (hconv : Convex ℝ K) (v : E) :
    nearestPoint K hne hclosed hconv v ∈ K := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex
    hne hclosed.isComplete hconv v)).1

lemma norm_sub_nearestPoint (K : Set E) (hne : K.Nonempty)
    (hclosed : IsClosed K) (hconv : Convex ℝ K) (v : E) :
    ‖v - nearestPoint K hne hclosed hconv v‖ = Metric.infDist v K := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [Metric.infDist_eq_iInf]
  simpa only [nearestPoint, dist_eq_norm] using
    (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex
      hne hclosed.isComplete hconv v)).2

lemma nearestPoint_support (K : Set E) (hne : K.Nonempty)
    (hclosed : IsClosed K) (hconv : Convex ℝ K) (v z : E) (hz : z ∈ K) :
    ⟪v - nearestPoint K hne hclosed hconv v,
      z - nearestPoint K hne hclosed hconv v⟫_ℝ ≤ 0 := by
  apply (norm_eq_iInf_iff_real_inner_le_zero hconv
    (nearestPoint_mem K hne hclosed hconv v)).mp ?_ z hz
  simpa only [Metric.infDist_eq_iInf, dist_eq_norm] using
    norm_sub_nearestPoint K hne hclosed hconv v

def unitSupportSet (K : Set E) : Set (E × E) :=
  {q | q.1 ∈ K ∧ ‖q.2‖ = 1 ∧ ∀ z ∈ K, ⟪q.2, z - q.1⟫_ℝ ≤ 0}

def boundedUnitSupportSet (K : Set E) (R : ℝ) : Set (E × E) :=
  unitSupportSet K ∩ {q | ‖q.1‖ ≤ R}

omit [FiniteDimensional ℝ E] in
lemma isClosed_unitSupportSet (K : Set E) (hK : IsClosed K) :
    IsClosed (unitSupportSet K) := by
  have hsupport : IsClosed {q : E × E | ∀ z ∈ K, ⟪q.2, z - q.1⟫_ℝ ≤ 0} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun z => isClosed_iInter fun _ =>
      isClosed_le (continuous_snd.inner (continuous_const.sub continuous_fst)) continuous_const
  exact (hK.preimage continuous_fst).inter
    ((isClosed_eq (continuous_norm.comp continuous_snd) continuous_const).inter hsupport)

lemma isCompact_boundedUnitSupportSet (K : Set E) (R : ℝ) (hK : IsClosed K) :
    IsCompact (boundedUnitSupportSet K R) := by
  have hc : IsClosed (boundedUnitSupportSet K R) :=
    (isClosed_unitSupportSet K hK).inter
      (isClosed_le (continuous_norm.comp continuous_fst) continuous_const)
  apply ((isCompact_closedBall (0 : E) R).prod
    (isCompact_closedBall (0 : E) 1)).of_isClosed_subset hc
  intro q hq
  exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right, mem_ofPred_eq] using hq.2,
    by simp only [Metric.mem_closedBall, dist_zero_right, hq.1.2.1, le_refl]⟩

lemma unitSupport_eval_le_infDist {K : Set E} (hne : K.Nonempty)
    (hclosed : IsClosed K) (hconv : Convex ℝ K) {q : E × E}
    (hq : q ∈ unitSupportSet K) (v : E) :
    ⟪q.2, v - q.1⟫_ℝ ≤ Metric.infDist v K := by
  let p := nearestPoint K hne hclosed hconv v
  have hs := hq.2.2 p (nearestPoint_mem K hne hclosed hconv v)
  have hn : ⟪q.2, v - p⟫_ℝ ≤ ‖v - p‖ := by
    simpa only [hq.2.1, one_mul] using real_inner_le_norm q.2 (v - p)
  calc
    ⟪q.2, v - q.1⟫_ℝ = ⟪q.2, v - p⟫_ℝ + ⟪q.2, p - q.1⟫_ℝ := by
      rw [← inner_add_right]
      congr 1
      abel
    _ ≤ ‖v - p‖ := by linarith
    _ = Metric.infDist v K := norm_sub_nearestPoint K hne hclosed hconv v

lemma norm_nearestPoint_le {K : Set E} (hne : K.Nonempty)
    (hclosed : IsClosed K) (hconv : Convex ℝ K) {z₀ v : E}
    (hz₀ : z₀ ∈ K) {B : ℝ} (hv : ‖v‖ ≤ B) :
    ‖nearestPoint K hne hclosed hconv v‖ ≤ 2 * B + ‖z₀‖ := by
  let p := nearestPoint K hne hclosed hconv v
  have hnear : ‖v - p‖ ≤ ‖v - z₀‖ := by
    rw [norm_sub_nearestPoint]
    simpa only [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := v) hz₀
  have hp : ‖p‖ ≤ ‖v‖ + ‖v - p‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le v (v - p)
  have hz := norm_sub_le v z₀
  linarith

theorem exists_boundedUnitSupport_active {K : Set E} (hne : K.Nonempty)
    (hclosed : IsClosed K) (hconv : Convex ℝ K) {z₀ v : E}
    (hz₀ : z₀ ∈ K) {B : ℝ} (hvB : ‖v‖ ≤ B) (hv : v ∉ K) :
    ∃ q ∈ boundedUnitSupportSet K (2 * B + ‖z₀‖),
      ⟪q.2, v - q.1⟫_ℝ = Metric.infDist v K := by
  let p := nearestPoint K hne hclosed hconv v
  let r := ‖v - p‖
  have hr : 0 < r := by
    rw [show r = Metric.infDist v K from norm_sub_nearestPoint K hne hclosed hconv v]
    exact (hclosed.notMem_iff_infDist_pos hne).mp hv
  refine ⟨(p, r⁻¹ • (v - p)), ⟨⟨nearestPoint_mem K hne hclosed hconv v, ?_, ?_⟩,
    norm_nearestPoint_le hne hclosed hconv hz₀ hvB⟩, ?_⟩
  · change ‖r⁻¹ • (v - p)‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact inv_mul_cancel₀ hr.ne'
  · intro z hz
    change ⟪r⁻¹ • (v - p), z - p⟫_ℝ ≤ 0
    rw [real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hr.le)
      (nearestPoint_support K hne hclosed hconv v z hz)
  · change ⟪r⁻¹ • (v - p), v - p⟫_ℝ = Metric.infDist v K
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    change r⁻¹ * r ^ 2 = Metric.infDist v K
    calc
      r⁻¹ * r ^ 2 = r := by field_simp
      _ = Metric.infDist v K := norm_sub_nearestPoint K hne hclosed hconv v

lemma unitSupport_at_nearestPoint_of_active {K : Set E} (hne : K.Nonempty)
    (hclosed : IsClosed K) (hconv : Convex ℝ K) {q : E × E}
    (hq : q ∈ unitSupportSet K) {v : E}
    (hactive : ⟪q.2, v - q.1⟫_ℝ = Metric.infDist v K) :
    (nearestPoint K hne hclosed hconv v, q.2) ∈ unitSupportSet K := by
  let p := nearestPoint K hne hclosed hconv v
  have hp := nearestPoint_mem K hne hclosed hconv v
  have hs := hq.2.2 p hp
  have hn : ⟪q.2, v - p⟫_ℝ ≤ Metric.infDist v K := by
    rw [← norm_sub_nearestPoint K hne hclosed hconv v]
    simpa only [hq.2.1, one_mul] using real_inner_le_norm q.2 (v - p)
  have heq : ⟪q.2, v - q.1⟫_ℝ = ⟪q.2, v - p⟫_ℝ + ⟪q.2, p - q.1⟫_ℝ := by
    rw [← inner_add_right]
    congr 1
    abel
  have hzero : ⟪q.2, p - q.1⟫_ℝ = 0 := by linarith
  refine ⟨hp, hq.2.1, ?_⟩
  intro z hz
  have h := hq.2.2 z hz
  have heq' : ⟪q.2, z - p⟫_ℝ = ⟪q.2, z - q.1⟫_ℝ - ⟪q.2, p - q.1⟫_ℝ := by
    rw [← inner_sub_right]
    congr 1
    abel
  linarith

omit [FiniteDimensional ℝ E] in

theorem support_inner_velocity_nonpos {K : Set E} {p n w : E}
    (hsupport : ∀ z ∈ K, ⟪n, z - p⟫_ℝ ≤ 0)
    {γ : ℝ → E} {a ε : ℝ} (hε : 0 < ε) (hγa : γ a = p)
    (hγ : ∀ t ∈ Icc a (a + ε), γ t ∈ K)
    (hd : HasDerivWithinAt γ w (Icc a (a + ε)) a) : ⟪n, w⟫_ℝ ≤ 0 := by
  have hmax : IsMaxOn (fun t => ⟪n, γ t - p⟫_ℝ) (Icc a (a + ε)) a := by
    intro t ht
    change ⟪n, γ t - p⟫_ℝ ≤ ⟪n, γ a - p⟫_ℝ
    simpa only [hγa, sub_self, inner_zero_right] using hsupport (γ t) (hγ t ht)
  have hscalar : HasDerivWithinAt (fun t => ⟪n, γ t - p⟫_ℝ)
      ⟪n, w⟫_ℝ (Icc a (a + ε)) a := by
    simpa using (hasDerivWithinAt_const a (Icc a (a + ε)) n).inner ℝ (hd.sub_const p)
  have hcone : (a + ε) - a ∈ posTangentConeAt (Icc a (a + ε)) a :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc a (a + ε)).segment_subset ⟨le_rfl, by linarith⟩
        ⟨by linarith, le_rfl⟩)
  have h := hmax.localize.hasFDerivWithinAt_nonpos hscalar.hasFDerivWithinAt hcone
  change ((a + ε) - a) * ⟪n, w⟫_ℝ ≤ 0 at h
  nlinarith

theorem reaction_inner_le_mul_infDist {K S : Set E} (hne : K.Nonempty)
    (hclosed : IsClosed K) (hconv : Convex ℝ K) {q : E × E}
    (hq : q ∈ unitSupportSet K) {v : E}
    (hactive : ⟪q.2, v - q.1⟫_ℝ = Metric.infDist v K)
    {ψ : E → E} {C : ℝ≥0} (hψ : LipschitzOnWith C ψ S)
    (hv : v ∈ S) (hp : nearestPoint K hne hclosed hconv v ∈ S)
    (hinward : ∀ r ∈ unitSupportSet K, ⟪r.2, ψ r.1⟫_ℝ ≤ 0) :
    ⟪q.2, ψ v⟫_ℝ ≤ C * Metric.infDist v K := by
  let p := nearestPoint K hne hclosed hconv v
  have hi := hinward (p, q.2)
    (unitSupport_at_nearestPoint_of_active hne hclosed hconv hq hactive)
  have hnorm : ⟪q.2, ψ v - ψ p⟫_ℝ ≤ ‖ψ v - ψ p‖ := by
    simpa only [hq.2.1, one_mul] using real_inner_le_norm q.2 (ψ v - ψ p)
  have hlip : ‖ψ v - ψ p‖ ≤ C * Metric.infDist v K := by
    simpa only [dist_eq_norm, p, norm_sub_nearestPoint K hne hclosed hconv v] using
      hψ.dist_le_mul v hv p hp
  rw [inner_sub_right] at hnorm
  change ⟪q.2, ψ p⟫_ℝ ≤ 0 at hi
  linarith

end Poincare.Parabolic
