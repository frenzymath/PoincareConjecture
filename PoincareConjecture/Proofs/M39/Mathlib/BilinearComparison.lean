import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open Set
open scoped Topology

namespace ContinuousLinearMap

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_uniform_pos_quadratic_lower
    [FiniteDimensional ℝ E]
    {B : X → E →L[ℝ] E →L[ℝ] ℝ} {K : Set X}
    (hK : IsCompact K) (hB : ContinuousOn B K)
    (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : E, c * ‖v‖ ^ 2 ≤ B x v v := by
  have hcontinuous : ContinuousOn (fun p : X × E => B p.1 p.2 p.2)
      (K ×ˢ Metric.sphere 0 1) :=
    ((hB.comp (continuous_fst.continuousOn : ContinuousOn (Prod.fst : X × E → X)
      (K ×ˢ Metric.sphere 0 1)) (fun _ h => h.1)).clm_apply
      continuousOn_snd).clm_apply continuousOn_snd
  obtain ⟨c, hc, hmin⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_forall_le'
    hcontinuous (a := (0 : ℝ)) (by
      intro p hp
      apply hpos p.1 hp.1
      intro hzero
      simpa [hzero] using hp.2)
  refine ⟨c, hc, fun x hx v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hunit : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : E) 1 := by
    simp [norm_smul, hn]
  have h := mul_le_mul_of_nonneg_left (hmin (x, ‖v‖⁻¹ • v) ⟨hx, hunit⟩)
    (sq_nonneg ‖v‖)
  have hscale : ‖v‖ ^ 2 * B x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = B x v v := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    field_simp
  simpa only [hscale, mul_comm (‖v‖ ^ 2) c] using h

theorem exists_bilinear_norm_le_basis {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ E) :
    ∃ D : ℝ, 0 < D ∧ ∀ (B : E →L[ℝ] E →L[ℝ] ℝ) (e : ℝ),
      0 ≤ e → (∀ i j, ‖B (b i) (b j)‖ ≤ e) → ‖B‖ ≤ D * e := by
  obtain ⟨D₁, hD₁, h₁⟩ := b.exists_opNorm_le (F := E →L[ℝ] ℝ)
  obtain ⟨D₂, hD₂, h₂⟩ := b.exists_opNorm_le (F := ℝ)
  refine ⟨D₁ * D₂, mul_pos hD₁ hD₂, fun B e he hcoeff => ?_⟩
  have hinner : ∀ i, ‖B (b i)‖ ≤ D₂ * e := fun i => h₂ he (hcoeff i)
  simpa only [mul_assoc] using h₁ (mul_nonneg hD₂.le he) hinner

theorem quadratic_le_mul_of_norm_sub_le
    (A B : E →L[ℝ] E →L[ℝ] ℝ) {c k : ℝ} (hk : 1 < k)
    (hlower : ∀ v, c * ‖v‖ ^ 2 ≤ B v v)
    (herror : ‖B - A‖ ≤ c * (k - 1) / k) (v : E) : B v v ≤ k * A v v := by
  have hk0 : 0 < k := zero_lt_one.trans hk
  have hnorm : ‖(B - A) v v‖ ≤ ‖B - A‖ * ‖v‖ ^ 2 := by
    calc
      ‖(B - A) v v‖ ≤ ‖(B - A) v‖ * ‖v‖ := le_opNorm _ _
      _ ≤ (‖B - A‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (le_opNorm _ _) (norm_nonneg v)
      _ = _ := by ring
  have hdiff : B v v - A v v ≤ c * (k - 1) / k * ‖v‖ ^ 2 := by
    exact (le_abs_self _).trans
      (hnorm.trans (mul_le_mul_of_nonneg_right herror (sq_nonneg ‖v‖)))
  have hmul := mul_le_mul_of_nonneg_left hdiff hk0.le
  have hcancel : k * (c * (k - 1) / k * ‖v‖ ^ 2) =
      (k - 1) * (c * ‖v‖ ^ 2) := by field_simp
  rw [hcancel] at hmul
  have hbase := mul_le_mul_of_nonneg_left (hlower v) (sub_pos.mpr hk).le
  nlinarith

theorem eventually_quadratic_le_mul_of_coefficients
    [FiniteDimensional ℝ E] {ι α : Type*} [Finite ι]
    (b : Module.Basis ι ℝ E) {l : Filter α}
    {B : X → E →L[ℝ] E →L[ℝ] ℝ}
    {A : α → X → E →L[ℝ] E →L[ℝ] ℝ} {K : Set X}
    (hK : IsCompact K) (hB : ContinuousOn B K)
    (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < B x v v)
    (hconv : ∀ i j, ∀ e : ℝ, 0 < e →
      ∀ᶠ t in l, ∀ x ∈ K, ‖(B x - A t x) (b i) (b j)‖ ≤ e)
    {k : ℝ} (hk : 1 < k) :
    ∀ᶠ t in l, ∀ x ∈ K, ∀ v : E, B x v v ≤ k * A t x v v := by
  obtain ⟨c, hc, hlower⟩ := exists_uniform_pos_quadratic_lower hK hB hpos
  obtain ⟨D, hD, hnorm⟩ := exists_bilinear_norm_le_basis b
  let e := c * (k - 1) / (k * D)
  have hk0 : 0 < k := zero_lt_one.trans hk
  have he : 0 < e := div_pos (mul_pos hc (sub_pos.mpr hk)) (mul_pos hk0 hD)
  have hall : ∀ᶠ t in l, ∀ i j, ∀ x ∈ K,
      ‖(B x - A t x) (b i) (b j)‖ ≤ e :=
    Filter.eventually_all.mpr (fun i =>
      Filter.eventually_all.mpr (fun j => hconv i j e he))
  filter_upwards [hall] with t ht
  intro x hx v
  apply quadratic_le_mul_of_norm_sub_le (A t x) (B x) hk (hlower x hx)
  have herror := hnorm (B x - A t x) e he.le (fun i j => ht i j x hx)
  have hcancel : D * e = c * (k - 1) / k := by
    dsimp [e]
    field_simp
  exact herror.trans_eq hcancel

end ContinuousLinearMap
