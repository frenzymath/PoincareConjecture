import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.OppositeSegments
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Sequences















set_option autoImplicit false

open Filter Set
open scoped Topology

namespace Poincare.AncientVolume.Splitting


noncomputable def vertexComparisonCosine {X : Type*} [MetricSpace X]
    (p x y : X) : ℝ :=
  (dist p x ^ 2 + dist x y ^ 2 - dist p y ^ 2) / (2 * dist p x * dist x y)

private theorem comparison_cosine_le_of_triangle
    {a b d c q δ : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hq : 0 ≤ q) (hδ : 0 ≤ δ)
    (hlower : b - a ≤ d) (hupper : d ≤ a + b)
    (hfar : a * (1 + δ) ≤ δ * b)
    (hside : d ^ 2 ≤ a ^ 2 + b ^ 2 - 2 * a * b * q)
    (hcosine : a ^ 2 + d ^ 2 - 2 * a * d * c = b ^ 2) :
    c ≤ δ - (1 - δ) * q := by
  have hsmall : a ≤ δ * d := by
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hlower)]
  have hfar' : (1 - δ) * d ≤ b := by linarith
  have hprod := mul_le_mul_of_nonneg_right hfar' hq
  have hbound : d * c ≤ a - b * q := by nlinarith
  have hscaled : d * c ≤ d * (δ - (1 - δ) * q) := by nlinarith
  nlinarith



theorem exists_farther_vertices_of_convergent_directions
    {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : X) (x : ℕ → X) (v : ℕ → E) {vlim : E}
    (hx : ∀ i, 0 < dist p (x i))
    (hescape : Tendsto (fun i => dist p (x i)) atTop atTop)
    (hv : Tendsto v atTop (𝓝 vlim)) (hvlim : ‖vlim‖ = 1)
    (hhinge : ∀ i j, dist (x i) (x j) ^ 2 ≤
      dist p (x i) ^ 2 + dist p (x j) ^ 2 -
        2 * dist p (x i) * dist p (x j) * inner ℝ (v i) (v j)) :
    ∃ m : ℕ → ℕ,
      (∀ i, i ≤ m i) ∧
      (∀ i, dist p (x i) * ((i : ℝ) + 2) + 1 ≤ dist p (x (m i))) ∧
      Tendsto (fun i => vertexComparisonCosine p (x i) (x (m i))) atTop (𝓝 (-1)) := by
  have hex (i : ℕ) : ∃ j, i ≤ j ∧
      dist p (x i) * ((i : ℝ) + 2) + 1 ≤ dist p (x j) :=
    ((eventually_ge_atTop i).and
      (hescape.eventually_ge_atTop (dist p (x i) * ((i : ℝ) + 2) + 1))).exists
  choose m hm hfar using hex
  have hmtop : Tendsto m atTop atTop := tendsto_atTop_mono hm tendsto_id
  let q : ℕ → ℝ := fun i => inner ℝ (v i) (v (m i))
  have hq : Tendsto q atTop (𝓝 1) := by
    simpa only [q, Function.comp_def, real_inner_self_eq_norm_sq, hvlim, one_pow] using
      hv.inner (𝕜 := ℝ) (hv.comp hmtop)
  let δ : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 1)
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hpositive (i : ℕ) : 0 < dist (x i) (x (m i)) := by
    have htri := dist_triangle p (x i) (x (m i))
    have hn := mul_nonneg (hx i).le (Nat.cast_nonneg i : 0 ≤ (i : ℝ))
    nlinarith [hfar i, hx i]
  have hlower (i : ℕ) : -1 ≤ vertexComparisonCosine p (x i) (x (m i)) := by
    rw [vertexComparisonCosine,
      le_div_iff₀ (mul_pos (mul_pos (by norm_num) (hx i)) (hpositive i))]
    have htri := dist_triangle p (x i) (x (m i))
    have hs := pow_le_pow_left₀ dist_nonneg htri 2
    nlinarith
  have hupper : ∀ᶠ i in atTop,
      vertexComparisonCosine p (x i) (x (m i)) ≤ δ i - (1 - δ i) * q i := by
    filter_upwards [hq.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with i hi
    have hn : 0 < (i : ℝ) + 1 := by positivity
    have hδi : 0 ≤ δ i := by dsimp only [δ]; positivity
    have ht1 := dist_triangle p (x i) (x (m i))
    have ht2 := dist_triangle (x i) p (x (m i))
    rw [dist_comm (x i) p] at ht2
    apply comparison_cosine_le_of_triangle (hx i) (hpositive i) hi.le hδi
      (by linarith) ht2 ?_ (hhinge i (m i)) ?_
    · dsimp only [δ]
      have heq : dist p (x i) * (1 + 1 / ((i : ℝ) + 1)) =
          dist p (x i) * ((i : ℝ) + 2) / ((i : ℝ) + 1) := by
        field_simp
        ring
      rw [heq, div_mul_eq_mul_div, one_mul, div_le_div_iff_of_pos_right hn]
      nlinarith [hfar i]
    · dsimp only [vertexComparisonCosine]
      field_simp [(hx i).ne', (hpositive i).ne']
      ring
  have hbound : Tendsto (fun i => δ i - (1 - δ i) * q i) atTop (𝓝 (-1)) := by
    simpa using hδ.sub ((tendsto_const_nhds.sub hδ).mul hq)
  exact ⟨m, hm, hfar, tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbound (Eventually.of_forall hlower) hupper⟩



theorem exists_farther_vertices_of_unit_directions
    {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (p : X) (x : ℕ → X) (v : ℕ → E)
    (hx : ∀ i, 0 < dist p (x i))
    (hescape : Tendsto (fun i => dist p (x i)) atTop atTop)
    (hv : ∀ i, ‖v i‖ = 1)
    (hhinge : ∀ i j, dist (x i) (x j) ^ 2 ≤
      dist p (x i) ^ 2 + dist p (x j) ^ 2 -
        2 * dist p (x i) * dist p (x j) * inner ℝ (v i) (v j)) :
    ∃ s m : ℕ → ℕ, StrictMono s ∧
      (∀ i, i ≤ m i) ∧
      (∀ i, dist p (x (s i)) * ((i : ℝ) + 2) + 1 ≤ dist p (x (s (m i)))) ∧
      Tendsto (fun i => vertexComparisonCosine p (x (s i)) (x (s (m i))))
        atTop (𝓝 (-1)) := by
  obtain ⟨vlim, hvlim, s, hs, hvs⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq
    (show ∀ i, v i ∈ Metric.sphere (0 : E) 1 by simpa using hv)
  have hnorm : ‖vlim‖ = 1 := by simpa using hvlim
  obtain ⟨m, hm, hfar, hangle⟩ := exists_farther_vertices_of_convergent_directions
    p (x ∘ s) (v ∘ s) (fun i => hx (s i)) (hescape.comp hs.tendsto_atTop)
    hvs hnorm (fun i j => hhinge (s i) (s j))
  exact ⟨s, m, hs, hm, hfar, hangle⟩

end Poincare.AncientVolume.Splitting
