import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Sequences

set_option autoImplicit false

open Set Filter
open scoped Topology

theorem norm_frame_le_of_quadratic_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B : E →L[ℝ] E →L[ℝ] ℝ} {c : ℝ} (hc : 0 < c)
    (hB : ∀ v, c * ‖v‖ ^ 2 ≤ B v v) (A : E →L[ℝ] E)
    (hA : ∀ v w, B (A v) (A w) = inner ℝ v w) :
    ‖A‖ ≤ Real.sqrt c⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  have hquad := hB (A v)
  rw [hA, real_inner_self_eq_norm_sq] at hquad
  have hsq : ‖A v‖ ^ 2 ≤ c⁻¹ * ‖v‖ ^ 2 := by
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hquad)
  calc
    ‖A v‖ = Real.sqrt (‖A v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (c⁻¹ * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt c⁻¹ * ‖v‖ := by
      rw [Real.sqrt_mul (inv_pos.mpr hc).le, Real.sqrt_sq (norm_nonneg v)]

theorem exists_subseq_orthonormal_frame_of_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {B : ℕ → E →L[ℝ] E →L[ℝ] ℝ} {B₀ : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : Tendsto B atTop (𝓝 B₀)) (L : ℕ → E →L[ℝ] E)
    (hframe : ∀ i v w, B i (L i v) (L i w) = inner ℝ v w)
    {C : ℝ} (hbound : ∀ i, ‖L i‖ ≤ C) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ L₀ : E ≃L[ℝ] E,
      Tendsto (fun i => L (φ i)) atTop (𝓝 L₀.toContinuousLinearMap) ∧
      ∀ v w, B₀ (L₀ v) (L₀ w) = inner ℝ v w := by
  obtain ⟨A, _, φ, hφ, hL⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) C).tendsto_subseq
    (fun i => by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound i)
  have hA (v w : E) : B₀ (A v) (A w) = inner ℝ v w := by
    have hc : Continuous
        (fun z : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) =>
          z.1 (z.2 v) (z.2 w)) :=
      (continuous_fst.clm_apply (continuous_snd.clm_apply continuous_const)).clm_apply
        (continuous_snd.clm_apply continuous_const)
    have hval := hc.continuousAt.tendsto.comp
      ((hB.comp hφ.tendsto_atTop).prodMk_nhds hL)
    exact tendsto_nhds_unique hval (by simpa only [Function.comp_def, hframe] using
      (tendsto_const_nhds (x := inner ℝ v w) :
        Tendsto (fun _ : ℕ => inner ℝ v w) atTop (𝓝 (inner ℝ v w))))
  have hinj : Function.Injective A := by
    intro v w hvw
    have hzero : inner ℝ (v - w) (v - w) = 0 := by
      rw [← hA, map_sub, hvw, sub_self, map_zero]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
  have hbij : Function.Bijective A :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩
  exact ⟨φ, hφ, ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2), hL, hA⟩

theorem exists_subseq_orthonormal_frame_of_eventual_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {B : ℕ → E →L[ℝ] E →L[ℝ] ℝ} {B₀ : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : Tendsto B atTop (𝓝 B₀)) (L : ℕ → E →L[ℝ] E)
    (hframe : ∀ i v w, B i (L i v) (L i w) = inner ℝ v w)
    {C : ℝ} (hbound : ∀ᶠ i in atTop, ‖L i‖ ≤ C) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ L₀ : E ≃L[ℝ] E,
      Tendsto (fun i => L (φ i)) atTop (𝓝 L₀.toContinuousLinearMap) ∧
      ∀ v w, B₀ (L₀ v) (L₀ w) = inner ℝ v w := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  have hshift : StrictMono (fun i : ℕ => i + N) := fun _ _ h => Nat.add_lt_add_right h N
  obtain ⟨φ, hφ, L₀, hL₀, hframe₀⟩ := exists_subseq_orthonormal_frame_of_bound
    (hB.comp hshift.tendsto_atTop) (fun i => L (i + N))
    (fun i => hframe (i + N)) (fun i => hN (i + N) (by omega))
  exact ⟨fun i => φ i + N, hshift.comp hφ, L₀, hL₀, hframe₀⟩
