import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerBoundaryEquicontinuity
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology

universe u

namespace PoincareConjecture

private theorem m65CircleMaps_compact_closure (f : ℕ → C(LoopCircle, LoopCircle))
    (hf : Equicontinuous (fun n z => f n z)) : IsCompact (closure (range f)) := by
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F := fun v : C(LoopCircle, LoopCircle) => (v : LoopCircle → LoopCircle))
    (𝔖 := {K | IsCompact K}) (fun _ h => h)
    (show Topology.IsClosedEmbedding (ContinuousMap.toUniformOnFunIsCompact :
      C(LoopCircle, LoopCircle) →
        UniformOnFun LoopCircle LoopCircle {K | IsCompact K}) from
      ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, by
        rw [ContinuousMap.range_toUniformOnFunIsCompact]
        exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith⟩)
  · intro K _hK
    have heq : Equicontinuous (fun v : range f => (v.val : LoopCircle → LoopCircle)) := by
      intro x V hV
      filter_upwards [hf x V hV] with y hy v
      obtain ⟨n, hn⟩ := v.property
      simpa only [← hn] using hy n
    exact heq.equicontinuousOn K
  · intro K _hK x _hx
    exact ⟨univ, isCompact_univ, fun _ _ => mem_univ _⟩

theorem m65NormalizedWeakDisks_boundary_subsequence
    {M : Type u} [TopologicalSpace M] {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : ℕ → M65WeakDisk e γ) (he : Continuous e) (hγ : Continuous γ)
    (hJordan : Function.Injective (e ∘ γ))
    {a b c : LoopCircle} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpin : ∀ n, (F n).Normalized a b c) (B : ℝ)
    (hB : ∀ n, ‖(F n).derivative 0‖ ^ 2 + ‖(F n).derivative 1‖ ^ 2 ≤ B) :
    ∃ (σ : ℕ → ℕ) (β : C(LoopCircle, LoopCircle)), StrictMono σ ∧
      Tendsto (fun n => (F (σ n)).parameter) atTop (𝓝 β) ∧
      M65WeakCircleParameter β ∧
      β ⟨orthonormalBasisOneI.repr 1, by simp⟩ = a ∧
      β ⟨orthonormalBasisOneI.repr (-1), by simp⟩ = b ∧
      (β ⟨orthonormalBasisOneI.repr I, by simp⟩ = c ∨
        β ⟨orthonormalBasisOneI.repr (-I), by simp⟩ = c) := by
  let f := fun n => (F n).parameter
  have hc := m65CircleMaps_compact_closure f
    (m65NormalizedWeakDisks_boundary_equicontinuous F he hγ hJordan hab hac hbc hpin B hB)
  have : Filter.IsCountablyGenerated (uniformity C(LoopCircle, LoopCircle)) := inferInstance
  have : FirstCountableTopology C(LoopCircle, LoopCircle) :=
    UniformSpace.firstCountableTopology _
  obtain ⟨β, _hβ, σ, hσ, hlim⟩ := hc.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  refine ⟨σ, β, hσ, hlim, ?_, ?_⟩
  · exact isClosed_closure.mem_of_tendsto hlim
      (Eventually.of_forall fun n => (F (σ n)).weakly_monotone)
  · let p : LoopCircle := ⟨orthonormalBasisOneI.repr 1, by simp⟩
    let n : LoopCircle := ⟨orthonormalBasisOneI.repr (-1), by simp⟩
    let ip : LoopCircle := ⟨orthonormalBasisOneI.repr I, by simp⟩
    let im : LoopCircle := ⟨orthonormalBasisOneI.repr (-I), by simp⟩
    have hclosed : IsClosed {v : C(LoopCircle, LoopCircle) |
        v p = a ∧ v n = b ∧ (v ip = c ∨ v im = c)} :=
      (isClosed_eq (continuous_eval_const p) continuous_const).inter
        ((isClosed_eq (continuous_eval_const n) continuous_const).inter
          ((isClosed_eq (continuous_eval_const ip) continuous_const).union
            (isClosed_eq (continuous_eval_const im) continuous_const)))
    exact hclosed.mem_of_tendsto hlim (Eventually.of_forall fun k => hpin (σ k))

theorem m65AngularTrace_tendsto_of_continuous
    (f : ℕ → C(LoopCircle, ℝ)) (f0 : C(LoopCircle, ℝ))
    (b : ℕ → Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi)))
    (b0 : Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi)))
    (hb : ∀ n, b n =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
      fun t => f n (m65LoopAngular t))
    (hb0 : b0 =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
      fun t => f0 (m65LoopAngular t))
    (hf : Tendsto f atTop (𝓝 f0)) : Tendsto b atTop (𝓝 b0) := by
  let mu : Measure ℝ := volume.restrict (Icc (-Real.pi) Real.pi)
  have hbounded : Bornology.IsBounded (range f) := Metric.isBounded_range_of_tendsto f hf
  obtain ⟨C, hC⟩ := hbounded.exists_norm_le
  let D := max C ‖f0‖
  have hD : 0 ≤ D := (norm_nonneg f0).trans (le_max_right _ _)
  have hfn (n : ℕ) (z : LoopCircle) : ‖f n z‖ ≤ D :=
    ((f n).norm_coe_le_norm z).trans ((hC _ (mem_range_self n)).trans (le_max_left _ _))
  have hf0 (z : LoopCircle) : ‖f0 z‖ ≤ D :=
    (f0.norm_coe_le_norm z).trans (le_max_right _ _)
  let err (n : ℕ) (t : ℝ) := ‖f n (m65LoopAngular t) - f0 (m65LoopAngular t)‖ ^ 2
  have hmeas (n : ℕ) : AEStronglyMeasurable (err n) mu :=
    (((f n).continuous.comp m65LoopAngular_continuous_surjective.1).sub
      (f0.continuous.comp m65LoopAngular_continuous_surjective.1)).norm.pow 2
      |>.aestronglyMeasurable
  have hmajor : Integrable (fun _ : ℝ => (2 * D) ^ 2) mu := integrable_const _
  have hbound (n : ℕ) : ∀ᵐ t ∂mu, ‖err n t‖ ≤ (2 * D) ^ 2 := by
    apply ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    exact (norm_sub_le _ _).trans (by
      linarith [hfn n (m65LoopAngular t), hf0 (m65LoopAngular t)])
  have hlim : ∀ᵐ t ∂mu, Tendsto (fun n => err n t) atTop (𝓝 0) := by
    apply ae_of_all
    intro t
    have hpoint := ((continuous_eval_const (m65LoopAngular t)).tendsto f0).comp hf
    simpa only [err, Function.comp_apply, sub_self, norm_zero,
      zero_pow (by decide : 2 ≠ 0)] using
      (hpoint.sub (tendsto_const_nhds (x := f0 (m65LoopAngular t)))).norm.pow 2
  have hint := tendsto_integral_of_dominated_convergence _ hmeas hmajor hbound hlim
  simp only [integral_zero] at hint
  have heq (n : ℕ) : ‖b n - b0‖ ^ 2 = ∫ t, err n t ∂mu := by
    rw [Lp.norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (b n) b0, hb n, hb0] with t ht hn h0
    rw [ht, Pi.sub_apply, hn, h0]
  have hsq : Tendsto (fun n => ‖b n - b0‖ ^ 2) atTop (𝓝 0) := by
    simpa only [heq] using hint
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsq.sqrt

end PoincareConjecture
