import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Depth
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Cutoff.DepthProfile

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff ENNReal NNReal

universe u

namespace PoincareConjecture

theorem exists_centered_depth_profile (s0 : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧
      support φ ⊆ Icc (s0 - 5 * δ / 8) (s0 + δ / 8) ∧
      φ s0 = 1 ∧ ∀ s, |deriv φ s| ≤ (2 * neckDepthConstant) / δ := by
  obtain ⟨ψ, hψ, hsψ, _, hval, hbound⟩ :=
    exists_half_neck_profile.choose_spec.2 1 zero_lt_one 1 (by norm_num)
  change ∀ s, |deriv ψ s| ≤ neckDepthConstant * 1 at hbound
  norm_num at hsψ hval hbound
  let φ : ℝ → ℝ := fun s => ψ (2 * (s - s0) / δ + 1 / 2)
  refine ⟨φ, hψ.comp (by fun_prop), ?_, ?_, ?_⟩
  · intro s hs
    have hp : 2 * (s - s0) / δ + 1 / 2 ∈ Icc (-(3 / 4)) (3 / 4) := hsψ _ hs
    have hl : -(5 / 4 : ℝ) ≤ 2 * (s - s0) / δ := by linarith [hp.1]
    have hu : 2 * (s - s0) / δ ≤ (1 / 4 : ℝ) := by linarith [hp.2]
    have hl' := (le_div_iff₀ hδ).mp hl
    have hu' := (div_le_iff₀ hδ).mp hu
    constructor <;> linarith
  · simpa only [φ, sub_self, mul_zero, zero_div, zero_add] using hval
  · intro s
    have hd : deriv φ s = deriv ψ (2 * (s - s0) / δ + 1 / 2) * (2 / δ) := by
      simpa only [φ, Function.comp_def, mul_one, id_eq] using
        ((hψ.differentiable (by simp) _).hasDerivAt.comp s
          (((((hasDerivAt_id s).sub_const s0).const_mul 2).div_const δ).add_const
            (1 / 2))).deriv
    rw [hd, abs_mul, abs_of_pos (div_pos (by norm_num) hδ)]
    calc
      _ ≤ neckDepthConstant * (2 / δ) :=
        mul_le_mul_of_nonneg_right (hbound _) (by positivity)
      _ = _ := by ring

namespace EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem edist_lower_of_not_mem_carrier (N : EpsilonNeck g)
    {x y : M} (hx : x ∈ N.carrier) (hy : y ∉ N.carrier) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) *
      (N.epsilon⁻¹ - |(N.coordinate_inverse x).2|) / (2 * neckDepthConstant)) ≤
      g.edist x y := by
  let s0 := (N.coordinate_inverse x).2
  let δ := N.epsilon⁻¹ - |s0|
  have hδ : 0 < δ := sub_pos.mpr (abs_lt.mpr (N.coordinate_inverse_mem x hx).2)
  obtain ⟨φ, hφ, hs, hval, hbound⟩ := exists_centered_depth_profile s0 hδ
  have ha : -N.epsilon⁻¹ < s0 - 5 * δ / 8 := by
    have heq : δ = N.epsilon⁻¹ - |s0| := rfl
    linarith [neg_abs_le s0]
  have hb : s0 + δ / 8 < N.epsilon⁻¹ := by
    have heq : δ = N.epsilon⁻¹ - |s0| := rfl
    linarith [le_abs_self s0]
  have hfactor : 0 < N.scale * Real.sqrt (1 - N.epsilon) :=
    mul_pos N.scale_pos (Real.sqrt_pos.mpr (by linarith [N.epsilon_lt_half]))
  have hC : 0 < 2 * neckDepthConstant := mul_pos (by norm_num) neckDepthConstant_pos
  let k : ℝ := ((2 * neckDepthConstant) / δ) /
    (N.scale * Real.sqrt (1 - N.epsilon))
  have hk : 0 < k := div_pos (div_pos hC hδ) hfactor
  let K : ℝ≥0 := ⟨k, hk.le⟩
  have hdist := g.edist_le_mul_edist_of_derivative_bound
    ((N.contMDiff_axialCutoff ha hb hφ hs).of_le (by simp))
    (K := K) hk (N.abs_mvfderiv_axialCutoff_le ha hb hφ hs
      (div_pos hC hδ).le hbound) x y
  rw [N.axialCutoff_eq_of_mem φ hx, N.axialCutoff_eq_zero_of_not_mem φ hy,
    hval] at hdist
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal k * g.edist x y := by
    have hK : ENNReal.ofReal k = (K : ℝ≥0∞) := by
      change ENNReal.ofReal (K : ℝ) = (K : ℝ≥0∞)
      exact ENNReal.ofReal_coe_nnreal
    rw [hK]
    simpa only [edist_dist, Real.dist_eq, sub_zero, abs_one,
      ENNReal.ofReal_one] using hdist
  let r := N.scale * Real.sqrt (1 - N.epsilon) * δ / (2 * neckDepthConstant)
  have hr : 0 < r := div_pos (mul_pos hfactor hδ) hC
  have hrk : r * k = 1 := by
    have hsqrt : Real.sqrt (1 - N.epsilon) ≠ 0 :=
      (Real.sqrt_pos.mpr (by linarith [N.epsilon_lt_half])).ne'
    dsimp only [r, k]
    field_simp [hδ.ne', neckDepthConstant_pos.ne', N.scale_pos.ne', hsqrt]
  change ENNReal.ofReal r ≤ g.edist x y
  calc
    _ = ENNReal.ofReal r * 1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal r * (ENNReal.ofReal k * g.edist x y) :=
      mul_le_mul' le_rfl hone
    _ = g.edist x y := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hr.le, hrk, ENNReal.ofReal_one, one_mul]

theorem mem_carrier_of_edist_lt_buffer (N : EpsilonNeck g)
    {x y : M} (hx : x ∈ N.carrier)
    (hxy : g.edist x y < ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) *
      (N.epsilon⁻¹ - |(N.coordinate_inverse x).2|) / (2 * neckDepthConstant))) :
    y ∈ N.carrier := by
  by_contra hy
  exact (not_lt_of_ge (N.edist_lower_of_not_mem_carrier hx hy)) hxy

end EpsilonNeck
end PoincareConjecture
