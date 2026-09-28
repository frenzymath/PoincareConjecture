import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.TangentialTests
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.Analysis.Sobolev.BoundaryExtension

open BoundaryTangential

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

def normalCutoff (n : ℕ) (x : E) : ℝ :=
  Real.smoothTransition (((n : ℝ) + 1) * x 0 - 1)

theorem normalCutoff_smooth (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (normalCutoff (d := d) n) := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun x : E => x 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin d)).contDiff
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul hp).sub contDiff_const)

theorem normalCutoff_norm_le (n : ℕ) (x : E) : ‖normalCutoff n x‖ ≤ 1 := by
  rw [normalCutoff, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem normalCutoff_tsupport (n : ℕ) :
    tsupport (normalCutoff (d := d) n) ⊆ halfSpace d := by
  have hs : tsupport (normalCutoff (d := d) n) ⊆
      {x : E | 1 ≤ ((n : ℝ) + 1) * x 0} := by
    apply closure_minimal ?_
      (isClosed_le continuous_const
        (continuous_const.mul (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous))
    intro x hx
    change 1 ≤ ((n : ℝ) + 1) * x 0
    have hn : ¬ ((n : ℝ) + 1) * x 0 - 1 ≤ 0 := by
      intro h
      exact hx (Real.smoothTransition.zero_of_nonpos h)
    linarith
  intro x hx
  have hx' := hs hx
  change 1 ≤ ((n : ℝ) + 1) * x 0 at hx'
  change 0 < x 0
  by_contra! h
  have hmul := mul_nonpos_of_nonneg_of_nonpos
    (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) h
  linarith

theorem normalCutoff_fderiv (n : ℕ) (x : E) :
    fderiv ℝ (normalCutoff n) x =
      deriv Real.smoothTransition (((n : ℝ) + 1) * x 0 - 1) •
        (((n : ℝ) + 1) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin d)) := by
  have hi := (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin d)).hasFDerivAt
    (x := x)).const_mul ((n : ℝ) + 1)).sub_const 1
  have ho := (Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable_one
  exact ((ho _).hasDerivAt.comp_hasFDerivAt x hi).fderiv

theorem normalCutoff_partial (n : ℕ) (k : Fin d) (hk : k ≠ 0) (x : E) :
    fderiv ℝ (normalCutoff n) x (EuclideanSpace.single k 1) = 0 := by
  simp [normalCutoff_fderiv, hk.symm]

theorem normalCutoff_normal_partial (n : ℕ) (x : E) :
    fderiv ℝ (normalCutoff n) x (EuclideanSpace.single 0 1) =
      deriv Real.smoothTransition (((n : ℝ) + 1) * x 0 - 1) * ((n : ℝ) + 1) := by
  simp [normalCutoff_fderiv]

theorem normalCutoff_eventually_eq_one {x : E} (hx : x ∈ halfSpace d) :
    ∀ᶠ n : ℕ in atTop, normalCutoff n x = 1 := by
  change 0 < x 0 at hx
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / x 0)
  have hN' : 2 < (N : ℝ) * x 0 := (div_lt_iff₀ hx).mp hN
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  apply Real.smoothTransition.one_of_one_le
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

theorem normalCutoff_tendsto {x : E} (hx : x ∈ halfSpace d) :
    Tendsto (fun n => normalCutoff n x) atTop (𝓝 1) := by
  exact tendsto_const_nhds.congr'
    ((normalCutoff_eventually_eq_one hx).mono fun _ hn => hn.symm)

private theorem smoothTransition_deriv_zero_of_neg {s : ℝ} (hs : s < 0) :
    deriv Real.smoothTransition s = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
    filter_upwards [gt_mem_nhds hs] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  simpa using h.deriv_eq

private theorem smoothTransition_deriv_zero_of_one_lt {s : ℝ} (hs : 1 < s) :
    deriv Real.smoothTransition s = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
    filter_upwards [lt_mem_nhds hs] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  simpa using h.deriv_eq

private theorem smoothTransition_deriv_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, ‖deriv Real.smoothTransition s‖ ≤ C := by
  have hs : tsupport (deriv Real.smoothTransition) ⊆ Icc (0 : ℝ) 1 := by
    apply closure_minimal ?_ isClosed_Icc
    intro s hs
    constructor
    · by_contra! h
      exact hs (smoothTransition_deriv_zero_of_neg h)
    · by_contra! h
      exact hs (smoothTransition_deriv_zero_of_one_lt h)
  have hc : HasCompactSupport (deriv Real.smoothTransition) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hs
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := (1 : ℕ∞))).continuous_deriv_one
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hcont
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

theorem normalCutoff_fderiv_eq_zero_of_two_lt (n : ℕ) (x : E)
    (hx : 2 < ((n : ℝ) + 1) * x 0) : fderiv ℝ (normalCutoff n) x = 0 := by
  rw [normalCutoff_fderiv,
    smoothTransition_deriv_zero_of_one_lt (by linarith), zero_smul]

theorem normalCutoff_fderiv_eventually_eq_zero {x : E} (hx : x ∈ halfSpace d) :
    ∀ᶠ n : ℕ in atTop, fderiv ℝ (normalCutoff n) x = 0 := by
  change 0 < x 0 at hx
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / x 0)
  have hN' : 2 < (N : ℝ) * x 0 := (div_lt_iff₀ hx).mp hN
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  apply normalCutoff_fderiv_eq_zero_of_two_lt
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

theorem exists_normalCutoff_normal_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : E), 0 ≤ x 0 →
      x 0 * ‖fderiv ℝ (normalCutoff n) x (EuclideanSpace.single 0 1)‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := smoothTransition_deriv_bounded
  refine ⟨2 * C, mul_nonneg (by norm_num) hC0, ?_⟩
  intro n x hx
  by_cases hsmall : ((n : ℝ) + 1) * x 0 ≤ 2
  · rw [normalCutoff_normal_partial, norm_mul,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    calc
      _ = (((n : ℝ) + 1) * x 0) *
          ‖deriv Real.smoothTransition (((n : ℝ) + 1) * x 0 - 1)‖ := by ring
      _ ≤ (((n : ℝ) + 1) * x 0) * C :=
        mul_le_mul_of_nonneg_left (hC _) (mul_nonneg (by positivity) hx)
      _ ≤ 2 * C := mul_le_mul_of_nonneg_right hsmall hC0
  · rw [normalCutoff_fderiv_eq_zero_of_two_lt n x (lt_of_not_ge hsmall)]
    simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC0

end Poincare.Analysis.Sobolev.BoundaryExtension
