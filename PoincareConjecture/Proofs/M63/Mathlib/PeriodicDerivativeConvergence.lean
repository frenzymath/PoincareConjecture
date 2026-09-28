import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Instances.AddCircle.Real

set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

universe u

namespace PoincareConjecture.M63

theorem exists_periodic_derivative_limit
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ} [Fact (0 < P)]
    (f df : ℕ → C(AddCircle P, E)) (f0 : C(AddCircle P, E))
    (hder : ∀ (j : ℕ) (x : ℝ), HasDerivAt
      (fun y : ℝ => f j (y : AddCircle P)) (df j (x : AddCircle P)) x)
    {L : ℝ≥0} (hlip : ∀ j, LipschitzWith L (fun x : ℝ => df j (x : AddCircle P)))
    (hlim : Tendsto f atTop (𝓝 f0)) :
    ∃ g : C(AddCircle P, E), Tendsto df atTop (𝓝 g) ∧
      ∀ x : ℝ, HasDerivAt (fun y : ℝ => f0 (y : AddCircle P))
        (g (x : AddCircle P)) x := by
  have hinc (j : ℕ) (x r : ℝ) (hr : 0 < r) :
      ‖f j ((x + r : ℝ) : AddCircle P) - f j (x : AddCircle P) -
        r • df j (x : AddCircle P)‖ ≤ (L : ℝ) * r ^ 2 := by
    let G : ℝ → E := fun y => f j (y : AddCircle P) - y • df j (x : AddCircle P)
    have hG (y : ℝ) : HasDerivAt G
        (df j (y : AddCircle P) - df j (x : AddCircle P)) y := by
      simpa only [G, id_eq, one_smul] using
        (hder j y).fun_sub ((hasDerivAt_id y).smul_const (df j (x : AddCircle P)))
    have hbound (y : ℝ) (hy : y ∈ Ico x (x + r)) :
        ‖df j (y : AddCircle P) - df j (x : AddCircle P)‖ ≤ (L : ℝ) * r := by
      have h := (hlip j).dist_le_mul y x
      rw [dist_eq_norm, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy.1)] at h
      exact h.trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) L.coe_nonneg)
    have hseg := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun y (_hy : y ∈ Icc x (x + r)) => (hG y).hasDerivWithinAt) hbound
      (x + r) ⟨by linarith, le_rfl⟩
    have heq : G (x + r) - G x =
        f j ((x + r : ℝ) : AddCircle P) - f j (x : AddCircle P) -
          r • df j (x : AddCircle P) := by
      dsimp only [G]
      rw [add_smul]
      abel
    rw [heq] at hseg
    convert hseg using 1
    ring
  have hdiff (j k : ℕ) (r : ℝ) (hr : 0 < r) :
      ‖df j - df k‖ ≤ (2 * ‖f j - f k‖ + 2 * (L : ℝ) * r ^ 2) / r := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    let A : ℕ → E := fun i =>
      f i ((x + r : ℝ) : AddCircle P) - f i (x : AddCircle P) -
        r • df i (x : AddCircle P)
    have heq : r • (df j (x : AddCircle P) - df k (x : AddCircle P)) =
        (f j ((x + r : ℝ) : AddCircle P) - f k ((x + r : ℝ) : AddCircle P)) -
          (f j (x : AddCircle P) - f k (x : AddCircle P)) - A j + A k := by
      dsimp only [A]
      rw [smul_sub]
      abel
    have hj := hinc j x r hr
    have hk := hinc k x r hr
    have hplus := ContinuousMap.norm_coe_le_norm (f j - f k) ((x + r : ℝ) : AddCircle P)
    have hzero := ContinuousMap.norm_coe_le_norm (f j - f k) (x : AddCircle P)
    have htri : ‖r • (df j (x : AddCircle P) - df k (x : AddCircle P))‖ ≤
        2 * ‖f j - f k‖ + 2 * (L : ℝ) * r ^ 2 := by
      rw [heq]
      calc
        _ ≤ ‖(f j ((x + r : ℝ) : AddCircle P) - f k ((x + r : ℝ) : AddCircle P)) -
            (f j (x : AddCircle P) - f k (x : AddCircle P)) - A j‖ + ‖A k‖ :=
          norm_add_le _ _
        _ ≤ (‖f j ((x + r : ℝ) : AddCircle P) - f k ((x + r : ℝ) : AddCircle P)‖ +
            ‖f j (x : AddCircle P) - f k (x : AddCircle P)‖ + ‖A j‖) + ‖A k‖ :=
          add_le_add (norm_sub_le _ _ |>.trans
            (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl
        _ ≤ _ := by
          change ‖A j‖ ≤ (L : ℝ) * r ^ 2 at hj
          change ‖A k‖ ≤ (L : ℝ) * r ^ 2 at hk
          change ‖f j ((x + r : ℝ) : AddCircle P) -
            f k ((x + r : ℝ) : AddCircle P)‖ ≤ ‖f j - f k‖ at hplus
          change ‖f j (x : AddCircle P) - f k (x : AddCircle P)‖ ≤ ‖f j - f k‖ at hzero
          linarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr] at htri
    exact (le_div_iff₀ hr).mpr (by simpa only [ContinuousMap.sub_apply, mul_comm] using htri)
  have hdc : CauchySeq df := by
    apply Metric.cauchySeq_iff.mpr
    intro eps heps
    let r : ℝ := eps / (8 * ((L : ℝ) + 1))
    have hr : 0 < r := by dsimp only [r]; positivity
    have hre : 8 * ((L : ℝ) + 1) * r = eps := by dsimp only [r]; field_simp
    have hsmall : 2 * (L : ℝ) * r < eps / 4 := by nlinarith [L.coe_nonneg]
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq (eps * r / 4) (by positivity)
    refine ⟨N, fun j hj k hk => ?_⟩
    have hval := hN j hj k hk
    rw [dist_eq_norm] at hval ⊢
    apply (hdiff j k r hr).trans_lt
    apply (div_lt_iff₀ hr).mpr
    have hprod := mul_lt_mul_of_pos_right hsmall hr
    nlinarith
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hdc
  refine ⟨g, hg, ?_⟩
  have hdu : TendstoUniformly
      (fun j (x : ℝ) => df j (x : AddCircle P))
      (fun x : ℝ => g (x : AddCircle P)) atTop :=
    (ContinuousMap.tendsto_iff_tendstoUniformly.mp hg).comp
      (fun x : ℝ => (x : AddCircle P))
  have hpoint (x : ℝ) : Tendsto (fun j => f j (x : AddCircle P)) atTop
      (𝓝 (f0 (x : AddCircle P))) :=
    ((continuous_eval_const (x : AddCircle P)).tendsto f0).comp hlim
  exact hasDerivAt_of_tendstoUniformly hdu (Eventually.of_forall hder) hpoint

end PoincareConjecture.M63
