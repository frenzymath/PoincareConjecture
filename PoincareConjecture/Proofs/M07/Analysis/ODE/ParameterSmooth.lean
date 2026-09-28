import PoincareConjecture.Proofs.M07.Analysis.ODE.ParameterExistence
import PoincareConjecture.Proofs.M07.Analysis.ODE.ParameterImplicit









noncomputable section

open Set Filter Function Metric
open scoped Topology ContDiff NNReal

namespace Poincare.ODE.Parameter

open Poincare.ODE.Parameter

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F]

theorem exists_local_flow_contDiffAt (f : F → F) (hf : ContDiff ℝ ∞ f) (z0 : F) :
    ∃ (r epsilon T : ℝ) (Z : F → ℝ → F) (L : ℝ≥0)
      (sigma : F → C(Set.Icc (0 : ℝ) T, F)) (_hT : 0 < T),
      0 < r ∧ 0 < epsilon ∧ T < epsilon ∧
      (∀ z ∈ closedBall z0 r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-epsilon) epsilon,
          HasDerivWithinAt (Z z) (f (Z z t)) (Icc (-epsilon) epsilon) t) ∧
        (∀ t ∈ Icc (-epsilon) epsilon, Z z t ∈ ball z0 1)) ∧
      (∀ t ∈ Icc (-epsilon) epsilon,
        LipschitzOnWith L (Z · t) (closedBall z0 r)) ∧
      (∀ z ∈ closedBall z0 r, ∀ t : Set.Icc (0 : ℝ) T,
        sigma z t = Z z t.1) ∧
      (∀ x ∈ ball z0 r, ContDiffAt ℝ ∞ sigma x) := by
  classical
  have hf1 : ContDiffAt ℝ 1 f z0 := hf.contDiffAt.of_le (by norm_num)
  have hdf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_closedBall z0 1).exists_bound_of_continuousOn
    hdf.continuousOn
  have hC0 : 0 ≤ C :=
    le_trans (norm_nonneg (fderiv ℝ f z0)) (hC z0 (mem_closedBall_self zero_le_one))
  obtain ⟨r, epsilon, Z, L, hr, hepsilon, hflow, hLip⟩ :=
    Poincare.ODE.Parameter.exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt
      hf1 (ball_mem_nhds z0 one_pos)
  set T : ℝ := min (epsilon / 2) (1 / (2 * (C + 1))) with hTdef
  have hT : 0 < T := lt_min (by positivity) (by positivity)
  have hTepsilon : T < epsilon :=
    (min_le_left _ _).trans_lt (half_lt_self hepsilon)
  have hTC : T * C < 1 := by
    have h1 : T ≤ 1 / (2 * (C + 1)) := min_le_right _ _
    have h2 : (0 : ℝ) < 2 * (C + 1) := by positivity
    have h3 : T * C ≤ (1 / (2 * (C + 1))) * C :=
      mul_le_mul_of_nonneg_right h1 hC0
    have h4 : (1 / (2 * (C + 1))) * (2 * (C + 1)) = 1 :=
      one_div_mul_cancel (ne_of_gt h2)
    nlinarith
  have hIccT : Icc (0 : ℝ) T ⊆ Icc (-epsilon) epsilon := fun t ht =>
    ⟨le_trans (neg_nonpos.mpr hepsilon.le) ht.1, ht.2.trans hTepsilon.le⟩
  set sigma : F → C(Set.Icc (0 : ℝ) T, F) := fun x =>
    if hx : x ∈ closedBall z0 r then
      ⟨fun t => Z x t.1, by
        have hcont : ContinuousOn (Z x) (Icc (-epsilon) epsilon) := fun s hs =>
          ((hflow x hx).2.1 s hs).continuousWithinAt
        exact hcont.comp_continuous continuous_subtype_val fun t => hIccT t.2⟩
    else ContinuousMap.const _ z0 with hsigmaDef
  have hsigmaBall : ∀ z ∈ closedBall z0 r, ∀ t : Set.Icc (0 : ℝ) T,
      sigma z t = Z z t.1 := by
    intro z hz t
    simp only [hsigmaDef, dif_pos hz]
    rfl
  refine ⟨r, epsilon, T, Z, L, sigma, hT, hr, hepsilon, hTepsilon,
    hflow, hLip, hsigmaBall, ?_⟩
  intro x0 hx0
  have hx0c : x0 ∈ closedBall z0 r := ball_subset_closedBall hx0
  have hconf : ∀ t : Set.Icc (0 : ℝ) T, sigma x0 t ∈ ball z0 1 := fun t => by
    rw [hsigmaBall x0 hx0c t]
    exact (hflow x0 hx0c).2.2 t.1 (hIccT t.2)
  set A0 : C(Set.Icc (0 : ℝ) T, F →L[ℝ] F) :=
    ⟨fun t => fderiv ℝ f (sigma x0 t), hdf.comp (sigma x0).continuous⟩ with hA0def
  have hA0 : ∀ t : Set.Icc (0 : ℝ) T, A0 t = fderiv ℝ f (sigma x0 t) :=
    fun _ => rfl
  have hA0C : ‖A0‖ ≤ C := (ContinuousMap.norm_le _ hC0).mpr fun t =>
    hC _ (ball_subset_closedBall (hconf t))
  have hTL : T * ‖A0‖ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hA0C hT.le) hTC
  have hsigmac : ContinuousAt sigma x0 := by
    have hlips : LipschitzOnWith L sigma (closedBall z0 r) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [ContinuousMap.dist_le (mul_nonneg L.coe_nonneg dist_nonneg)]
      intro t
      rw [hsigmaBall x hx t, hsigmaBall y hy t]
      exact (hLip t.1 (hIccT t.2)).dist_le_mul x hx y hy
    exact (hlips.continuousOn.continuousWithinAt hx0c).continuousAt
      (mem_of_superset (isOpen_ball.mem_nhds hx0) ball_subset_closedBall)
  have hsigmaResidual :
      ∀ᶠ x in 𝓝 x0, picardResidual hT.le f (x, sigma x) = 0 := by
    filter_upwards [isOpen_ball.mem_nhds hx0] with x hx
    have hxc : x ∈ closedBall z0 r := ball_subset_closedBall hx
    obtain ⟨hzero, hderiv, _⟩ := hflow x hxc
    refine picardResidual_eq_zero_of_hasDerivWithinAt hT
      hf.continuous.continuousOn hzero (fun t _ => mem_univ _) ?_
      (sigma x) (fun t => hsigmaBall x hxc t)
    intro t ht
    exact (hderiv t (hIccT ht)).mono hIccT
  exact contDiffAt_flow_of_picardResidual hT hf hA0 hTL rfl hsigmac hsigmaResidual

end Poincare.ODE.Parameter
