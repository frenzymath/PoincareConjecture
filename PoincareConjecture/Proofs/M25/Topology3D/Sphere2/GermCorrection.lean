import PoincareConjecture.Proofs.M25.Topology3D.Sphere2.SmallPerturbationFamily
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension









set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold Topology NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]




theorem exists_small_derivative_germ_extension {U : Set E} (hU : IsOpen U)
    (h0 : (0 : E) ∈ U) {g : E → E} (hg : ContDiffOn ℝ ∞ g U)
    (hg0 : g 0 = 0) (hd0 : fderiv ℝ g 0 = ContinuousLinearMap.id ℝ E) :
    ∃ r : ℝ, 0 < r ∧ closedBall (0 : E) (2 * r) ⊆ U ∧
      ∃ P : E → E, ContDiff ℝ ∞ P ∧
        (∀ x ∈ closedBall (0 : E) r, P x = g x) ∧
        (∀ x, x ∉ closedBall (0 : E) (2 * r) → P x = x) ∧
        (∀ x, ‖fderiv ℝ P x - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 2 : ℝ)) := by
  let b : ContDiffBump (0 : E) := default
  have hb : ContDiff ℝ ∞ (b : E → ℝ) := b.contDiff
  obtain ⟨B₀, hB₀⟩ := b.hasCompactSupport.isCompact.exists_bound_of_continuousOn
    (hb.continuous_fderiv (by simp)).continuousOn
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hDb (x : E) : ‖fderiv ℝ (b : E → ℝ) x‖ ≤ B := by
    by_cases hx : x ∈ tsupport (b : E → ℝ)
    · exact (hB₀ x hx).trans (le_max_left _ _)
    · rw [fderiv_of_notMem_tsupport ℝ hx, norm_zero]
      exact hB
  let ε : ℝ := 1 / (4 * (1 + 2 * B))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεeq : (1 + 2 * B) * ε = 1 / 4 := by dsimp [ε]; field_simp
  have hc : ContinuousAt (fun x => ‖fderiv ℝ g x - ContinuousLinearMap.id ℝ E‖)
      (0 : E) :=
    (((hg.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt
      (hU.mem_nhds h0)).sub continuousAt_const).norm
  have hsmall : ∀ᶠ x in 𝓝 (0 : E),
      ‖fderiv ℝ g x - ContinuousLinearMap.id ℝ E‖ < ε :=
    hc (Iio_mem_nhds (by simpa only [hd0, sub_self, norm_zero] using hε))
  obtain ⟨R, hR, hRsub⟩ := nhds_basis_closedBall.mem_iff.mp
    (inter_mem (hU.mem_nhds h0) hsmall)
  let r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have h2r : 2 * r = R := by dsimp [r]; ring
  have hball : closedBall (0 : E) (2 * r) ⊆ U := by
    rw [h2r]
    exact fun _ hx => (hRsub hx).1
  have hdg (x : E) (hx : x ∈ closedBall (0 : E) (2 * r)) :
      ‖fderiv ℝ g x - ContinuousLinearMap.id ℝ E‖ ≤ ε := by
    rw [h2r] at hx
    exact (hRsub hx).2.le
  let χ : E → ℝ := fun x => b (r⁻¹ • x)
  have hχ : ContDiff ℝ ∞ χ := hb.comp (contDiff_id.const_smul r⁻¹)
  have hχsupp : tsupport χ ⊆ closedBall (0 : E) (2 * r) := by
    apply closure_minimal ?_ isClosed_closedBall
    intro x hx
    have hbx : r⁻¹ • x ∈ ball (0 : E) 2 := by
      change r⁻¹ • x ∈ ball (0 : E) b.rOut
      rw [← b.support_eq]
      exact hx
    have hn : ‖x‖ / r < 2 := by
      simpa only [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg
        (inv_nonneg.mpr hr.le), ← div_eq_inv_mul] using hbx
    rw [mem_closedBall_zero_iff]
    exact ((div_lt_iff₀ hr).mp hn).le
  have hχone (x : E) (hx : x ∈ closedBall (0 : E) r) : χ x = 1 := by
    apply b.one_of_mem_closedBall
    rw [mem_closedBall_zero_iff]
    change ‖r⁻¹ • x‖ ≤ 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), ← div_eq_inv_mul]
    exact (div_le_one hr).mpr (mem_closedBall_zero_iff.mp hx)
  have hχbound (x : E) : ‖χ x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg b.nonneg]
    exact b.le_one
  have hDχ (x : E) : ‖fderiv ℝ χ x‖ ≤ B / r := by
    have hd := (hb.differentiable (by simp) (r⁻¹ • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul r⁻¹)
    change HasFDerivAt χ ((fderiv ℝ (b : E → ℝ) (r⁻¹ • x)).comp
      (r⁻¹ • ContinuousLinearMap.id ℝ E)) x at hd
    rw [hd.fderiv]
    calc
      ‖(fderiv ℝ (b : E → ℝ) (r⁻¹ • x)).comp
          (r⁻¹ • ContinuousLinearMap.id ℝ E)‖ ≤
          ‖fderiv ℝ (b : E → ℝ) (r⁻¹ • x)‖ *
            ‖r⁻¹ • ContinuousLinearMap.id ℝ E‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ B * (r⁻¹ * 1) := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
        exact mul_le_mul (hDb _) (mul_le_mul_of_nonneg_left
          ContinuousLinearMap.norm_id_le (inv_nonneg.mpr hr.le))
          (mul_nonneg (inv_nonneg.mpr hr.le) (norm_nonneg _)) hB
      _ = B / r := by rw [mul_one, div_eq_mul_inv]
  let P : E → E := fun x => x + χ x • (g x - x)
  have hP : ContDiff ℝ ∞ P :=
    Poincare.Analysis.Calculus.contDiff_cutoff_perturbation hU hχ
      (hχsupp.trans hball) hg
  have hbound (x : E) :
      ‖fderiv ℝ P x - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 2 : ℝ) := by
    by_cases hx : x ∈ tsupport χ
    · have hxball := hχsupp hx
      have hdiff : ∀ y ∈ closedBall (0 : E) (2 * r), DifferentiableAt ℝ g y :=
        fun y hy => (hg.contDiffAt (hU.mem_nhds (hball hy))).differentiableAt (by simp)
      have hdist : ‖g x - x‖ ≤ ε * (2 * r) := by
        have hm := (convex_closedBall (0 : E) (2 * r)).norm_image_sub_le_of_norm_fderiv_le'
          hdiff hdg (mem_closedBall_self (by positivity)) hxball
        have hm' : ‖g x - x‖ ≤ ε * ‖x‖ := by
          simpa only [hg0, sub_zero, ContinuousLinearMap.id_apply] using hm
        exact hm'.trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hxball) hε.le)
      have ha := mul_le_mul (hχbound x) (hdg x hxball) (norm_nonneg _) zero_le_one
      have hb' := mul_le_mul (hDχ x) hdist (norm_nonneg _) (div_nonneg hB hr.le)
      have hcancel : B / r * (ε * (2 * r)) = 2 * B * ε := by field_simp
      calc
        ‖fderiv ℝ P x - ContinuousLinearMap.id ℝ E‖ ≤
            ‖χ x‖ * ‖fderiv ℝ g x - ContinuousLinearMap.id ℝ E‖ +
              ‖fderiv ℝ χ x‖ * ‖g x - x‖ :=
          Poincare.Analysis.Calculus.norm_fderiv_cutoff_perturbation_sub_id_le
            (hχ.differentiable (by simp) x) (hdiff x hxball)
        _ ≤ 1 * ε + B / r * (ε * (2 * r)) := add_le_add ha hb'
        _ = (1 + 2 * B) * ε := by rw [hcancel]; ring
        _ = 1 / 4 := hεeq
        _ ≤ 1 / 2 := by norm_num
    · have heq : P =ᶠ[𝓝 x] id := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        simp only [Pi.zero_apply] at hy
        simp only [P, hy, zero_smul, add_zero, id_eq]
      rw [heq.fderiv_eq, fderiv_id, sub_self, norm_zero]
      norm_num
  refine ⟨r, hr, hball, P, hP, ?_, ?_, hbound⟩
  · intro x hx
    simp only [P, hχone x hx, one_smul, add_sub_cancel]
  · intro x hx
    have hz : χ x = 0 := notMem_support.mp (fun hs => hx (hχsupp (subset_tsupport χ hs)))
    simp only [P, hz, zero_smul, add_zero]




theorem exists_compact_germ_isotopy {U : Set E} (hU : IsOpen U) (h0 : (0 : E) ∈ U)
    {g : E → E} (hg : ContDiffOn ℝ ∞ g U) (hg0 : g 0 = 0)
    (hd0 : fderiv ℝ g 0 = ContinuousLinearMap.id ℝ E) :
    ∃ r : ℝ, 0 < r ∧ closedBall (0 : E) (2 * r) ⊆ U ∧
      ∃ D : ℝ → E ≃ₘ[ℝ] E,
        ContDiff ℝ ∞ (fun p : ℝ × E => D p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × E => (D p.1).symm p.2) ∧
        (∀ t, t ≤ 0 → ∀ x, D t x = x) ∧
        (∀ t, 1 ≤ t → ∀ x ∈ closedBall (0 : E) r, D t x = g x) ∧
        (∀ t x, x ∉ closedBall (0 : E) (2 * r) → D t x = x ∧ (D t).symm x = x) ∧
        (∀ t, D t 0 = 0) := by
  obtain ⟨r, hr, hball, P, hP, hPg, hPfix, hPb⟩ :=
    exists_small_derivative_germ_extension hU h0 hg hg0 hd0
  let F : ℝ × E → E := fun p => p.2 + Real.smoothTransition p.1 • (P p.2 - p.2)
  have hF : ContDiff ℝ ∞ F := contDiff_snd.add
    ((Real.smoothTransition.contDiff.comp contDiff_fst).smul
      ((hP.comp contDiff_snd).sub contDiff_snd))
  have hclose (t : ℝ) (x : E) :
      ‖fderiv ℝ (fun y => F (t, y)) x - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 2 : ℝ≥0) := by
    have hd := (hasFDerivAt_id x).add
      (((hP.differentiable (by simp) x).hasFDerivAt.sub (hasFDerivAt_id x)).const_smul
        (Real.smoothTransition t))
    change HasFDerivAt (fun y => F (t, y))
      (ContinuousLinearMap.id ℝ E + Real.smoothTransition t •
        (fderiv ℝ P x - ContinuousLinearMap.id ℝ E)) x at hd
    rw [hd.fderiv, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (Real.smoothTransition.nonneg t)]
    norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    exact (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one t)
      (norm_nonneg _)).trans (by simpa only [one_mul] using hPb x)
  obtain ⟨D, hD, hDs, hDi⟩ := exists_smooth_diffeomorph_family_of_fderiv_close_id
    F hF (by norm_num : (1 / 2 : ℝ≥0) < 1) hclose
  refine ⟨r, hr, hball, D, hDs, hDi, ?_, ?_, ?_, ?_⟩
  · intro t ht x
    rw [hD]
    simp only [F, Real.smoothTransition.zero_of_nonpos ht, zero_smul, add_zero]
  · intro t ht x hx
    rw [hD]
    simp only [F, Real.smoothTransition.one_of_one_le ht, one_smul, add_sub_cancel, hPg x hx]
  · intro t x hx
    have heq : D t x = x := by
      rw [hD]
      simp only [F, hPfix x hx, sub_self, smul_zero, add_zero]
    refine ⟨heq, ?_⟩
    have hi := congrArg (D t).symm heq
    simpa only [(D t).symm_apply_apply] using hi.symm
  · intro t
    rw [hD]
    simp only [F, hPg 0 (mem_closedBall_self hr.le), hg0, sub_self, smul_zero, add_zero]

end PoincareConjecture.M25.Topology3D
