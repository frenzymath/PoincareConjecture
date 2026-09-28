import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Uniform
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.SpatialRescaling








set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace Poincare.Parabolic



theorem exists_uniform_interior_heat_hessian_bound_scaled
    (n : ℕ) (hn : 1 ≤ n) {r lam Λ H : ℝ}
    (hr : 0 < r) (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
        ContDiffOn ℝ ∞ a (Metric.ball 0 (r * 2)) →
        (∀ x ∈ Metric.ball 0 (r * 2), ∀ v w,
          inner ℝ (a x v) w = inner ℝ v (a x w)) →
        (∀ x ∈ Metric.ball 0 (r * 2), ∀ v,
          lam * ‖v‖ ^ 2 ≤ inner ℝ v (a x v) ∧
          inner ℝ v (a x v) ≤ Λ * ‖v‖ ^ 2) →
        (∀ x ∈ Metric.ball 0 (r * 2), ∀ y ∈ Metric.ball 0 (r * 2),
          ‖a x - a y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ)) →
        ∀ B : ℝ, 0 ≤ B → ∀ f : EuclideanSpace ℝ (Fin n) × ℝ → ℝ,
          ContDiffOn ℝ ∞ f (Metric.ball 0 (r * 2) ×ˢ Ioo 0 2) →
          (∀ x ∈ Metric.ball 0 (r * 2), ∀ t ∈ Ioc (0 : ℝ) 1,
            HasDerivAt (fun s ↦ f (x, s))
              (∑ i, ∑ j, inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
                (a x (EuclideanSpace.basisFun (Fin n) ℝ j)) *
                fderiv ℝ (fderiv ℝ (fun z ↦ f (z, t))) x
                  (EuclideanSpace.basisFun (Fin n) ℝ i)
                  (EuclideanSpace.basisFun (Fin n) ℝ j)) t) →
          (∀ x ∈ Metric.ball 0 (r * 2), ∀ t ∈ Ioc (0 : ℝ) 1, |f (x, t)| ≤ B) →
          ‖fderiv ℝ (fderiv ℝ (fun z ↦ f (z, 1))) 0‖ ≤ C * B := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  obtain ⟨C, hC, hestimate⟩ := Interior.exists_uniform_interior_heat_hessian_bound
    n hn (lam / r ^ 2) (Λ / r ^ 2) (H * r ^ (1 / 2 : ℝ) / r ^ 2)
    (div_pos hlam hr2) (div_le_div_of_nonneg_right hlamΛ hr2.le) (by positivity)
  refine ⟨C / r ^ 2, div_pos hC hr2, ?_⟩
  intro a ha hsymm hell hholder B hB f hf hheat hvalue
  let ar := fun x ↦ (r ^ 2)⁻¹ • a (r • x)
  have har : ContDiffOn ℝ ∞ ar (Metric.ball 0 2) :=
    (ha.comp (contDiffOn_id.const_smul r) (fun x hx ↦ smul_mem_ball x hr hx)).const_smul _
  have hars : ∀ x ∈ Metric.ball 0 2, ∀ v w,
      inner ℝ (ar x v) w = inner ℝ v (ar x w) := by
    intro x hx v w
    simp only [ar, smul_apply, real_inner_smul_left,
      real_inner_smul_right, hsymm _ (smul_mem_ball x hr hx)]
  have hare : ∀ x ∈ Metric.ball 0 2, ∀ v,
      (lam / r ^ 2) * ‖v‖ ^ 2 ≤ inner ℝ v (ar x v) ∧
      inner ℝ v (ar x v) ≤ (Λ / r ^ 2) * ‖v‖ ^ 2 := by
    intro x hx v
    have hv := hell _ (smul_mem_ball x hr hx) v
    constructor
    · simpa [ar, real_inner_smul_right, div_eq_mul_inv, mul_assoc, mul_comm,
        mul_left_comm] using mul_le_mul_of_nonneg_left hv.1 (inv_nonneg.mpr hr2.le)
    · simpa [ar, real_inner_smul_right, div_eq_mul_inv, mul_assoc, mul_comm,
        mul_left_comm] using mul_le_mul_of_nonneg_left hv.2 (inv_nonneg.mpr hr2.le)
  have harh : ∀ x ∈ Metric.ball 0 2, ∀ y ∈ Metric.ball 0 2,
      ‖ar x - ar y‖ ≤ (H * r ^ (1 / 2 : ℝ) / r ^ 2) * ‖x - y‖ ^ (1 / 2 : ℝ) := by
    intro x hx y hy
    have h := mul_le_mul_of_nonneg_left
      (hholder _ (smul_mem_ball x hr hx) _ (smul_mem_ball y hr hy))
      (inv_nonneg.mpr hr2.le)
    simpa [ar, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      abs_of_nonneg (inv_nonneg.mpr hr2.le), Real.mul_rpow hr.le (norm_nonneg _),
      div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
  let fr := fun z : EuclideanSpace ℝ (Fin n) × ℝ ↦ f (r • z.1, z.2)
  have hfr : ContDiffOn ℝ ∞ fr (Metric.ball 0 2 ×ˢ Ioo 0 2) :=
    hf.comp ((contDiffOn_fst.const_smul r).prodMk contDiffOn_snd)
      (fun z hz ↦ ⟨smul_mem_ball z.1 hr hz.1, hz.2⟩)
  have hfre : ∀ x ∈ Metric.ball 0 2, ∀ t ∈ Ioc (0 : ℝ) 1,
      HasDerivAt (fun s ↦ fr (x, s))
        (∑ i, ∑ j, inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
          (ar x (EuclideanSpace.basisFun (Fin n) ℝ j)) *
          fderiv ℝ (fderiv ℝ (fun z ↦ fr (z, t))) x
            (EuclideanSpace.basisFun (Fin n) ℝ i)
            (EuclideanSpace.basisFun (Fin n) ℝ j)) t := by
    intro x hx t ht
    have h := hasDerivAt_spatially_rescaled_heat (fun z t ↦ f (z, t))
      (fun z i j ↦ inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
        (a z (EuclideanSpace.basisFun (Fin n) ℝ j))) hr.ne' x
      (hheat _ (smul_mem_ball x hr hx) t ht)
    simpa only [fr, ar, smul_apply, real_inner_smul_right, div_eq_mul_inv,
      mul_comm (r ^ 2)⁻¹] using h
  have hb := hestimate ar har hars hare harh B hB fr hfr hfre
    (fun x hx t ht ↦ hvalue _ (smul_mem_ball x hr hx) t ht)
  have hbop : ‖fderiv ℝ (fderiv ℝ (fun z ↦ fr (z, 1))) 0‖ ≤ C * B :=
    ContinuousLinearMap.opNorm_le_bound₂ _ (mul_nonneg hC.le hB) (by
      intro v w
      simpa only [Real.norm_eq_abs] using hb v w)
  have h := norm_fderiv_fderiv_le_of_rescaled (fun z ↦ f (z, 1)) hr hbop
  simpa only [div_mul_eq_mul_div] using h

end Poincare.Parabolic
