import PoincareConjecture.Proofs.M35.RadialGauge.SourceDerivativeDifference
import Mathlib.Analysis.Calculus.ContDiff.Bounds










set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {X E F W : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable local instance m35JetCalculusLocal1 :
    NormedAddCommGroup (F →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35JetCalculusLocal2 :
    NormedSpace ℝ (F →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance m35JetCalculusLocal3 :
    NormedAddCommGroup (E →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35JetCalculusLocal4 :
    NormedSpace ℝ (E →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace


theorem norm_fderiv_bilinear_le (B : E →L[ℝ] F →L[ℝ] W)
    {f : X → E} {g : X → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hB : ‖B‖ ≤ 1) (x : X) :
    ‖fderiv ℝ (fun y => B (f y) (g y)) x‖ ≤
      ‖f x‖ * ‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖ * ‖g x‖ := by
  simpa [Finset.sum_range_succ, norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one]
    using B.norm_iteratedFDeriv_le_of_bilinear_of_le_one hf hg x
      (n := 1) (by simp) hB



theorem norm_fderiv_clm_comp_le
    {f : X → F →L[ℝ] W} {g : X → E →L[ℝ] F}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : X) :
    ‖fderiv ℝ (fun y => (f y).comp (g y)) x‖ ≤
      ‖f x‖ * ‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖ * ‖g x‖ :=
  norm_fderiv_bilinear_le (ContinuousLinearMap.compL ℝ E F W) hf hg
    (ContinuousLinearMap.norm_compL_le ℝ E F W) x


theorem norm_fderiv_clm_apply_le
    {f : X → E →L[ℝ] F} {g : X → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : X) :
    ‖fderiv ℝ (fun y => f y (g y)) x‖ ≤
      ‖f x‖ * ‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖ * ‖g x‖ := by
  rw [((hf.differentiable (by simp) x).hasFDerivAt.clm_apply
    (hg.differentiable (by simp) x).hasFDerivAt).fderiv]
  exact (norm_add_le _ _).trans (add_le_add ((f x).opNorm_comp_le _)
    (by simpa only [ContinuousLinearMap.opNorm_flip] using
      (fderiv ℝ f x).flip.le_opNorm (g x)))

theorem norm_fderiv_smul_le {f : X → ℝ} {g : X → F}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : X) :
    ‖fderiv ℝ (fun y => f y • g y) x‖ ≤
      ‖f x‖ * ‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖ * ‖g x‖ :=
  norm_fderiv_bilinear_le (ContinuousLinearMap.lsmul ℝ ℝ) hf hg
    ContinuousLinearMap.opNorm_lsmul_le x



theorem graph_derivative_norm_le_general (q : (X × ℝ) →L[ℝ] F)
    (p : X →L[ℝ] ℝ) :
    ‖q.comp ((ContinuousLinearMap.id ℝ X).prod p)‖ ≤
      ‖q.comp (ContinuousLinearMap.inl ℝ X ℝ)‖ + ‖q (0, 1)‖ * ‖p‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have heq : q (v, p v) = q (v, 0) + (p v) • q (0, 1) := by
    have hp : (v, p v) = (v, 0) + (p v) • (0, (1 : ℝ)) := by ext <;> simp
    rw [hp, map_add, map_smul]
  change ‖q (v, p v)‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖q (v, 0)‖ + ‖(p v) • q (0, 1)‖ := norm_add_le _ _
    _ ≤ ‖q.comp (ContinuousLinearMap.inl ℝ X ℝ)‖ * ‖v‖ +
        (‖p‖ * ‖v‖) * ‖q (0, 1)‖ := by
      apply add_le_add
      · exact (q.comp (ContinuousLinearMap.inl ℝ X ℝ)).le_opNorm v
      · rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (p.le_opNorm v) (norm_nonneg _)
    _ = _ := by ring

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "D" => V →L[ℝ] ℝ

noncomputable local instance m35JetCalculusLocal5 :
    NormedAddCommGroup D := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35JetCalculusLocal6 :
    NormedSpace ℝ D := ContinuousLinearMap.toNormedSpace



noncomputable def dualSquaredLinear : D →L[ℝ] D →L[ℝ] ℝ :=
  let R := (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap
  (2 : ℝ) • (((ContinuousLinearMap.compL ℝ D V ℝ).flip R).comp
    ((innerSL ℝ).comp R))

theorem dualSquaredLinear_apply (p : D) :
    dualSquaredLinear p = dualSquaredDifferential p := rfl

theorem dualSquaredLinear_norm_le : ‖(dualSquaredLinear : D →L[ℝ] D →L[ℝ] ℝ)‖ ≤ 2 := by
  exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (fun p => dualSquaredDifferential_norm_le p)

theorem dualSquaredDifferential_contDiff
    {p : V → D} (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (fun x => dualSquaredDifferential (p x)) :=
  (dualSquaredLinear.contDiff).comp hp

theorem norm_fderiv_dualSquaredDifferential_le
    {p : V → D} {x : V} (hp : DifferentiableAt ℝ p x) :
    ‖fderiv ℝ (fun y => dualSquaredDifferential (p y)) x‖ ≤ 2 * ‖fderiv ℝ p x‖ := by
  rw [show fderiv ℝ (fun y => dualSquaredDifferential (p y)) x =
      dualSquaredLinear.comp (fderiv ℝ p x) from
    (dualSquaredLinear.hasFDerivAt.comp x hp.hasFDerivAt).fderiv]
  exact (dualSquaredLinear.opNorm_comp_le _).trans
    (mul_le_mul_of_nonneg_right dualSquaredLinear_norm_le (norm_nonneg _))



theorem norm_fderiv_flip (H : X → E →L[ℝ] F →L[ℝ] W)
    {x : X} (hH : DifferentiableAt ℝ H x) :
    ‖fderiv ℝ (fun y => (H y).flip) x‖ = ‖fderiv ℝ H x‖ := by
  let L := ContinuousLinearMap.flipₗᵢ ℝ E F W
  have heq : fderiv ℝ (fun y => (H y).flip) x =
      L.toContinuousLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ H x) :=
    (L.hasFDerivAt.comp x hH.hasFDerivAt).fderiv
  rw [heq]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _)
    intro v
    change ‖((fderiv ℝ H x) v).flip‖ ≤ _
    rw [ContinuousLinearMap.opNorm_flip]
    exact (fderiv ℝ H x).le_opNorm v
  · apply ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _)
    intro v
    have h := (L.toContinuousLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ H x)).le_opNorm v
    change ‖((fderiv ℝ H x) v).flip‖ ≤ _ at h
    rw [ContinuousLinearMap.opNorm_flip] at h
    exact h

theorem forcingSpaceDeriv_contDiff {G : V → ℝ → ℝ}
    (hG : ContDiff ℝ ∞ (fun p : V × ℝ => G p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : V × ℝ => forcingSpaceDeriv G p.1 p.2) :=
  (contDiff_infty_iff_fderiv.mp hG).2.clm_comp contDiff_const

theorem forcingScalarDeriv_contDiff {G : V → ℝ → ℝ}
    (hG : ContDiff ℝ ∞ (fun p : V × ℝ => G p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : V × ℝ => forcingScalarDeriv G p.1 p.2) :=
  (contDiff_infty_iff_fderiv.mp hG).2.clm_apply contDiff_const

end PoincareConjecture.M35.RadialGauge
