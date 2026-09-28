import PoincareConjecture.Proofs.M28.Mathlib.FiniteHessian.Estimate

set_option autoImplicit false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.Proofs.M28.FiniteHessian

variable {ι E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem contDiffAt_bilinear_pullback {f : E → F} {A : F → F →L[ℝ] F →L[ℝ] G}
    {x : E} (hf : ContDiffAt ℝ ∞ f x) (hA : ContDiffAt ℝ ∞ A (f x)) :
    ContDiffAt ℝ ∞ (fun y => (A (f y)).bilinearComp
      (fderiv ℝ f y) (fderiv ℝ f y)) x := by
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  have hpre := (hA.comp x hf).clm_comp hD
  let flip₁ := (ContinuousLinearMap.flipₗᵢ ℝ E F G).toLinearIsometry.toContinuousLinearMap
  let flip₂ := (ContinuousLinearMap.flipₗᵢ ℝ E E G).toLinearIsometry.toContinuousLinearMap
  have hc₁ : ContDiff ℝ ∞ flip₁ :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := E →L[ℝ] F →L[ℝ] G)
      (F := F →L[ℝ] E →L[ℝ] G) flip₁
  have hc₂ : ContDiff ℝ ∞ flip₂ :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] G)
      (F := E →L[ℝ] E →L[ℝ] G) flip₂
  exact hc₂.contDiffAt.comp x ((hc₁.contDiffAt.comp x hpre).clm_comp hD)

theorem HasUniformJetBoundsAt.bilinear_pullback {n : ℕ}
    {f : ι → E → F} {A : ι → F → F →L[ℝ] F →L[ℝ] G} {x : ι → E}
    (hf : HasUniformJetBoundsAt n (fun i => fderiv ℝ (f i)) x)
    (hA : HasUniformJetBoundsAt n A (fun i => f i (x i)))
    (hcf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hcA : ∀ i, ContDiffAt ℝ ∞ (A i) (f i (x i))) :
    HasUniformJetBoundsAt n (fun i y => (A i (f i y)).bilinearComp
      (fderiv ℝ (f i) y) (fderiv ℝ (f i) y)) x := by
  have hD : ∀ i, ContDiffAt ℝ ∞ (fderiv ℝ (f i)) (x i) :=
    fun i => (hcf i).fderiv_right (by simp)
  have hAc : ∀ i, ContDiffAt ℝ ∞ (fun y => A i (f i y)) (x i) :=
    fun i => (hcA i).comp (x i) (hcf i)
  have hAcj : HasUniformJetBoundsAt n (fun i y => A i (f i y)) x :=
    hf.comp_of_fderiv hA hcf hcA
  have hpre : HasUniformJetBoundsAt n
      (fun i y => (A i (f i y)).comp (fderiv ℝ (f i) y)) x :=
    hAcj.clm_comp hf hAc hD
  have hcpre : ∀ i, ContDiffAt ℝ ∞
      (fun y => (A i (f i y)).comp (fderiv ℝ (f i) y)) (x i) :=
    fun i => (hAc i).clm_comp (hD i)
  let flip₁ := (ContinuousLinearMap.flipₗᵢ ℝ E F G).toLinearIsometry.toContinuousLinearMap
  let flip₂ := (ContinuousLinearMap.flipₗᵢ ℝ E E G).toLinearIsometry.toContinuousLinearMap
  have hc₁ : ContDiff ℝ ∞ flip₁ :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := E →L[ℝ] F →L[ℝ] G)
      (F := F →L[ℝ] E →L[ℝ] G) flip₁
  have hc₂ : ContDiff ℝ ∞ flip₂ :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] G)
      (F := E →L[ℝ] E →L[ℝ] G) flip₂
  have hflip := hpre.clm (G := F →L[ℝ] E →L[ℝ] G) hcpre flip₁
  have hcflip : ∀ i, ContDiffAt ℝ ∞
      (fun y => flip₁ ((A i (f i y)).comp (fderiv ℝ (f i) y))) (x i) :=
    fun i => hc₁.contDiffAt.comp (x i) (hcpre i)
  have hpre' := hflip.clm_comp hf hcflip hD
  have hcpre' : ∀ i, ContDiffAt ℝ ∞
      (fun y => (flip₁ ((A i (f i y)).comp (fderiv ℝ (f i) y))).comp
        (fderiv ℝ (f i) y)) (x i) :=
    fun i => (hcflip i).clm_comp (hD i)
  exact hpre'.clm (G := E →L[ℝ] E →L[ℝ] G) hcpre' flip₂

theorem exists_bilinear_pullback_error_bound (n : ℕ)
    {f : ι → E → F} {A : ι → F → F →L[ℝ] F →L[ℝ] G} {x : ι → E}
    {error : ι → ℝ} (herror : ∀ i, 0 < error i)
    (hf : HasUniformJetBoundsAt n (fun i => fderiv ℝ (f i)) x)
    (hcf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hcA : ∀ i, ContDiffAt ℝ ∞ (A i) (f i (x i)))
    (hA : ∀ m, m ≤ n → ∀ i,
      ‖iteratedFDeriv ℝ m (A i) (f i (x i))‖ ≤ error i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m, m ≤ n → ∀ i,
      ‖iteratedFDeriv ℝ m (fun y => (A i (f i y)).bilinearComp
        (fderiv ℝ (f i) y) (fderiv ℝ (f i) y)) (x i)‖ ≤ C * error i := by
  let T := fun i y => (error i)⁻¹ • A i y
  have hcT : ∀ i, ContDiffAt ℝ ∞ (T i) (f i (x i)) :=
    fun i => (hcA i).const_smul _
  have hT : HasUniformJetBoundsAt n T (fun i => f i (x i)) := by
    intro m hm
    refine ⟨1, fun i => ?_⟩
    change ‖iteratedFDeriv ℝ m (fun y => (error i)⁻¹ • A i y) (f i (x i))‖ ≤ 1
    rw [iteratedFDeriv_const_smul_apply' ((hcA i).of_le (by exact_mod_cast le_top)),
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (herror i))]
    calc
      _ ≤ (error i)⁻¹ * error i :=
        mul_le_mul_of_nonneg_left (hA m hm i) (inv_nonneg.mpr (herror i).le)
      _ = 1 := inv_mul_cancel₀ (herror i).ne'
  obtain ⟨C, hC0, hC⟩ := (hf.bilinear_pullback hT hcf hcT).bound_all
  refine ⟨C, hC0, ?_⟩
  intro m hm i
  have hh := hC m hm i
  have heq : (fun y => (T i (f i y)).bilinearComp
      (fderiv ℝ (f i) y) (fderiv ℝ (f i) y)) =
      (fun y => (error i)⁻¹ • (A i (f i y)).bilinearComp
        (fderiv ℝ (f i) y) (fderiv ℝ (f i) y)) := by
    funext y
    ext u v
    rfl
  rw [heq, iteratedFDeriv_const_smul_apply'
    ((contDiffAt_bilinear_pullback (hcf i) (hcA i)).of_le (by exact_mod_cast le_top)),
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (herror i))] at hh
  apply (div_le_iff₀ (herror i)).mp
  simpa only [div_eq_mul_inv, mul_comm] using hh

end PoincareConjecture.Proofs.M28.FiniteHessian
