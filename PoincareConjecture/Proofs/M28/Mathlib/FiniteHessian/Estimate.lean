import PoincareConjecture.Proofs.M28.Mathlib.FiniteHessian.JetBounds











set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.Proofs.M28.FiniteHessian

variable {ι E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem hasUniformJetBoundsAt_fderiv_of_hessian
    (n : ℕ) {f : ι → E → F} {x : ι → E}
    {A : ι → E → E →L[ℝ] E →L[ℝ] E}
    {B : ι → F → F →L[ℝ] F →L[ℝ] F}
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hA : ∀ i, ContDiffAt ℝ ∞ (A i) (x i))
    (hB : ∀ i, ContDiffAt ℝ ∞ (B i) (f i (x i)))
    (hAj : HasUniformJetBoundsAt n A x)
    (hBj : HasUniformJetBoundsAt n B (fun i => f i (x i)))
    (hfirst : ∃ C : ℝ, ∀ i, ‖fderiv ℝ (f i) (x i)‖ ≤ C)
    (hEq : ∀ i, ∀ᶠ y in 𝓝 (x i), ∀ u v,
      fderiv ℝ (fderiv ℝ (f i)) y u v =
        fderiv ℝ (f i) y (A i y u v) -
          B i (f i y) (fderiv ℝ (f i) y u) (fderiv ℝ (f i) y v)) :
    HasUniformJetBoundsAt (n + 1) (fun i => fderiv ℝ (f i)) x := by
  let D := fun i => fderiv ℝ (f i)
  have hD : ∀ i, ContDiffAt ℝ ∞ (D i) (x i) :=
    fun i => (hf i).fderiv_right (by simp)
  have hBc : ∀ i, ContDiffAt ℝ ∞ (fun y => B i (f i y)) (x i) :=
    fun i => (hB i).comp (x i) (hf i)
  let postL : (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] E) →L[ℝ] E →L[ℝ] F :=
    ContinuousLinearMap.compL ℝ E E F
  let flip₁ := (ContinuousLinearMap.flipₗᵢ ℝ E F F).toLinearIsometry.toContinuousLinearMap
  let flip₂ := (ContinuousLinearMap.flipₗᵢ ℝ E E F).toLinearIsometry.toContinuousLinearMap
  have hpostL : ContDiff ℝ ∞ postL :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := E →L[ℝ] F)
      (F := (E →L[ℝ] E) →L[ℝ] E →L[ℝ] F) postL
  have hflip₁ : ContDiff ℝ ∞ flip₁ :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := E →L[ℝ] F →L[ℝ] F)
      (F := F →L[ℝ] E →L[ℝ] F) flip₁
  have hflip₂ : ContDiff ℝ ∞ flip₂ :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] F)
      (F := E →L[ℝ] E →L[ℝ] F) flip₂
  have hsteps : ∀ k, k ≤ n + 1 → HasUniformJetBoundsAt k D x := by
    intro k
    induction k with
    | zero =>
        intro _ m hm
        have hm0 : m = 0 := by omega
        subst m
        simpa only [norm_iteratedFDeriv_zero] using hfirst
    | succ k ih =>
        intro hk
        have hkn : k ≤ n := by omega
        have ih := ih (by omega)
        have hBfj := ih.comp_of_fderiv (hBj.mono_order hkn) hf hB
        have hpost := ih.clm (G := (E →L[ℝ] E) →L[ℝ] E →L[ℝ] F)
          hD postL
        have hcpost : ∀ i, ContDiffAt ℝ ∞
            (fun y => postL (D i y)) (x i) :=
          fun i => hpostL.contDiffAt.comp (x i) (hD i)
        have hleft := hpost.clm_comp (hAj.mono_order hkn) hcpost hA
        have hcleft : ∀ i, ContDiffAt ℝ ∞
            (fun y => (postL (D i y)).comp (A i y)) (x i) :=
          fun i => (hcpost i).clm_comp (hA i)
        have hpre := hBfj.clm_comp ih hBc hD
        have hcpre : ∀ i, ContDiffAt ℝ ∞
            (fun y => (B i (f i y)).comp (D i y)) (x i) :=
          fun i => (hBc i).clm_comp (hD i)
        have hflip := hpre.clm (G := F →L[ℝ] E →L[ℝ] F) hcpre flip₁
        have hcflip : ∀ i, ContDiffAt ℝ ∞
            (fun y => flip₁ ((B i (f i y)).comp (D i y))) (x i) :=
          fun i => hflip₁.contDiffAt.comp (x i) (hcpre i)
        have hpre' := hflip.clm_comp ih hcflip hD
        have hcpre' : ∀ i, ContDiffAt ℝ ∞
            (fun y => (flip₁ ((B i (f i y)).comp (D i y))).comp (D i y)) (x i) :=
          fun i => (hcflip i).clm_comp (hD i)
        have hright := hpre'.clm (G := E →L[ℝ] E →L[ℝ] F) hcpre' flip₂
        have hcright : ∀ i, ContDiffAt ℝ ∞
            (fun y => flip₂ ((flip₁ ((B i (f i y)).comp (D i y))).comp (D i y))) (x i) :=
          fun i => hflip₂.contDiffAt.comp (x i) (hcpre' i)
        apply HasUniformJetBoundsAt.succ_of_fderiv hfirst
        apply (hleft.sub hright hcleft hcright).congr_germ
        intro i
        filter_upwards [hEq i] with y hy
        ext u v
        exact (hy u v).symm
  exact hsteps (n + 1) le_rfl




theorem exists_uniform_positive_jet_bound_of_hessian
    (n : ℕ) {f : ι → E → F} {x : ι → E}
    {A : ι → E → E →L[ℝ] E →L[ℝ] E}
    {B : ι → F → F →L[ℝ] F →L[ℝ] F}
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hA : ∀ i, ContDiffAt ℝ ∞ (A i) (x i))
    (hB : ∀ i, ContDiffAt ℝ ∞ (B i) (f i (x i)))
    (hAj : HasUniformJetBoundsAt n A x)
    (hBj : HasUniformJetBoundsAt n B (fun i => f i (x i)))
    (hfirst : ∃ C : ℝ, ∀ i, ‖fderiv ℝ (f i) (x i)‖ ≤ C)
    (hEq : ∀ i, ∀ᶠ y in 𝓝 (x i), ∀ u v,
      fderiv ℝ (fderiv ℝ (f i)) y u v =
        fderiv ℝ (f i) y (A i y u v) -
          B i (f i y) (fderiv ℝ (f i) y u) (fderiv ℝ (f i) y v)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m, 1 ≤ m → m ≤ n + 2 → ∀ i,
      ‖iteratedFDeriv ℝ m (f i) (x i)‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ :=
    (hasUniformJetBoundsAt_fderiv_of_hessian n hf hA hB hAj hBj hfirst hEq).bound_all
  refine ⟨C, hC0, ?_⟩
  intro m hmpos hm i
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simpa only [norm_iteratedFDeriv_fderiv] using hC k (by omega) i

end PoincareConjecture.Proofs.M28.FiniteHessian
