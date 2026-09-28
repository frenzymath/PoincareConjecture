import PoincareConjecture.Proofs.M34.Mathlib.BilinearPullbackJetBound
import PoincareConjecture.Proofs.M34.Mathlib.NeckBilinearSmooth
import PoincareConjecture.Proofs.M34.Mathlib.FiniteJetNormBounds

set_option autoImplicit false

set_option maxSynthPendingDepth 12

open Filter
open scoped ContDiff Topology
open Poincare.Analysis.Calculus

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem exists_hessian_germ_step_bound (m : ℕ) {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : E → F) (A : E → E →L[ℝ] E →L[ℝ] E)
      (B : F → F →L[ℝ] F →L[ℝ] F) (x : E),
      ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ A x → ContDiffAt ℝ ∞ B (f x) →
      (∀ᶠ y in 𝓝 x, ∀ v w,
        fderiv ℝ (fderiv ℝ f) y v w = fderiv ℝ f y (A y v w) -
          B (f y) (fderiv ℝ f y v) (fderiv ℝ f y w)) →
      (∀ j ≤ m + 1, ‖iteratedFDeriv ℝ j f x‖ ≤ K) →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j A x‖ ≤ K) →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j B (f x)‖ ≤ K) →
      ‖iteratedFDeriv ℝ (m + 2) f x‖ ≤ C := by
  let op : (E →L[ℝ] F) →L[ℝ]
      (E →L[ℝ] E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] F :=
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (E →L[ℝ] F)).comp
      (ContinuousLinearMap.compL ℝ E E F)
  obtain ⟨D, hD, hDb⟩ :=
    exists_bilinear_pullback_jet_bound (E := E) (F := F) (G := F) m hK
  refine ⟨max 1 (‖op‖ * (2 : ℝ) ^ m * K * K + D * K), le_max_left _ _, ?_⟩
  intro f A B x hf hA hB hEq hfj hAj hBj
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  have hs : ContDiffAt ℝ ∞ (fun y => op (fderiv ℝ f y) (A y)) x :=
    op.isBoundedBilinearMap.contDiff.contDiffAt.comp x (hd.prodMk hA)
  have ht := hf.bilinearPullback hB
  have hsbound := norm_iteratedFDeriv_bilinear_le_of_jet_bounds op hd hA m
    (zero_le_one.trans hK)
    (fun j hj => by rw [norm_iteratedFDeriv_fderiv]; exact hfj _ (by omega)) hAj
  have htbound := hDb f B x hf hB hfj K (zero_le_one.trans hK) hBj
  have heq : (fderiv ℝ (fderiv ℝ f)) =ᶠ[𝓝 x]
      (fun y => op (fderiv ℝ f y) (A y) -
        (B (f y)).bilinearComp (fderiv ℝ f y) (fderiv ℝ f y)) := by
    filter_upwards [hEq] with y hy
    ext v w
    exact hy v w
  calc
    _ = ‖iteratedFDeriv ℝ m (fderiv ℝ (fderiv ℝ f)) x‖ := by
      rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
    _ = ‖iteratedFDeriv ℝ m (fun y => op (fderiv ℝ f y) (A y) -
        (B (f y)).bilinearComp (fderiv ℝ f y) (fderiv ℝ f y)) x‖ :=
      congrArg norm ((heq.iteratedFDeriv ℝ m).self_of_nhds)
    _ ≤ _ := (norm_iteratedFDeriv_sub_le_of_contDiffAt m
      (hs.of_le (by exact_mod_cast le_top))
      (ht.of_le (by exact_mod_cast le_top))).trans
        ((add_le_add hsbound htbound).trans (le_max_right _ _))

theorem exists_finite_hessian_germ_jet_bound (N : ℕ) {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : E → F) (A : E → E →L[ℝ] E →L[ℝ] E)
      (B : F → F →L[ℝ] F →L[ℝ] F) (x : E),
      ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ A x → ContDiffAt ℝ ∞ B (f x) →
      (∀ᶠ y in 𝓝 x, ∀ v w,
        fderiv ℝ (fderiv ℝ f) y v w = fderiv ℝ f y (A y v w) -
          B (f y) (fderiv ℝ f y v) (fderiv ℝ f y w)) →
      ‖f x‖ ≤ K → ‖fderiv ℝ f x‖ ≤ K →
      (∀ j ≤ N, ‖iteratedFDeriv ℝ j A x‖ ≤ K) →
      (∀ j ≤ N, ‖iteratedFDeriv ℝ j B (f x)‖ ≤ K) →
      ∀ j ≤ N + 2, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  induction N with
  | zero =>
    obtain ⟨C, hC, hCb⟩ := exists_hessian_germ_step_bound (E := E) (F := F) 0 hK
    refine ⟨max K C, hK.trans (le_max_left _ _), ?_⟩
    intro f A B x hf hA hB hEq hzero hfirst hAj hBj j hj
    have hlow (l : ℕ) (hl : l ≤ 1) : ‖iteratedFDeriv ℝ l f x‖ ≤ K := by
      interval_cases l
      · simpa only [norm_iteratedFDeriv_zero] using hzero
      · simpa only [norm_iteratedFDeriv_one] using hfirst
    by_cases hle : j ≤ 1
    · exact (hlow j hle).trans (le_max_left _ _)
    · have he : j = 2 := by omega
      subst j
      exact (hCb f A B x hf hA hB hEq hlow hAj hBj).trans (le_max_right _ _)
  | succ N ih =>
    obtain ⟨C, hC, hCb⟩ := ih
    let K' := max K C
    have hK' : 1 ≤ K' := hK.trans (le_max_left _ _)
    obtain ⟨D, hD, hDb⟩ := exists_hessian_germ_step_bound
      (E := E) (F := F) (N + 1) hK'
    refine ⟨max C D, hC.trans (le_max_left _ _), ?_⟩
    intro f A B x hf hA hB hEq hzero hfirst hAj hBj j hj
    have hprev : ∀ l ≤ N + 2, ‖iteratedFDeriv ℝ l f x‖ ≤ C :=
      hCb f A B x hf hA hB hEq hzero hfirst
        (fun l hl => hAj l (by omega)) (fun l hl => hBj l (by omega))
    by_cases hle : j ≤ N + 2
    · exact (hprev j hle).trans (le_max_left _ _)
    · have he : j = (N + 1) + 2 := by omega
      subst j
      apply (hDb f A B x hf hA hB hEq
        (fun l hl => (hprev l (by omega)).trans (le_max_right _ _))
        (fun l hl => (hAj l hl).trans (le_max_left _ _))
        (fun l hl => (hBj l hl).trans (le_max_left _ _))).trans (le_max_right _ _)

end
