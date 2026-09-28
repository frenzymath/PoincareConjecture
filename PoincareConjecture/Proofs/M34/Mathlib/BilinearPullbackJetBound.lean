import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Operations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped ContDiff Topology BigOperators

namespace Poincare.Analysis.Calculus

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

private theorem norm_iteratedFDeriv_bilinear_le_of_contDiffAt
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖ * ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j f x‖ * ‖iteratedFDeriv ℝ (m - j) g x‖ := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := (m : ℕ∞ω))
    (by exact_mod_cast le_top) (by simp)
  obtain ⟨t, ht, hgt⟩ := hg.contDiffOn (m := (m : ℕ∞ω))
    (by exact_mod_cast le_top) (by simp)
  obtain ⟨v, hv, hvo, hxv⟩ := mem_nhds_iff.mp (inter_mem hs ht)
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear
    (hfs.mono (fun _ hy => (hv hy).1)) (hgt.mono (fun _ hy => (hv hy).2))
    hvo.uniqueDiffOn hxv (le_refl (m : ℕ∞ω))
  simpa only [iteratedFDerivWithin_of_isOpen _ hvo hxv] using h

theorem norm_iteratedFDeriv_bilinear_le_of_jet_bounds
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ)
    {A D : ℝ} (hA : 0 ≤ A)
    (hfjet : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hgjet : ∀ j ≤ m, ‖iteratedFDeriv ℝ j g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ m (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖ * (2 : ℝ) ^ m * A * D := by
  apply (norm_iteratedFDeriv_bilinear_le_of_contDiffAt B hf hg m).trans
  calc
    _ ≤ ‖B‖ * ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * A * D := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (hfjet j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) (by positivity))
        (hgjet (m - j) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = ‖B‖ * (2 : ℝ) ^ m * A * D := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hsum : (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ)) = 2 ^ m := by
        exact_mod_cast Nat.sum_range_choose m
      rw [hsum]
      ring

private noncomputable def bilinearPrecomposeFlip :
    (F →L[ℝ] G →L[ℝ] H) →L[ℝ] (E →L[ℝ] F) →L[ℝ] G →L[ℝ] E →L[ℝ] H :=
  (ContinuousLinearMap.compL ℝ (E →L[ℝ] F) (E →L[ℝ] G →L[ℝ] H)
      (G →L[ℝ] E →L[ℝ] H)
      (ContinuousLinearMap.flipₗᵢ ℝ E G H).toContinuousLinearEquiv.toContinuousLinearMap).comp
    (ContinuousLinearMap.compL ℝ E F (G →L[ℝ] H))

private theorem bilinearPrecomposeFlip_apply (b : F →L[ℝ] G →L[ℝ] H) (A : E →L[ℝ] F) :
    bilinearPrecomposeFlip b A = (b.comp A).flip := rfl

private theorem exists_two_bilinear_jet_bound
    {I : Type*} [NormedAddCommGroup I] [NormedSpace ℝ I]
    (op₁ : F →L[ℝ] G →L[ℝ] H) (op₂ : H →L[ℝ] G →L[ℝ] I)
    (m : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E → F) (d : E → G) (x : E),
      ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ d x →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j d x‖ ≤ D) →
      ∀ A : ℝ, 0 ≤ A → (∀ j ≤ m, ‖iteratedFDeriv ℝ j f x‖ ≤ A) →
      ‖iteratedFDeriv ℝ m (fun y => op₂ (op₁ (f y) (d y)) (d y)) x‖ ≤ C * A := by
  let C₁ : ℝ := ‖op₁‖ * 2 ^ m * D
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  refine ⟨‖op₂‖ * 2 ^ m * C₁ * D, by positivity, ?_⟩
  intro f d x hf hd hdjet A hA hfjet
  have hfirst : ContDiffAt ℝ ∞ (fun y => op₁ (f y) (d y)) x :=
    op₁.isBoundedBilinearMap.contDiff.contDiffAt.comp x (hf.prodMk hd)
  have hfirstjet (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j (fun y => op₁ (f y) (d y)) x‖ ≤ C₁ * A := by
    have hb := norm_iteratedFDeriv_bilinear_le_of_jet_bounds op₁ hf hd j hA
      (fun l hl => hfjet l (hl.trans hj)) (fun l hl => hdjet l (hl.trans hj))
    calc
      _ ≤ ‖op₁‖ * 2 ^ j * A * D := hb
      _ ≤ ‖op₁‖ * 2 ^ m * A * D := by
        gcongr
        norm_num
      _ = C₁ * A := by dsimp [C₁]; ring
  have hb := norm_iteratedFDeriv_bilinear_le_of_jet_bounds op₂ hfirst hd m
    (mul_nonneg hC₁ hA) hfirstjet hdjet
  exact hb.trans_eq (by ring)

theorem exists_bilinear_pullback_jet_bound (m : ℕ) {D : ℝ} (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E → F) (B : F → F →L[ℝ] F →L[ℝ] G) (x : E),
      ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ B (f x) →
      (∀ j ≤ m + 1, ‖iteratedFDeriv ℝ j f x‖ ≤ D) →
      ∀ A : ℝ, 0 ≤ A →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j B (f x)‖ ≤ A) →
      ‖iteratedFDeriv ℝ m (fun y => (B (f y)).bilinearComp
        (fderiv ℝ f y) (fderiv ℝ f y)) x‖ ≤ C * A := by
  let op₁ := bilinearPrecomposeFlip (E := E) (F := F) (G := F) (H := G)
  let op₂ := bilinearPrecomposeFlip (E := E) (F := F) (G := E) (H := G)
  have hop (b : F →L[ℝ] F →L[ℝ] G) (A : E →L[ℝ] F) :
      op₂ (op₁ b A) A = b.bilinearComp A A := by
    simp only [op₁, op₂, bilinearPrecomposeFlip_apply, ContinuousLinearMap.bilinearComp]
  let C₀ : ℝ := m.factorial * D ^ m
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  obtain ⟨C, hC, hbound⟩ := exists_two_bilinear_jet_bound (E := E) op₁ op₂ m hD0
  refine ⟨C * C₀, mul_nonneg hC hC₀, ?_⟩
  intro f B x hf hB hfjet A hA hBjet
  have hc := hB.comp x hf
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  have hcjet (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j (B ∘ f) x‖ ≤ C₀ * A := by
    have hb := norm_iteratedFDeriv_comp_le_of_contDiffAt hf hB j
      (fun l hl => hBjet l (hl.trans hj))
      (fun l hl hlm => (hfjet l (by omega)).trans
        (le_self_pow₀ hD (Nat.ne_of_gt hl)))
    calc
      _ ≤ j.factorial * A * D ^ j := hb
      _ ≤ m.factorial * A * D ^ m := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hA)
          (pow_le_pow_right₀ hD hj) (pow_nonneg hD0 _) (by positivity)
      _ = C₀ * A := by dsimp [C₀]; ring
  have hdjet (j : ℕ) (hj : j ≤ m) : ‖iteratedFDeriv ℝ j (fderiv ℝ f) x‖ ≤ D := by
    rw [norm_iteratedFDeriv_fderiv]
    exact hfjet (j + 1) (by omega)
  have hb := hbound (B ∘ f) (fderiv ℝ f) x hc hd hdjet (C₀ * A)
    (mul_nonneg hC₀ hA) hcjet
  simpa only [Function.comp_apply, hop, mul_assoc] using hb

end Poincare.Analysis.Calculus
