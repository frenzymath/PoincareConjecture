import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Operations









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.SpacetimeBounds

variable {D E F G : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_bilinear_le_of_contDiffAt
    (L : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F} {x : D}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (q : ℕ) :
    ‖iteratedFDeriv ℝ q (fun y => L (f y) (g y)) x‖ ≤
      ‖L‖ * ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (q - i) g x‖ := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := (q : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨t, ht, hgt⟩ := hg.contDiffOn (m := (q : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨v, hv, hvo, hxv⟩ := mem_nhds_iff.mp (inter_mem hs ht)
  have h := L.norm_iteratedFDerivWithin_le_of_bilinear
    (hfs.mono (fun _ hy => (hv hy).1)) (hgt.mono (fun _ hy => (hv hy).2))
    hvo.uniqueDiffOn hxv (le_refl (q : ℕ∞ω))
  simpa only [iteratedFDerivWithin_of_isOpen _ hvo hxv] using h



theorem norm_iteratedFDeriv_bilinear_le_affine_highest
    (L : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F} {x : D}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (q : ℕ)
    {A B A' B' T : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hA' : 0 ≤ A') (hB' : 0 ≤ B')
    (hT : 1 ≤ T)
    (hflow : ∀ j ≤ q, ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hglow : ∀ j ≤ q, ‖iteratedFDeriv ℝ j g x‖ ≤ B)
    (hftop : ‖iteratedFDeriv ℝ (q + 1) f x‖ ≤ A' * T)
    (hgtop : ‖iteratedFDeriv ℝ (q + 1) g x‖ ≤ B' * T) :
    ‖iteratedFDeriv ℝ (q + 1) (fun y => L (f y) (g y)) x‖ ≤
      (‖L‖ * (A * B' + A' * B + A * B) *
        ∑ i ∈ Finset.range (q + 2), ((q + 1).choose i : ℝ)) * T := by
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  let C : ℝ := A * B' + A' * B + A * B
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hAB' : 0 ≤ A * B' := mul_nonneg hA hB'
  have hA'B : 0 ≤ A' * B := mul_nonneg hA' hB
  have hterm (i : ℕ) (hi : i ≤ q + 1) :
      ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (q + 1 - i) g x‖ ≤ C * T := by
    by_cases hi0 : i = 0
    · subst i
      simp only [Nat.sub_zero]
      apply (mul_le_mul (hflow 0 (by omega)) hgtop (norm_nonneg _) hA).trans
      dsimp [C]
      nlinarith [mul_nonneg hA'B hT0, mul_nonneg hAB hT0]
    by_cases hitop : i = q + 1
    · subst i
      rw [Nat.sub_self]
      apply (mul_le_mul hftop (hglow 0 (by omega)) (norm_nonneg _)
        (mul_nonneg hA' hT0)).trans
      dsimp [C]
      nlinarith [mul_nonneg hAB' hT0, mul_nonneg hAB hT0]
    · apply (mul_le_mul (hflow i (by omega)) (hglow (q + 1 - i) (by omega))
        (norm_nonneg _) hA).trans
      dsimp [C]
      nlinarith [mul_nonneg hAB' hT0, mul_nonneg hA'B hT0]
  apply (norm_iteratedFDeriv_bilinear_le_of_contDiffAt L hf hg (q + 1)).trans
  calc
    _ ≤ ‖L‖ * ∑ i ∈ Finset.range (q + 2), ((q + 1).choose i : ℝ) * (C * T) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg L)
      apply Finset.sum_le_sum
      intro i hi
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hterm i (by have := Finset.mem_range.mp hi; omega))
        (Nat.cast_nonneg _)
    _ = _ := by simp only [← Finset.sum_mul, C]; ring



theorem norm_iteratedFDeriv_comp_le_affine_highest
    {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x))
    (q : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (houter : ∀ j ≤ q + 1, ‖iteratedFDeriv ℝ j g (f x)‖ ≤ A)
    (hinner : ∀ j, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℝ j f x‖ ≤ B ^ j) :
    ‖iteratedFDeriv ℝ (q + 1) (g ∘ f) x‖ ≤
      (∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * (i.factorial * A * B ^ i)) *
        (‖iteratedFDeriv ℝ (q + 1) f x‖ + B ^ (q + 1)) := by
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hdf : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  have hdg : ContDiffAt ℝ ∞ (fderiv ℝ g) (f x) := hg.fderiv_right (by simp)
  have hchain : fderiv ℝ (g ∘ f) =ᶠ[𝓝 x]
      (fun y => (fderiv ℝ g (f y)).comp (fderiv ℝ f y)) := by
    have hfe := (hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
    have hge := (hg.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
    filter_upwards [hfe, hf.continuousAt.tendsto.eventually hge] with y hfy hgy
    exact ((hgy.differentiableAt (by simp)).hasFDerivAt.comp y
      (hfy.differentiableAt (by simp)).hasFDerivAt).fderiv
  have hprod := norm_iteratedFDeriv_bilinear_le_of_contDiffAt
    (ContinuousLinearMap.compL ℝ E F G) (hdg.comp x hf) hdf q
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i ((fderiv ℝ g) ∘ f) x‖ *
      ‖iteratedFDeriv ℝ (q - i) (fderiv ℝ f) x‖ :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have hprod' := hprod.trans (mul_le_of_le_one_left hsum0
    (ContinuousLinearMap.norm_compL_le ℝ E F G))
  rw [← norm_iteratedFDeriv_fderiv]
  rw [(hchain.iteratedFDeriv (𝕜 := ℝ) q).eq_of_nhds]
  apply hprod'.trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hout : ‖iteratedFDeriv ℝ i ((fderiv ℝ g) ∘ f) x‖ ≤ i.factorial * A * B ^ i := by
    apply Poincare.Analysis.Calculus.norm_iteratedFDeriv_comp_le_of_contDiffAt hf hdg i
    · intro j hj
      rw [norm_iteratedFDeriv_fderiv]
      exact houter (j + 1) (by omega)
    · intro j hj hj'
      exact hinner j hj (hj'.trans hiq)
  have hin : ‖iteratedFDeriv ℝ (q - i) (fderiv ℝ f) x‖ ≤
      ‖iteratedFDeriv ℝ (q + 1) f x‖ + B ^ (q + 1) := by
    rw [norm_iteratedFDeriv_fderiv]
    by_cases hi0 : i = 0
    · subst i
      simp only [Nat.sub_zero]
      exact le_add_of_nonneg_right (pow_nonneg hB0 _)
    · apply (hinner (q - i + 1) (by omega) (by omega)).trans
      apply le_trans (pow_le_pow_right₀ hB (by omega : q - i + 1 ≤ q + 1))
      exact le_add_of_nonneg_left (norm_nonneg _)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hout (Nat.cast_nonneg _)) hin
    (norm_nonneg _) (by positivity)

end PoincareConjecture.SpacetimeBounds
