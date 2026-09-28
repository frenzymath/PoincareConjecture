import PoincareConjecture.Proofs.M35.Mathlib.PointJetBounds










set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



theorem jet_comp_tendsto_zero_of_bounded
    {r : ℕ} {f : ℕ → E → F} {g : ℕ → F → G} {p : ℕ → E}
    (hf : HasUniformJetBoundsAt r f p)
    (hcf : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (f k) (p k))
    (hcg : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (g k) (f k (p k)))
    (hg : ∀ m ≤ r, Tendsto (fun k => iteratedFDeriv ℝ m (g k) (f k (p k)))
      atTop (𝓝 0)) :
    Tendsto (fun k => iteratedFDeriv ℝ r (g k ∘ f k) (p k)) atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := hf.bound_all
  let B (k : ℕ) := ∑ m ∈ Finset.range (r + 1),
    ‖iteratedFDeriv ℝ m (g k) (f k (p k))‖
  have hB : Tendsto B atTop (𝓝 0) := by
    have hh := tendsto_finsetSum (Finset.range (r + 1)) (fun m hm =>
      (hg m (Nat.le_of_lt_succ (Finset.mem_range.mp hm))).norm)
    simpa only [norm_zero, Finset.sum_const_zero, B] using hh
  have hbound : ∀ᶠ k in atTop,
      ‖iteratedFDeriv ℝ r (g k ∘ f k) (p k)‖ ≤ r.factorial * B k * (max C 1) ^ r := by
    filter_upwards [hcf, hcg] with k hfk hgk
    have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
    apply CoordinateTransition.norm_iteratedFDeriv_comp_le_of_contDiffAt
      (hgk.of_le hr) (hfk.of_le hr)
    · intro m hm
      exact Finset.single_le_sum
        (f := fun j => ‖iteratedFDeriv ℝ j (g k) (f k (p k))‖)
        (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    · intro m hm hmr
      exact (hC m hmr k).trans ((le_max_left _ _).trans
        (le_self_pow₀ (le_max_right _ _) (Nat.ne_of_gt hm)))
  apply squeeze_zero_norm' hbound
  simpa only [mul_zero, zero_mul] using (tendsto_const_nhds.mul hB).mul
    (tendsto_const_nhds (x := (max C 1) ^ r))

private theorem norm_bilinear_jet_le (B : F →L[ℝ] G →L[ℝ] H)
    {f : E → F} {g : E → G} {p : E} (r : ℕ)
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p) :
    ‖iteratedFDeriv ℝ r (fun y => B (f y) (g y)) p‖ ≤
      ‖B‖ * ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j f p‖ * ‖iteratedFDeriv ℝ (r - j) g p‖ := by
  have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
  obtain ⟨Sf, hSf, hfs⟩ := hf.contDiffOn (m := r) hr (by simp)
  obtain ⟨Sg, hSg, hgs⟩ := hg.contDiffOn (m := r) hr (by simp)
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp (inter_mem hSf hSg)
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear
    (hfs.mono (hUsub.trans inter_subset_left))
    (hgs.mono (hUsub.trans inter_subset_right)) hU.uniqueDiffOn hpU (le_refl (r : ℕ∞ω))
  simpa only [iteratedFDerivWithin_of_isOpen _ hU hpU] using h



theorem jet_bilinear_tendsto_zero_of_bounded
    {r : ℕ} {f : ℕ → E → F} {g : ℕ → E → G} {p : ℕ → E}
    (B : F →L[ℝ] G →L[ℝ] H)
    (hf : ∀ m ≤ r, Tendsto (fun k => iteratedFDeriv ℝ m (f k) (p k)) atTop (𝓝 0))
    (hg : HasUniformJetBoundsAt r g p)
    (hcf : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (f k) (p k))
    (hcg : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (g k) (p k)) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun y => B (f k y) (g k y)) (p k))
      atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := hg.bound_all
  let A (k : ℕ) := ‖B‖ * ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) *
    ‖iteratedFDeriv ℝ j (f k) (p k)‖ * C
  have hA : Tendsto A atTop (𝓝 0) := by
    have hh := tendsto_finsetSum (Finset.range (r + 1)) (fun j hj =>
      ((tendsto_const_nhds (x := (r.choose j : ℝ))).mul
        (hf j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).norm).mul
          (tendsto_const_nhds (x := C)))
    simpa only [norm_zero, mul_zero, zero_mul, Finset.sum_const_zero, A] using
      (tendsto_const_nhds (x := ‖B‖)).mul hh
  apply squeeze_zero_norm' _ hA
  filter_upwards [hcf, hcg] with k hfk hgk
  apply (norm_bilinear_jet_le B r hfk hgk).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hC (r - j) (Nat.sub_le _ _) k)
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))

end PoincareConjecture.M35
