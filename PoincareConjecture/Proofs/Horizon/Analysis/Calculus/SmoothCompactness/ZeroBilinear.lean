import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Pullback








set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

private theorem bilinear_jet_bound
    {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖ * ∑ l ∈ Finset.range (m + 1), (m.choose l : ℝ) *
        ‖iteratedFDeriv ℝ l f x‖ * ‖iteratedFDeriv ℝ (m - l) g x‖ := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := (m : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨t, ht, hgt⟩ := hg.contDiffOn (m := (m : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨v, hv, hvo, hxv⟩ := mem_nhds_iff.mp (inter_mem hs ht)
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear
    (hfs.mono (fun _ hy => (hv hy).1)) (hgt.mono (fun _ hy => (hv hy).2))
    hvo.uniqueDiffOn hxv (le_refl (m : ℕ∞ω))
  simpa only [iteratedFDerivWithin_of_isOpen _ hvo hxv] using h




theorem smooth_convergence_zero_bilinear_on_open
    {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {U : Set E} (hU : IsOpen U) (B : F →L[ℝ] G →L[ℝ] H)
    {f : ℕ → E → F} {g : ℕ → E → G}
    (hflocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) W)
    (hglocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (g k) W)
    (hfjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k)) (fun _ => 0) atTop K)
    (hgbound : ∀ K, IsCompact K → K ⊆ U → ∀ m, ∃ C : ℝ,
      ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (g k) x‖ ≤ C) :
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (fun y => B (f k y) (g k y)) W) ∧
      ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (fun y => B (f k y) (g k y)))
        (fun _ => 0) atTop K := by
  classical
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨V, hV, hxV, hf⟩ := hflocal x hx
    obtain ⟨W, hW, hxW, hg⟩ := hglocal x hx
    refine ⟨U ∩ V ∩ W, (hU.inter hV).inter hW, ⟨⟨hx, hxV⟩, hxW⟩,
      fun _ hy => hy.1.1, ?_⟩
    filter_upwards [hf, hg] with k hkf hkg
    exact B.isBoundedBilinearMap.contDiff.comp₂_contDiffOn
      (hkf.mono fun _ hy => hy.1.2) (hkg.mono fun _ hy => hy.2)
  · intro m K hK hKU
    choose A hA using fun j : Fin (m + 1) => hgbound K hK hKU j
    let D : ℝ := ∑ j : Fin (m + 1), max (A j) 0
    have hD : 0 ≤ D := Finset.sum_nonneg fun j _ => le_max_right _ _
    have hgb : ∀ᶠ k in atTop, ∀ j, j ≤ m → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ j (g k) x‖ ≤ D := by
      filter_upwards [eventually_all.mpr hA] with k hk j hj x hx
      let i : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
      exact (hk i x hx).trans ((le_max_left _ _).trans
        (Finset.single_le_sum (fun q _ => le_max_right (A q) 0) (Finset.mem_univ i)))
    let C : ℝ := ‖B‖ * (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ)) * D
    have hC : 0 ≤ C := by dsimp [C]; positivity
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    let δ : ℝ := ε / (C + 1)
    have hC1 : 0 < C + 1 := by linarith
    have hδ : 0 < δ := div_pos hε hC1
    have hfsmall : ∀ᶠ k in atTop, ∀ j : Fin (m + 1), ∀ x ∈ K,
        ‖iteratedFDeriv ℝ (j : ℕ) (f k) x‖ < δ := by
      apply eventually_all.mpr
      intro j
      simpa only [dist_zero_left] using
        Metric.tendstoUniformlyOn_iff.mp (hfjet j K hK hKU) δ hδ
    filter_upwards [hfsmall, hgb,
      eventually_contDiffAt_on_compact hK hKU hflocal,
      eventually_contDiffAt_on_compact hK hKU hglocal]
      with k hkf hkg hkfs hkgs x hx
    simp only [dist_zero_left]
    calc
      ‖iteratedFDeriv ℝ m (fun y => B (f k y) (g k y)) x‖ ≤
          ‖B‖ * ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
            ‖iteratedFDeriv ℝ j (f k) x‖ *
            ‖iteratedFDeriv ℝ (m - j) (g k) x‖ :=
        bilinear_jet_bound B (hkfs x hx) (hkgs x hx) m
      _ ≤ ‖B‖ * ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * δ * D := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left
            (hkf ⟨j, Finset.mem_range.mp hj⟩ x hx).le (by positivity))
          (hkg (m - j) (Nat.sub_le _ _) x hx) (norm_nonneg _) (by positivity)
      _ = C * δ := by
        dsimp [C]
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        ring
      _ < (C + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one C) hδ
      _ = ε := by dsimp [δ]; field_simp

end Poincare.Analysis.Calculus
