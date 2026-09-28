import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Pullback









set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

theorem smooth_zero_convergence_comp_of_bounded
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U V : Set E} (hV : IsOpen V)
    {f : ℕ → E → F}
    {g : ℕ → E → E}
    (hflocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) W)
    (hglocal : ∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (g k) W)
    (hfjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k))
      (iteratedFDeriv ℝ m (fun _ => (0 : F))) atTop K)
    (hgbound : ∀ K, IsCompact K → K ⊆ V → ∀ m, ∃ B : ℝ,
      ∀ᶠ i in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (g i) x‖ ≤ B)
    (htarget : ∀ K, IsCompact K → K ⊆ V → ∃ T,
      IsCompact T ∧ T ⊆ U ∧ ∀ᶠ k in atTop, MapsTo (g k) K T) :
    (∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k ∘ g k) W) ∧
      ∀ m K, IsCompact K → K ⊆ V → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (f k ∘ g k))
        (iteratedFDeriv ℝ m (fun _ => (0 : F))) atTop K := by
  have hlocal : ∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k ∘ g k) W := by
    intro x hx
    obtain ⟨K, hK, hxK, hKV⟩ := exists_compact_between isCompact_singleton hV
      (singleton_subset_iff.mpr hx)
    obtain ⟨T, hT, hTU, hmap⟩ := htarget K hK hKV
    refine ⟨interior K, isOpen_interior, hxK (mem_singleton x), interior_subset.trans hKV, ?_⟩
    filter_upwards [hmap, eventually_contDiffAt_on_compact hT hTU hflocal,
      eventually_contDiffAt_on_compact hK hKV hglocal] with k hkmap hkf hkg y hy
    exact ((hkf _ (hkmap (interior_subset hy))).comp y
      (hkg y (interior_subset hy))).contDiffWithinAt
  refine ⟨hlocal, ?_⟩
  intro m K hK hKV
  obtain ⟨T, hT, hTU, hmap⟩ := htarget K hK hKV
  choose A hA using fun j : Fin (m + 1) => hgbound K hK hKV j
  let D : ℝ := ∑ j : Fin (m + 1), max (A j) 0
  have hD : 0 ≤ D := Finset.sum_nonneg fun j _ => le_max_right _ _
  have hgb : ∀ᶠ i in atTop, ∀ j, j ≤ m → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (g i) x‖ ≤ D := by
    filter_upwards [eventually_all.mpr hA] with i hi j hj x hx
    let a : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    exact (hi a x hx).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun b _ => le_max_right (A b) 0) (Finset.mem_univ a)))
  let C : ℝ := m.factorial * (max D 1) ^ m
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ : ℝ := ε / (C + 1)
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hC1
  have hfsmall : ∀ᶠ i in atTop, ∀ j : Fin (m + 1), ∀ x ∈ T,
      ‖iteratedFDeriv ℝ (j : ℕ) (f i) x‖ < δ := by
    apply eventually_all.mpr
    intro j
    simpa using Metric.tendstoUniformlyOn_iff.mp (hfjet j T hT hTU) δ hδ
  filter_upwards [hmap, hgb, hfsmall, eventually_contDiffAt_on_compact hT hTU hflocal,
    eventually_contDiffAt_on_compact hK hKV hglocal] with i himap hig hif hisf hisg x hx
  have hnorm : ‖iteratedFDeriv ℝ m (f i ∘ g i) x‖ ≤ C * δ := by
    calc
      _ ≤ m.factorial * δ * (max D 1) ^ m :=
        norm_iteratedFDeriv_comp_le_of_contDiffAt (hisg x hx) (hisf _ (himap hx)) m
          (fun j hj => (hif ⟨j, Nat.lt_succ_of_le hj⟩ _ (himap hx)).le)
          (fun j hj hjm => (hig j hjm x hx).trans ((le_max_left _ _).trans
            (le_self_pow₀ (le_max_right D 1) (Nat.ne_of_gt hj))))
      _ = C * δ := by dsimp [C]; ring
  have hsmall : ‖iteratedFDeriv ℝ m (f i ∘ g i) x‖ < ε := calc
    _ ≤ C * δ := hnorm
    _ < (C + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one C) hδ
    _ = ε := by dsimp [δ]; field_simp
  simpa using hsmall

end Poincare.Analysis.Calculus
