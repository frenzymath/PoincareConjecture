import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.EmptyBigon



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

theorem exists_highest_generic_annular_axis {f : ℝ → ℝ}
    (hf : FinitePiecewiseAffineOn f (Icc 0 1)) {c : ℝ}
    (hreg : ∀ (x : ℝ) (k : ℤ), x ∈ Icc (0 : ℝ) 1 → f x = c + 32 * (k : ℝ) →
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, f y - (c + 32 * (k : ℝ)) = m * (y - x))
    (habove : ∃ t ∈ Icc (0 : ℝ) 1, c < f t) :
    ∃ (k : ℤ) (d : ℝ), 0 ≤ k ∧ 0 < d ∧ d < 32 ∧
      (∃ t ∈ Icc (0 : ℝ) 1, c + 32 * (k : ℝ) < f t) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, f t - (c + 32 * (k : ℝ)) ≤ d := by
  have himage := isCompact_Icc.image_of_continuousOn hf.continuousOn
  obtain ⟨M, ⟨x, hx, hfx⟩, hmax⟩ := himage.exists_isGreatest
    ⟨f 0, mem_image_of_mem f ⟨le_rfl, zero_le_one⟩⟩
  have hbound (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) : f y ≤ M :=
    hmax (mem_image_of_mem f hy)
  have hMc : c < M := by
    obtain ⟨t, ht, hct⟩ := habove
    exact hct.trans_le (hbound t ht)
  have hMne (k : ℤ) : M ≠ c + 32 * (k : ℝ) := by
    intro heq
    obtain ⟨a, b, m, ha, hax, hxb, hb, hm, hformula⟩ := hreg x k hx (hfx.trans heq)
    rcases lt_or_gt_of_ne hm with hm | hm
    · have hfa := hformula a ⟨le_rfl, (hax.trans hxb).le⟩
      have hba := hbound a ⟨ha, (hax.trans hxb).le.trans hb⟩
      have hp := mul_pos_of_neg_of_neg hm (sub_neg.mpr hax)
      rw [heq] at hba
      linarith
    · have hfb := hformula b ⟨(hax.trans hxb).le, le_rfl⟩
      have hbb := hbound b ⟨ha.trans (hax.trans hxb).le, hb⟩
      have hp := mul_pos hm (sub_pos.mpr hxb)
      rw [heq] at hbb
      linarith
  let k : ℤ := ⌊(M - c) / 32⌋
  have hk0 : 0 ≤ k := Int.floor_nonneg.mpr (by linarith)
  have hlo := Int.floor_le ((M - c) / 32)
  have hhi := Int.lt_floor_add_one ((M - c) / 32)
  change (k : ℝ) ≤ (M - c) / 32 at hlo
  change (M - c) / 32 < (k : ℝ) + 1 at hhi
  have hstrict : c + 32 * (k : ℝ) < M :=
    lt_of_le_of_ne (by linarith) (Ne.symm (hMne k))
  refine ⟨k, M - (c + 32 * (k : ℝ)), hk0, by linarith, by linarith,
    ⟨x, hx, hfx.symm ▸ hstrict⟩, ?_⟩
  intro t ht
  linarith [hbound t ht]

theorem exists_narrow_empty_returning_bigon_of_lift {r : ℝ → ℝ × ℝ}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) (hi : InjOn r (Icc 0 1))
    (hheight : ∀ t ∈ Icc (0 : ℝ) 1, (r t).2 ∈ Icc (-1 : ℝ) 1)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, (r t).2 ∈ Ioo (-1 : ℝ) 1)
    (hbottom : (r 0).2 = -1) (htop : (r 1).2 = 1)
    (hang0 : (r 0).1 = 0) (hang1 : (r 1).1 = 0)
    (htranslate : ∀ (s t : ℝ), s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      ∀ k : ℤ, r s = r t + (32 * (k : ℝ), 0) → s = t ∧ k = 0)
    {c : ℝ} (hc : 0 < c)
    (hfinite : {x ∈ Icc (0 : ℝ) 1 | ∃ k : ℤ, (r x).1 = c + 32 * (k : ℝ)}.Finite)
    (hreg : ∀ (x : ℝ) (k : ℤ), x ∈ Icc (0 : ℝ) 1 → (r x).1 = c + 32 * (k : ℝ) →
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, (r y).1 - (c + 32 * (k : ℝ)) = m * (y - x))
    (habove : ∃ t ∈ Icc (0 : ℝ) 1, c < (r t).1) :
    ∃ (c₀ d : ℝ) (k : ℤ) (a b : ℝ) (u v : ℝ × ℝ) (B : Set (ℝ × ℝ)),
      c ≤ c₀ ∧ (∃ n : ℤ, c₀ = c + 32 * (n : ℝ)) ∧
      0 < d ∧ d < 32 ∧ 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ u.1 < v.1 ∧
      {u, v} = ({annularLiftAboveAxis r (c₀ + 32 * (k : ℝ)) a,
        annularLiftAboveAxis r (c₀ + 32 * (k : ℝ)) b} : Set (ℝ × ℝ)) ∧
      IsFinitePLBallPair (ℝ × ℝ) B
        ((annularLiftAboveAxis r (c₀ + 32 * (k : ℝ)) '' Icc a b) ∪ segment ℝ u v) ∧
      IsCompact B ∧ B ⊆ Ioo (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) d ∧
      B ∩ (Prod.snd ⁻¹' ({0} : Set ℝ)) = segment ℝ u v ∧
      B ∩ (⋃ j : ℤ, annularLiftAboveAxis r (c₀ + 32 * (j : ℝ)) '' Icc (0 : ℝ) 1) =
        annularLiftAboveAxis r (c₀ + 32 * (k : ℝ)) '' Icc a b ∧
      (⋃ j : ℤ, annularLiftAboveAxis r (c₀ + 32 * (j : ℝ)) '' Icc (0 : ℝ) 1) ∩
        segment ℝ u v = {u, v} := by
  have hf : FinitePiecewiseAffineOn (fun t => (r t).1) (Icc 0 1) :=
    hr.postcomp (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  obtain ⟨n, d, hn, hd, hd32, habove', hband⟩ :=
    exists_highest_generic_annular_axis hf hreg habove
  let c₀ := c + 32 * (n : ℝ)
  have hc₀ : c ≤ c₀ := by
    have hn' : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    dsimp [c₀]; linarith
  have hshift (j : ℤ) : c₀ + 32 * (j : ℝ) = c + 32 * ((n + j : ℤ) : ℝ) := by
    dsimp [c₀]
    rw [Int.cast_add]
    ring
  have hfinite' (j : ℤ) : {t ∈ Icc (0 : ℝ) 1 | (r t).1 = c₀ + 32 * (j : ℝ)}.Finite := by
    rw [hshift]
    exact hfinite.subset (fun t ht => ⟨ht.1, n + j, ht.2⟩)
  have hreg' (j : ℤ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1)
      (hfx : (r x).1 = c₀ + 32 * (j : ℝ)) :
      ∃ u v m : ℝ, u < x ∧ x < v ∧ m ≠ 0 ∧
        ∀ y ∈ Icc u v, (r y).1 - (c₀ + 32 * (j : ℝ)) = m * (y - x) := by
    rw [hshift] at hfx ⊢
    obtain ⟨u, v, m, _, hux, hxv, _, hm, hformula⟩ := hreg x (n + j) hx hfx
    exact ⟨u, v, m, hux, hxv, hm, hformula⟩
  have hend0 (j : ℤ) : (r 0).1 ≠ c₀ + 32 * (j : ℝ) := by
    intro h
    rw [hshift] at h
    obtain ⟨u, v, m, hu, hux, _⟩ := hreg 0 (n + j) ⟨le_rfl, zero_le_one⟩ h
    linarith
  have hend1 (j : ℤ) : (r 1).1 ≠ c₀ + 32 * (j : ℝ) := by
    intro h
    rw [hshift] at h
    obtain ⟨u, v, m, _, _, hxv, hv, _⟩ := hreg 1 (n + j) ⟨zero_le_one, le_rfl⟩ h
    linarith
  obtain ⟨k, a, b, u, v, B, hresult⟩ := exists_empty_returning_bigon_of_lift
    hr hi hheight hproper hbottom htop htranslate
    (by rw [hang0]; exact hc.trans_le hc₀)
    (by rw [hang1]; exact hc.trans_le hc₀)
    habove' hband hend0 hend1 hfinite' hreg'
  exact ⟨c₀, d, k, a, b, u, v, B, hc₀, ⟨n, rfl⟩, hd, hd32, hresult⟩

end PoincareConjecture.M76.Dehn
