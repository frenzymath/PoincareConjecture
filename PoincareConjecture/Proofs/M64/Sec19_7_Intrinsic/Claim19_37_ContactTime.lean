import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_Continuation














noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture




theorem m64Intrinsic_exists_first_annulus_contact
    {q : ℝ → AnnulusCoordinates} (hq : Continuous q)
    {R eta : ℝ} (hR : 0 < R) (heta : 0 < eta)
    (hinside : ∀ t ∈ Ioo (0 : ℝ) eta, 1 < ‖q t‖ ∧ ‖q t‖ < 2) :
    ∃ b : ℝ, 0 < b ∧ b ≤ R ∧
      (∀ t ∈ Ioo (0 : ℝ) b, 1 < ‖q t‖ ∧ ‖q t‖ < 2) ∧
      q b ∈ standardAnnulusDomain ∧
      (b = R ∨ ‖q b‖ = 1 ∨ ‖q b‖ = 2) := by
  let d := min (eta / 2) (R / 2)
  have hd : 0 < d := lt_min (half_pos heta) (half_pos hR)
  have hdEta : d < eta := (min_le_left _ _).trans_lt (half_lt_self heta)
  have hdR : d < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  let C : Set ℝ := Icc d R ∩ {t | t = R ∨ ‖q t‖ ≤ 1 ∨ 2 ≤ ‖q t‖}
  have hC : IsCompact C := by
    apply isCompact_Icc.inter_right
    exact (isClosed_eq continuous_id continuous_const).union
      ((isClosed_le hq.norm continuous_const).union (isClosed_le continuous_const hq.norm))
  have hRC : R ∈ C := ⟨⟨hdR.le, le_rfl⟩, Or.inl rfl⟩
  obtain ⟨b, hbC, hmin⟩ := hC.exists_isLeast ⟨R, hRC⟩
  have hb : 0 < b := hd.trans_le hbC.1.1
  have hbR : b ≤ R := hbC.1.2
  have hbefore (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) b) :
      1 < ‖q t‖ ∧ ‖q t‖ < 2 := by
    by_cases htd : t < d
    · exact hinside t ⟨ht.1, htd.trans hdEta⟩
    · by_contra hnot
      have htC : t ∈ C := by
        refine ⟨⟨le_of_not_gt htd, ht.2.le.trans hbR⟩, Or.inr ?_⟩
        by_cases hlow : 1 < ‖q t‖
        · exact Or.inr (le_of_not_gt (fun hu => hnot ⟨hlow, hu⟩))
        · exact Or.inl (le_of_not_gt hlow)
      exact (not_le_of_gt ht.2) (hmin htC)
  have hend : q b ∈ standardAnnulusDomain := by
    have hIoo : Ioo (0 : ℝ) b ∈ 𝓝[<] b := by
      rw [← nhdsWithin_Ioo_eq_nhdsLT hb]
      exact self_mem_nhdsWithin
    apply m64Intrinsic_standardAnnulus_isCompact.isClosed.mem_of_tendsto
      (b := 𝓝[<] b) (hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [hIoo] with t ht
    exact ⟨(hbefore t ht).1.le, (hbefore t ht).2.le⟩
  refine ⟨b, hb, hbR, hbefore, hend, ?_⟩
  rcases hbC.2 with htime | hlow | hupp
  · exact Or.inl htime
  · exact Or.inr (Or.inl (le_antisymm hlow hend.1))
  · exact Or.inr (Or.inr (le_antisymm hend.2 hupp))

end PoincareConjecture
