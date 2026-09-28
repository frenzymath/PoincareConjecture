import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Sard.Basic
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis

theorem scalar_flat_image_null
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {V s : Set E} {f : E → ℝ} {n : ℕ}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V) (hs : s ⊆ V)
    (hdim : Module.finrank ℝ E ≤ n)
    (hflat : ∀ x ∈ s, ∀ k, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k f x = 0) :
    volume (f '' s) = 0 := by
  let r : NNReal := ⟨(n + 1 : ℕ), by positivity⟩
  have hr : 0 < r := by
    change (0 : ℝ) < ((n + 1 : ℕ) : ℝ)
    positivity
  have hholder : ∀ x ∈ s, ∃ C : NNReal, ∃ t ∈ nhdsWithin x s,
      HolderOnWith C r f t := by
    intro x hx
    let C : ℝ := ‖iteratedFDeriv ℝ (n + 1) f x‖ + 1
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hD : ContinuousAt (iteratedFDeriv ℝ (n + 1) f) x :=
      ((hf x (hs hx)).contDiffAt (hV.mem_nhds (hs hx))).continuousAt_iteratedFDeriv
        (by exact_mod_cast (le_top : (n + 1 : ℕ∞) ≤ ⊤))
    have hbound : ∀ᶠ y in 𝓝 x, ‖iteratedFDeriv ℝ (n + 1) f y‖ < C :=
      hD.norm.eventually (gt_mem_nhds (lt_add_one _))
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
      (inter_mem (hV.mem_nhds (hs hx)) hbound)
    refine ⟨⟨C / (Nat.factorial n : ℝ), by positivity⟩,
      Metric.ball x ε ∩ s, ?_, ?_⟩
    · exact inter_mem (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hε))
        self_mem_nhdsWithin
    · apply holderOnWith_of_flat_iteratedFDeriv (convex_ball x ε) hC inter_subset_left
      · intro z hz
        exact ((hf z (hball hz).1).contDiffAt
          (hV.mem_nhds (hball hz).1)).of_le
            (by exact_mod_cast (le_top : (n + 1 : ℕ∞) ≤ ⊤))
      · intro z hz k hk hkn
        exact hflat z hz.2 k hk hkn
      · intro z hz
        exact (hball hz).2.le
  have hsource : dimH s ≤ (Module.finrank ℝ E : ENNReal) := by
    rw [← Real.dimH_univ_eq_finrank E]
    exact dimH_mono (subset_univ s)
  have hquot : (Module.finrank ℝ E : ENNReal) / r < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl (by positivity)) (Or.inl (by simp)), one_mul]
    change (Module.finrank ℝ E : ENNReal) < (n + 1 : ℕ)
    exact_mod_cast Nat.lt_succ_of_le hdim
  have himage : dimH (f '' s) < 1 :=
    ((dimH_image_le_of_locally_holder_on hr hholder).trans
      (ENNReal.div_le_div_right hsource r)).trans_lt hquot
  have hhausdorff :
      Measure.hausdorffMeasure (Module.finrank ℝ ℝ : ℝ) (f '' s) = 0 := by
    simpa using hausdorffMeasure_of_dimH_lt himage
  rw [Measure.isAddLeftInvariant_eq_smul volume
    (Measure.hausdorffMeasure (Module.finrank ℝ ℝ : ℝ))]
  rw [Measure.smul_apply, hhausdorff]
  simp

end Poincare.Analysis
