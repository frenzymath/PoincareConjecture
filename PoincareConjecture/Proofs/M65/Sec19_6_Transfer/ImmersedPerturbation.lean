import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationGeneric

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture

private theorem enlarge_loop_time_interval {J : Set ℝ} (hJ : IsOpen J)
    (s t : ℝ) (hst : s ≤ t) (hI : Icc s t ⊆ J) :
    ∃ ell r : ℝ, ell < s ∧ t < r ∧ Icc ell r ⊆ J := by
  obtain ⟨es, hes, hsJ⟩ := Metric.mem_nhds_iff.mp
    (hJ.mem_nhds (hI (left_mem_Icc.mpr hst)))
  obtain ⟨et, het, htJ⟩ := Metric.mem_nhds_iff.mp
    (hJ.mem_nhds (hI (right_mem_Icc.mpr hst)))
  refine ⟨s - es / 2, t + et / 2, by linarith, by linarith, ?_⟩
  intro x hx
  by_cases hxs : x < s
  · apply hsJ
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1]
  · by_cases htx : t < x
    · apply htJ
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.2]
    · exact hI ⟨le_of_not_gt hxs, le_of_not_gt htx⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]
  {a b : ℝ} {J : Set ℝ} {s t : ℝ}

theorem m65Exists_generic_loop_perturbation (F : RicciFlow 3 M (Icc a b))
    (hJ : IsOpen J) (_hJF : J ⊆ Ioo a b) (C : M65SmoothFilledLoopFamily F J)
    (hst : s ≤ t) (hI : Icc s t ⊆ J) :
    ∃ (ell r : ℝ) (N : ℕ) (delta : ℝ)
        (Gamma : (Fin N → ℝ) → ℝ → C1FreeLoopSpace (M := M)) (Bad : Set (Fin N → ℝ)),
      ell < s ∧ t < r ∧ Icc ell r ⊆ J ∧ 0 < delta ∧
      ContMDiffOn 𝓘(ℝ, (Fin N → ℝ) × (ℝ × ℝ)) (𝓡 3) ∞
        (fun z => periodicFreeLoop (Gamma z.1 z.2.2) z.2.1)
        (ball 0 delta ×ˢ (univ ×ˢ Ioo ell r)) ∧
      (∀ q ∈ Ioo ell r, ∀ x,
        periodicFreeLoop (Gamma 0 q) x = periodicFreeLoop (C.loops q) x) ∧
      (∀ p ∈ ball 0 delta, ∀ q ∈ Ioo ell r, ∀ x,
        curveVelocity (n := 3) (periodicFreeLoop (Gamma p q)) x ≠ 0) ∧
      volume Bad = 0 ∧ ∀ p ∈ ball 0 delta, p ∉ Bad →
        {q | q ∈ Icc s t ∧ ¬Function.Injective (Gamma p q : LoopCircle → M)}.Finite := by
  obtain ⟨ell, r, hell, htr, hKJ⟩ := enlarge_loop_time_interval hJ s t hst hI
  obtain ⟨N, delta, Gamma, Bad, hdelta, hGamma, hbase, himmersed, hBad, hfinite⟩ :=
    M65Perturbation.exists_generic_control_family C hJ (Icc ell r) isCompact_Icc hKJ
  have hOJ : Ioo ell r ⊆ J := Ioo_subset_Icc_self.trans hKJ
  refine ⟨ell, r, N, delta, Gamma, Bad, hell, htr, hKJ, hdelta,
    hGamma.mono (prod_mono Subset.rfl (prod_mono Subset.rfl hOJ)),
    fun q hq => hbase q (hOJ hq),
    fun p hp q hq => himmersed p hp q (Ioo_subset_Icc_self hq), hBad, ?_⟩
  intro p hp hpBad
  exact (hfinite p hp hpBad).subset
    (fun _ hq => ⟨Icc_subset_Icc hell.le htr.le hq.1, hq.2⟩)

end PoincareConjecture
