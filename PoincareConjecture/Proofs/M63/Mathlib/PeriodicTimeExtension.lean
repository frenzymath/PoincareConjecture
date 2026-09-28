import PoincareConjecture.Proofs.M03.Existence.TangentHalfSpaceExtensionNative

set_option autoImplicit false

open Set Filter
open PoincareConjecture.HalfSpaceExtensionNative
open PoincareConjecture.TangentHalfSpaceExtensionNative
open scoped ContDiff Topology BigOperators

theorem exists_periodic_initialSlab_extension
    {L T : ℝ} (_hL : 0 < L) (hT : 0 < T) (k : ℕ)
    (v : ℝ → ℝ → ℝ) (hper : ∀ t, Function.Periodic (v t) L)
    (hv : ContDiffOn ℝ k (Function.uncurry v) (Ico 0 T ×ˢ univ)) :
    ∃ Y : ℝ → ℝ → ℝ, ContDiff ℝ k (Function.uncurry Y) ∧
      (∀ t, Function.Periodic (Y t) L) ∧
      ∀ t ∈ Icc 0 (T / 2), ∀ x, Y t x = v t x := by
  obtain ⟨c, hc⟩ := exists_reflectionWeights k
  let β := extensionBump k hT
  let R := PoincareConjecture.HalfSpaceExtensionNative.reflectionExtension c (Function.uncurry v)
  let Y : ℝ → ℝ → ℝ := fun t x => β t * R (t, x)
  have hR := contDiffOn_reflectionExtension_slab k c hc (Function.uncurry v) hT hv
  have hY : ContDiff ℝ k (Function.uncurry Y) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z.1 ∈ tsupport β
    · have htime := extensionBump_support_subset k hT hz
      have hRat : ContDiffAt ℝ k R z :=
        hR.contDiffAt (prod_mem_nhds (isOpen_Ioo.mem_nhds htime) univ_mem)
      have hβ : ContDiffAt ℝ k (fun w : ℝ × ℝ => β w.1) z :=
        β.contDiff.contDiffAt.comp z contDiffAt_fst
      exact hβ.mul hRat
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hzero : ∀ᶠ t in 𝓝 z.1, β t = 0 := notMem_tsupport_iff_eventuallyEq.mp hz
      filter_upwards [continuous_fst.continuousAt.eventually hzero] with w hw
      simp only [Function.uncurry_def, Y, hw, zero_mul]
  have hRper (t x : ℝ) : R (t, x + L) = R (t, x) := by
    dsimp only [R]
    by_cases ht : 0 ≤ t
    · rw [reflectionExtension_eqOn_upper c (Function.uncurry v)
          (x := (t, x + L)) ⟨ht, mem_univ _⟩,
        reflectionExtension_eqOn_upper c (Function.uncurry v)
          (x := (t, x)) ⟨ht, mem_univ _⟩]
      exact hper t x
    · rw [PoincareConjecture.HalfSpaceExtensionNative.reflectionExtension_of_negative c
        (Function.uncurry v) (x := (t, x + L)) (lt_of_not_ge ht),
        PoincareConjecture.HalfSpaceExtensionNative.reflectionExtension_of_negative c
          (Function.uncurry v) (x := (t, x)) (lt_of_not_ge ht)]
      apply Finset.sum_congr rfl
      intro j _
      simp only [timeScale_apply, Function.uncurry_def, hper _ x]
  refine ⟨Y, hY, ?_, ?_⟩
  · intro t x
    change β t * R (t, x + L) = β t * R (t, x)
    rw [hRper]
  · intro t ht x
    change β t * R (t, x) = v t x
    rw [show β t = 1 from extensionBump_one k hT ht, one_mul]
    exact reflectionExtension_eqOn_upper c (Function.uncurry v) ⟨ht.1, mem_univ _⟩
