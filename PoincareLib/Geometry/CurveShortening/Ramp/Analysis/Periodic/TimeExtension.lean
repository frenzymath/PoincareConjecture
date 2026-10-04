import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Local.Gauge.Flow.TangentHalfSpaceExtension

/-!
# Finite-order periodic time extensions

The actual finite reflection and a time-only bump preserve the spatial
period. This supplies finite-order real label fields without assuming
a smooth circle manifold or an infinite-order extension. MT2007
Claim 19.1, p. 437;
`2026-09-22-periodic-moving-label-flow-route.md`, Section 1.
-/

set_option autoImplicit false

open Set Filter
open PoincareMT.HalfSpaceExtensionNative
open PoincareMT.TangentHalfSpaceExtensionNative
open scoped ContDiff Topology BigOperators

/-- A periodic scalar field on the initial half-slab has a global
finite-order extension preserving its period and the closed half-slab
values. MT2007 Claim 19.1, p. 437; periodic moving-label flow route,
Section 1. -/
theorem exists_periodic_initialSlab_extension
    {L T : ℝ} (_hL : 0 < L) (hT : 0 < T) (k : ℕ)
    (v : ℝ → ℝ → ℝ) (hper : ∀ t, Function.Periodic (v t) L)
    (hv : ContDiffOn ℝ k (Function.uncurry v) (Ico 0 T ×ˢ univ)) :
    ∃ Y : ℝ → ℝ → ℝ, ContDiff ℝ k (Function.uncurry Y) ∧
      (∀ t, Function.Periodic (Y t) L) ∧
      ∀ t ∈ Icc 0 (T / 2), ∀ x, Y t x = v t x := by
  obtain ⟨c, hc⟩ := exists_reflectionWeights k
  let β := extensionBump k hT
  let R := PoincareMT.HalfSpaceExtensionNative.reflectionExtension c (Function.uncurry v)
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
    · rw [PoincareMT.HalfSpaceExtensionNative.reflectionExtension_of_negative c
        (Function.uncurry v) (x := (t, x + L)) (lt_of_not_ge ht),
        PoincareMT.HalfSpaceExtensionNative.reflectionExtension_of_negative c
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
