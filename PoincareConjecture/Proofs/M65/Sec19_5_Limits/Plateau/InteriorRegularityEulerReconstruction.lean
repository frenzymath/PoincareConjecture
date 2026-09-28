import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerEulerChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap

universe u

namespace PoincareConjecture.M65Euler

theorem exists_bounded_extension {N K : ℕ}
    {h : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin K)}
    {a : EuclideanSpace ℝ (Fin N)} (hh : ContDiffAt ℝ 1 h a) :
    ∃ (g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin K)) (C : NNReal),
      ContDiff ℝ 1 g ∧ (∀ y, ‖fderiv ℝ g y‖ ≤ (C : ℝ)) ∧ g =ᶠ[𝓝 a] h := by
  obtain ⟨r, hr, hrc⟩ := Metric.mem_nhds_iff.mp (hh.eventually (by simp))
  let χ : ContDiffBump a :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let g (y : EuclideanSpace ℝ (Fin N)) := χ y • h y
  have hg : ContDiff ℝ 1 g := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ ball a r
    · exact χ.contDiff.contDiffAt.smul (hrc hy)
    · have hys : y ∉ tsupport χ := by
        rw [χ.tsupport_eq]
        exact fun h => hy ((closedBall_subset_ball (by dsimp only [χ]; linarith)) h)
      have hz : g =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hys] with z hz
        change χ z • h z = 0
        simp only [hz, Pi.zero_apply, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  have hgc : HasCompactSupport g := χ.hasCompactSupport.smul_right
  obtain ⟨C, hC⟩ := (hgc.fderiv ℝ).exists_bound_of_continuous (hg.continuous_fderiv one_ne_zero)
  refine ⟨g, ⟨max C 0, le_max_right _ _⟩, hg, fun y => (hC y).trans (le_max_left _ _), ?_⟩
  filter_upwards [χ.eventuallyEq_one] with y hy
  change χ y • h y = h y
  simp only [hy, Pi.one_apply, one_smul]

def lift_target {M : Type u} {N : ℕ} {U : Set LoopPlane}
    (G : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin N) => y) U)
    (e : M → EuclideanSpace ℝ (Fin N)) (q : LoopPlane → M)
    (hq : (fun z => e (q z)) =ᵐ[volume.restrict U] G.value) :
    M65LocalWeakMap e U where
  value := q
  derivative := G.derivative
  value_memLp K hK hKU := (G.value_memLp K hK hKU).ae_eq
    (ae_restrict_of_ae_restrict_of_subset hKU hq.symm)
  derivative_memLp := G.derivative_memLp
  weak_derivative φ hc hs i j := by
    rw [G.weak_derivative φ hc hs i j]
    congr 1
    apply integral_congr_ae
    filter_upwards [hq] with z hz
    rw [hz]

theorem exists_inverse_chart_extension {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e) (p : M) :
    ∃ (B : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin N)) (C : NNReal)
      (W : Set (EuclideanSpace ℝ (Fin 3))),
      ContDiff ℝ 1 B ∧ (∀ y, ‖fderiv ℝ B y‖ ≤ (C : ℝ)) ∧
      IsOpen W ∧ extChartAt (𝓡 3) p p ∈ W ∧ W ⊆ (extChartAt (𝓡 3) p).target ∧
      ∀ y ∈ W, B y = e ((extChartAt (𝓡 3) p).symm y) ∧
        fderiv ℝ B y = fderiv ℝ (e ∘ (extChartAt (𝓡 3) p).symm) y := by
  let c := extChartAt (𝓡 3) p
  have hcsi : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm (c p) :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) p (mem_extChartAt_target p)).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target p))
  have hb : ContDiffAt ℝ 1 (e ∘ c.symm) (c p) :=
    (contMDiffAt_iff_contDiffAt.mp (he.contMDiffAt.comp (c p) hcsi)).of_le (by simp)
  obtain ⟨B, C, hB, hCb, heq⟩ := exists_bounded_extension hb
  have hmem : ∀ᶠ y in 𝓝 (c p), y ∈ c.target := extChartAt_target_mem_nhds (I := 𝓡 3) p
  have hnb : ∀ᶠ y in 𝓝 (c p), y ∈ c.target ∧ B =ᶠ[𝓝 y] e ∘ c.symm :=
    hmem.and heq.eventually_nhds
  obtain ⟨r, hr, hrc⟩ := Metric.mem_nhds_iff.mp hnb
  refine ⟨B, C, ball (c p) r, hB, hCb, isOpen_ball, mem_ball_self hr,
    fun y hy => (hrc hy).1, ?_⟩
  intro y hy
  exact ⟨(hrc hy).2.eq_of_nhds, (hrc hy).2.fderiv_eq⟩

end PoincareConjecture.M65Euler
