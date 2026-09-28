import PoincareConjecture.Proofs.M10.ChartMetricBounds
import PoincareConjecture.Proofs.M10.ChartBarrierHessian
import PoincareConjecture.Proofs.M10.ContactSemiconcavity
import PoincareConjecture.Proofs.M10.Continuity

set_option autoImplicit false

open Set Filter Metric
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}

set_option backward.isDefEq.respectTransparency false in

theorem reducedLength_chart_semiconcave
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (p q₀ : M) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    let e := extChartAt (𝓡 n) q₀
    ∃ r : ℝ, 0 < r ∧ ball (e q₀) r ⊆ e.target ∧ ∃ K : ℝ, 0 ≤ K ∧
      ConcaveOn ℝ (ball (e q₀) r)
        (fun y ↦ reducedLength F T p (e.symm y) τ - K * ‖y‖ ^ 2 / 2) := by
  let e := extChartAt (𝓡 n) q₀
  let u := fun y ↦ reducedLength F T p (e.symm y) τ
  obtain ⟨N, hN, hqN, _, C, hC, hbar⟩ :=
    hDifferential.local_upper_barrier_bounds p (q₀, τ) ⟨mem_univ _, hτ, hmax⟩
  obtain ⟨S, hS, hCS, hmetric⟩ := chartMetricForm_eventually_bounded (F.metric (T - τ)) q₀ hC
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hN' : ∀ᶠ y in 𝓝 (e q₀), (e.symm y, τ) ∈ N := by
    have ht := (continuousAt_extChartAt_symm (I := 𝓡 n) q₀).prodMk
      (continuousAt_const (y := τ))
    have hmem : (e.symm (e q₀), τ) ∈ N := by
      simpa only [e, extChartAt_to_inv] using hqN
    exact ht (hN.mem_nhds hmem)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hmetric hN')
  have htarget : ball (e q₀) r ⊆ e.target := fun y hy ↦ (hball hy).1.1
  let K := S ^ 2 + 2 * S ^ 3
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨r, hr, htarget, K, hK, ?_⟩
  apply concaveOn_sub_norm_sq_of_upper_contacts (convex_ball _ _)
  · apply (reducedLength_continuousOn hL hDifferential p).comp
      (((continuousOn_extChartAt_symm q₀).mono htarget).prodMk continuousOn_const)
    intro y _
    exact ⟨mem_univ _, hτ, hmax⟩
  · intro y hy
    have hyT := htarget hy
    obtain ⟨_, hB, hDB, hI⟩ := (hball hy).1
    obtain ⟨β, _, hgrad, hH⟩ := hbar (e.symm y, τ) (hball hy).2
    let b := (fun q ↦ β.representative (q, τ)) ∘ e.symm
    have hb : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2
        (fun q ↦ β.representative (q, τ)) (e.symm y) :=
      β.representative_space_smooth.of_le (by decide : (2 : ℕ∞ω) ≤ ∞)
    refine ⟨b, β.touches, ?_, fixedChart_scalar_contDiffAt q₀ hyT hb, ?_⟩
    · have hdom : ∀ᶠ z : M × ℝ in 𝓝 (e.symm y, τ),
          reducedLength F T p z.1 z.2 ≤ β.representative z :=
        Filter.eventually_of_mem (β.neighborhood_open.mem_nhds β.center_mem) β.dominates
      exact ((continuousAt_extChartAt_symm'' (I := 𝓡 n) hyT).prodMk continuousAt_const) hdom
    · intro v
      exact chart_barrier_second_fderiv_le q₀ hyT hb hS0 hB hDB hI (hgrad.trans hCS)
        (fun w ↦ (hH w).trans (mul_le_mul_of_nonneg_right hCS (by
          by_cases hw : w = 0
          · simp [hw]
          · exact ((F.metric (T - τ)).pos _ _ hw).le))) v

end PoincareConjecture.M10
