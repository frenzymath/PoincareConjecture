import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Flow
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]

theorem exists_supported_ball_shrinking_isotopy
    {r R c : Real} (hr : 0 < r) (hrR : r < R) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ F : Real -> Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
      (∀ x, F 0 x = x) ∧
      ContDiff Real ∞ (fun p : Real × E => F p.1 p.2) ∧
      (∀ t x, x ∉ closedBall (0 : E) R -> F t x = x) ∧
      ∀ t ∈ Icc (0 : Real) 1, ∀ x ∈ closedBall (0 : E) r,
        F t x = Real.exp (t * Real.log c) • x := by
  let chi : ContDiffBump (0 : E) := ⟨r, R, hr, hrR⟩
  let V : E -> E := fun x => (Real.log c * chi x) • x
  have hV : ContDiff Real ∞ V := (contDiff_const.mul chi.contDiff).smul contDiff_id
  have hzero (x : E) (hx : x ∉ closedBall (0 : E) R) : V x = 0 := by
    have he : chi x = 0 := chi.zero_of_le_dist (le_of_lt (not_le.mp hx))
    simp [V, he]
  have hK : IsCompact (closedBall (0 : E) R) := isCompact_closedBall 0 R
  obtain ⟨Phi, hi, hs, ho, hfix⟩ :=
    exists_diffeomorph_evolution_of_compact_spatial_support
      (fun p : Real × E => V p.2) (hV.comp contDiff_snd) hK (fun _ => hzero)
  have hVc : HasCompactSupport V := by
    apply hK.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (hzero x hn)
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hV (by simp)
  refine ⟨Phi 0, hi 0, hs 0, hfix 0, ?_⟩
  intro t ht x hx
  let g : Real -> E := fun t => Real.exp (t * Real.log c) • x
  have hgBall (t : Real) (ht : t ∈ Icc (0 : Real) 1) : g t ∈ closedBall (0 : E) r := by
    have hlog : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
    have he : Real.exp (t * Real.log c) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonneg_of_nonpos ht.1 hlog)
    rw [mem_closedBall, dist_zero_right] at hx ⊢
    calc
      ‖g t‖ = Real.exp (t * Real.log c) * ‖x‖ := by
        simp [g, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ ≤ r := by simpa using hx
  have hgder (t : Real) : HasDerivAt g
      ((Real.exp (t * Real.log c) * Real.log c) • x) t := by
    simpa only [g, id_eq, one_mul] using
      (((hasDerivAt_id t).mul_const (Real.log c)).exp).smul_const x
  have heq := ODE_solution_unique (v := fun _ => V) (fun _ => hL)
    (f := fun t => Phi 0 t x) (g := g)
    ((hs 0).continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    (fun t _ => (ho 0 x t).hasDerivWithinAt)
    ((continuous_id.mul continuous_const).rexp.smul continuous_const).continuousOn
    (fun t ht => by
      have hchi : chi (g t) = 1 := chi.one_of_mem_closedBall
        (hgBall t (Ico_subset_Icc_self ht))
      have hvel : V (g t) = (Real.exp (t * Real.log c) * Real.log c) • x := by
        simp only [V, hchi, g, smul_smul, mul_comm, one_mul]
      rw [hvel]
      exact (hgder t).hasDerivWithinAt)
    (by simp [hi, g])
  exact heq ht

theorem exists_supported_ball_shrinking
    {r R c : Real} (hr : 0 < r) (hrR : r < R) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ F : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
      (∀ x ∈ closedBall (0 : E) r, F x = c • x) ∧
      ∀ x ∉ closedBall (0 : E) R, F x = x := by
  obtain ⟨F, _, _, hfix, hmotion⟩ :=
    exists_supported_ball_shrinking_isotopy (E := E) hr hrR hc hc1
  refine ⟨F 1, fun x hx => ?_, hfix 1⟩
  simpa [Real.exp_log hc] using hmotion 1 (by simp) x hx

end Poincare.Manifold.Schoenflies
