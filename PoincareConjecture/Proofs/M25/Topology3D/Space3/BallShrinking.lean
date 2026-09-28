import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartRadialField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem exists_ball_shrinking_isotopy (B : BallNeighborhoodChart E F) :
    ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F F ∞,
      ContDiff ℝ ∞ (fun p : ℝ × F => Φ p.1 p.2) ∧
      (∀ y, Φ 0 y = y) ∧
      (∀ x ∈ closedBall (0 : E) 1, ∀ t : ℝ, 0 ≤ t →
        Φ t (B.chart x) = B.chart (Real.exp (-t) • x)) ∧
      ∃ C : Set F, IsCompact C ∧ C ⊆ B.chart.target ∧
        ∀ t y, y ∉ C → Φ t y = y := by
  obtain ⟨R, hR, hRsource⟩ := B.exists_larger_ball
  obtain ⟨r, hr1, hrR⟩ := exists_between hR
  have hr0 : 0 < r := zero_lt_one.trans hr1
  have hrsource : closedBall (0 : E) r ⊆ B.chart.source :=
    (closedBall_subset_ball hrR).trans hRsource
  have hcompact : IsCompact (B.chart '' closedBall 0 r) :=
    (isCompact_closedBall (0 : E) r).image_of_continuousOn
      (B.chart.continuousOn.mono hrsource)
  have htarget : B.chart '' closedBall 0 r ⊆ B.chart.target := by
    rintro y ⟨x, hx, rfl⟩
    exact B.chart.map_source (hrsource hx)
  obtain ⟨W, hW, hWs, hsupp, hnear⟩ := exists_compactField_extension
    hcompact B.chart.open_target htarget (chartRadialField B.chart)
    (chartRadialField_contDiffOn B.chart B.smooth B.smooth_symm)
  have hagree (y : F) (hy : y ∈ B.chart '' closedBall 0 r) :
      W y = chartRadialField B.chart y :=
    (eventually_nhdsSet_iff_forall.mp hnear y hy).self_of_nhds
  obtain ⟨k, l, hk, hl⟩ := compactField_bounds W hW hWs
  let Φ := fun t => boundedFlowDiffeomorph W hk hl hW hWs t
  refine ⟨Φ, ?_, ?_, ?_, tsupport W, hWs.isCompact, hsupp, ?_⟩
  · exact (boundedFlow_contDiff W hk hl hW hWs).comp
      (contDiff_snd.prodMk contDiff_fst)
  · intro y
    exact boundedFlow_zero W hk hl y
  · intro x hx t ht
    have hscale (u : ℝ) (hu : -Real.log r < u) :
        Real.exp (-u) • x ∈ closedBall (0 : E) r := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-u) * ‖x‖ ≤ Real.exp (-u) * 1 :=
          mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) (Real.exp_pos _).le
        _ ≤ r := by
          rw [mul_one]
          exact ((Real.lt_log_iff_exp_lt hr0).mp (by linarith)).le
    have h0 : (0 : ℝ) ∈ Ioo (-Real.log r) (t + 1) :=
      ⟨by linarith [Real.log_pos hr1], by linarith⟩
    have htI : t ∈ Ioo (-Real.log r) (t + 1) :=
      ⟨by linarith [Real.log_pos hr1], by linarith⟩
    have htrack : EqOn (boundedFlow W hk hl (B.chart x))
        (fun u => B.chart (Real.exp (-u) • x)) (Ioo (-Real.log r) (t + 1)) := by
      apply ODE_solution_unique_of_mem_Ioo
        (v := fun _ y => W y) (s := fun _ => univ)
        (fun _ _ => hk.lipschitzOnWith) h0
      · exact fun u _ => ⟨boundedFlow_hasDerivAt W hk hl (B.chart x) u, mem_univ _⟩
      · intro u hu
        refine ⟨?_, mem_univ _⟩
        rw [hagree _ ⟨Real.exp (-u) • x, hscale u hu.1, rfl⟩]
        exact chartRadialField_track_hasDerivAt B.chart B.smooth x u
          (hrsource (hscale u hu.1))
      · simp only [boundedFlow_zero, neg_zero, Real.exp_zero, one_smul]
    exact htrack htI
  · intro t y hy
    exact boundedFlow_eq_self W hk hl y (image_eq_zero_of_notMem_tsupport hy) t

end PoincareConjecture.M25.Topology3D
