import PoincareConjecture.Proofs.M09.TimeDependentFlow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM








set_option autoImplicit false

open scoped ContDiff Topology
open Set Metric

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_uniform_local_linear_solution (U : Set ℝ) (hU : IsOpen U)
    (A : ℝ → E →L[ℝ] E) (hA : ContDiffOn ℝ ∞ A U) (s0 : ℝ) (hs0 : s0 ∈ U) :
    ∃ (W : Set ℝ) (d : ℝ), IsOpen W ∧ s0 ∈ W ∧ W ⊆ U ∧ 0 < d ∧
      ∀ t0 ∈ W, ∀ v : E, ∃ f : ℝ → E,
        Set.Ioo (t0 - d) (t0 + d) ⊆ U ∧ f t0 = v ∧
        ContDiffOn ℝ ∞ f (Set.Ioo (t0 - d) (t0 + d)) ∧
        ∀ t ∈ Set.Ioo (t0 - d) (t0 + d), HasDerivAt f (A t (f t)) t := by
  let S : Set (ℝ × E) := U ×ˢ Set.univ
  let B : ℝ × E → E := fun z ↦ A z.1 z.2
  have hB : ContDiffOn ℝ ∞ B S :=
    (hA.comp contDiffOn_fst (fun z hz ↦ hz.1)).clm_apply contDiffOn_snd
  obtain ⟨beta, V, d, hV, hstart, hVS, hd, hbeta, hinit, hode⟩ :=
    exists_local_smooth_timeDependent_flow S (hU.prod isOpen_univ) B hB (s0, 0)
      ⟨hs0, Set.mem_univ _⟩
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV (s0, 0) hstart
  let W := Metric.ball s0 (r / 2)
  have hzV (t0 : ℝ) (ht0 : t0 ∈ W) (w : E) (hw : ‖w‖ < r) : (t0, w) ∈ V := by
    apply hrV
    change dist (t0, w) (s0, (0 : E)) < r
    rw [Prod.dist_eq, dist_zero_right]
    have ht : dist t0 s0 < r / 2 := ht0
    exact max_lt (by linarith) hw
  refine ⟨W, d, isOpen_ball, mem_ball_self (by positivity), ?_, hd, ?_⟩
  · intro t0 ht0
    exact (hVS (hzV t0 ht0 0 (by simpa only [norm_zero] using hr))).1
  · intro t0 ht0 v
    let c := (r / 2) / (‖v‖ + 1)
    have hden : 0 < ‖v‖ + 1 := by positivity
    have hc : 0 < c := by dsimp [c]; positivity
    have hcmul : c * (‖v‖ + 1) = r / 2 := div_mul_cancel₀ _ hden.ne'
    have hsmall : ‖c • v‖ < r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      nlinarith
    have hstartV := hzV t0 ht0 (c • v) hsmall
    let f : ℝ → E := fun t ↦ c⁻¹ • beta ((t0, c • v), t - t0)
    have hshift (t : ℝ) (ht : t ∈ Set.Ioo (t0 - d) (t0 + d)) :
        t - t0 ∈ Set.Ioo (-d) d := by constructor <;> linarith [ht.1, ht.2]
    have htime : ∀ t ∈ Set.Ioo (t0 - d) (t0 + d), t ∈ U := by
      intro t ht
      have h := (hode (t0, c • v) hstartV (t - t0) (hshift t ht)).1.1
      simpa only [add_sub_cancel] using h
    have hmap : Set.MapsTo (fun t : ℝ ↦ ((t0, c • v), t - t0))
        (Set.Ioo (t0 - d) (t0 + d)) (V ×ˢ Set.Ioo (-d) d) :=
      fun t ht ↦ ⟨hstartV, hshift t ht⟩
    have hcomp : ContDiffOn ℝ ∞ (fun t : ℝ ↦ beta ((t0, c • v), t - t0))
        (Set.Ioo (t0 - d) (t0 + d)) :=
      hbeta.comp (contDiff_const.prodMk (contDiff_id.sub contDiff_const)).contDiffOn hmap
    refine ⟨f, htime, ?_, contDiffOn_const.smul hcomp, ?_⟩
    · dsimp only [f]
      rw [sub_self, hinit (t0, c • v) hstartV, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    · intro t ht
      have h := (hode (t0, c • v) hstartV (t - t0) (hshift t ht)).2
      have h' := (h.scomp t ((hasDerivAt_id t).sub_const t0)).const_smul c⁻¹
      simpa only [Function.comp_def, id_eq, one_smul, B, add_sub_cancel, f,
        map_smul, Pi.smul_def] using h'

end PoincareConjecture.Proofs.M09
