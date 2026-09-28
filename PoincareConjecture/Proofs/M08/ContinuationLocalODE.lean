import PoincareConjecture.Proofs.M08.ClosedChartCoefficients
import Mathlib.Analysis.ODE.ExistUnique

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold Bundle

namespace PoincareConjecture.M08

section LocalODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem exists_smooth_local_phase {U : Set ℝ} {V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (f : ℝ → E → E)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ V))
    {t₀ : ℝ} {z₀ : E} (ht₀ : t₀ ∈ U) (hz₀ : z₀ ∈ V) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ z : ℝ → E,
      z t₀ = z₀ ∧ Ioo (t₀ - 2 * ε) (t₀ + 2 * ε) ⊆ U ∧
      MapsTo z (Ioo (t₀ - 2 * ε) (t₀ + 2 * ε)) V ∧
      ContDiffOn ℝ ∞ z (Ioo (t₀ - 2 * ε) (t₀ + 2 * ε)) ∧
      ∀ t ∈ Ioo (t₀ - 2 * ε) (t₀ + 2 * ε), HasDerivAt z (f t (z t)) t := by
  let A : ℝ × E → ℝ × E := fun w ↦ (1, f w.1 w.2)
  have hA : ContDiffAt ℝ 1 A (t₀, z₀) :=
    (contDiffAt_const.prodMk ((hf _ ⟨ht₀, hz₀⟩).contDiffAt
      ((hU.prod hV).mem_nhds ⟨ht₀, hz₀⟩))).of_le (by simp)
  obtain ⟨γ, hγ₀, d, hd, hγd⟩ :=
    hA.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  have hγtd (r : ℝ) (hr : r ∈ Ioo (t₀ - d) (t₀ + d)) :
      HasDerivAt (fun t ↦ (γ t).1) 1 r := by
    exact (hγd r hr).fst
  have hγt (t : ℝ) (ht : t ∈ Ioo (t₀ - d) (t₀ + d)) : (γ t).1 = t := by
    have heq : EqOn (fun r ↦ (γ r).1) (fun r ↦ r) (Ioo (t₀ - d) (t₀ + d)) := by
      apply isOpen_Ioo.eqOn_of_deriv_eq (x := t₀) isPreconnected_Ioo
        (fun r hr ↦ (hγtd r hr).differentiableAt.differentiableWithinAt)
        differentiableOn_id
      · intro r hr
        rw [(hγtd r hr).deriv, deriv_id]
      · exact ⟨by linarith, by linarith⟩
      · exact congrArg Prod.fst hγ₀
    exact heq ht
  have hγc : ContinuousAt γ t₀ :=
    (hγd t₀ ⟨by linarith, by linarith⟩).continuousAt
  have hnear : ∀ᶠ t in 𝓝 t₀, γ t ∈ U ×ˢ V := by
    apply hγc (hU.prod hV |>.mem_nhds ?_)
    rw [hγ₀]
    exact ⟨ht₀, hz₀⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let e := min d r / 4
  have he : 0 < e := by dsimp only [e]; positivity
  have hsub : Icc (t₀ - 3 * e) (t₀ + 3 * e) ⊆ Ioo (t₀ - d) (t₀ + d) := by
    intro t ht
    have he' : 4 * e ≤ d := by dsimp only [e]; linarith [min_le_left d r]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmem (t : ℝ) (ht : t ∈ Icc (t₀ - 3 * e) (t₀ + 3 * e)) : γ t ∈ U ×ˢ V := by
    apply hball
    have he' : 4 * e ≤ r := by dsimp only [e]; linarith [min_le_right d r]
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let z := fun t ↦ (γ t).2
  have hzd (t : ℝ) (ht : t ∈ Icc (t₀ - 3 * e) (t₀ + 3 * e)) :
      HasDerivAt z (f t (z t)) t := by
    have h := (hγd t (hsub ht)).snd
    change HasDerivAt z (f (γ t).1 (z t)) t at h
    rwa [hγt t (hsub ht)] at h
  have htime : Icc (t₀ - 3 * e) (t₀ + 3 * e) ⊆ U := by
    intro t ht
    simpa only [hγt t (hsub ht)] using (hmem t ht).1
  have htarget : MapsTo z (Icc (t₀ - 3 * e) (t₀ + 3 * e)) V :=
    fun t ht ↦ (hmem t ht).2
  have hzs : ContDiffOn ℝ ∞ z (Icc (t₀ - 3 * e) (t₀ + 3 * e)) :=
    ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := ⊤)
      (hf.mono (prod_mono htime subset_rfl))
      (fun t ht ↦ (hzd t ht).hasDerivWithinAt) htarget
  have hsmall : Ioo (t₀ - 2 * e) (t₀ + 2 * e) ⊆ Icc (t₀ - 3 * e) (t₀ + 3 * e) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact ⟨e, he, z, congrArg Prod.snd hγ₀, hsmall.trans htime,
    htarget.mono_left hsmall, hzs.mono hsmall, fun t ht ↦ hzd t (hsmall ht)⟩

theorem smooth_phase_eventuallyEq (f : ℝ → E → E) {z w : ℝ → E} {t₀ : ℝ}
    (hf : ContDiffAt ℝ 1 (Function.uncurry f) (t₀, z t₀))
    (hz : ∀ᶠ t in 𝓝 t₀, HasDerivAt z (f t (z t)) t)
    (hw : ∀ᶠ t in 𝓝 t₀, HasDerivAt w (f t (w t)) t)
    (heq : z t₀ = w t₀) : z =ᶠ[𝓝 t₀] w := by
  obtain ⟨K, S, hS, hLip⟩ := hf.exists_lipschitzOnWith
  have hzc : ContinuousAt z t₀ := (hz.self_of_nhds).continuousAt
  have hwc : ContinuousAt w t₀ := (hw.self_of_nhds).continuousAt
  have hzS : ∀ᶠ t in 𝓝 t₀, (t, z t) ∈ S :=
    (continuousAt_id.prodMk hzc) hS
  have hwS : ∀ᶠ t in 𝓝 t₀, (t, w t) ∈ S := by
    apply (continuousAt_id.prodMk hwc)
    simpa only [heq, id_eq] using hS
  apply ODE_solution_unique_of_eventually (K := K) (s := fun t ↦ {y | (t, y) ∈ S})
    (Filter.Eventually.of_forall (fun t ↦ ?_)) (hz.and hzS) (hw.and hwS) heq
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy y' hy'
  simpa only [Function.uncurry_apply_pair, Prod.dist_eq, dist_self,
    max_eq_right dist_nonneg] using hLip.dist_le_mul (x := (t, y)) (y := (t, y')) hy hy'

end LocalODE

end PoincareConjecture.M08
