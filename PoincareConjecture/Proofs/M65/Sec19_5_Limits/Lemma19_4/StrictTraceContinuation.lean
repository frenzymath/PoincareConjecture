import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceInterior
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceArcCapture
import Mathlib.Analysis.Calculus.MeanValue










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M65StrictTrace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}




theorem differential_zero_interior_of_local_zero (D : LeviCivitaData g)
    {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 3) ∞ f (Metric.ball (0 : LoopPlane) 1))
    (hb : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (hharm : ∀ z ∈ Metric.ball (0 : LoopPlane) 1, m65PlaneTension D f z = 0)
    {x : LoopPlane} (hx : x ∈ Metric.ball (0 : LoopPlane) 1)
    (hzero : ∀ᶠ y in 𝓝 x, mfderiv (𝓡 2) (𝓡 3) f y = 0) :
    ∀ z ∈ Metric.ball (0 : LoopPlane) 1, mfderiv (𝓡 2) (𝓡 3) f z = 0 := by
  let A : Set LoopPlane := {z | ∀ᶠ y in 𝓝 z, mfderiv (𝓡 2) (𝓡 3) f y = 0}
  have hA : IsOpen A := isOpen_setOfPred_eventually_nhds
  have hcl : closure A ∩ Metric.ball (0 : LoopPlane) 1 ⊆ A := by
    intro z hz
    by_contra hn
    have hisolated := (interior_differential_zero_alternative D hf hb hharm hz.2).resolve_left hn
    have hnot : ∀ᶠ y in 𝓝 z, y ∉ A := by
      filter_upwards [hisolated] with y hy hyA
      have hdy : mfderiv (𝓡 2) (𝓡 3) f y = 0 :=
        mem_of_mem_nhds (s := {w : LoopPlane | mfderiv (𝓡 2) (𝓡 3) f w = 0}) hyA
      exact hn ((hy hdy) ▸ hyA)
    exact (mem_closure_iff_frequently.mp hz.1) hnot
  have hall := (convex_ball (0 : LoopPlane) 1).isPreconnected.subset_of_closure_inter_subset
    hA ⟨x, hx, hzero⟩ hcl
  intro z hz
  exact mem_of_mem_nhds (s := {w : LoopPlane | mfderiv (𝓡 2) (𝓡 3) f w = 0}) (hall hz)




theorem not_local_zero_of_Jordan_trace [T2Space M] (D : LeviCivitaData g)
    {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e) (hei : Function.Injective e)
    {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 3) ∞ f (Metric.ball (0 : LoopPlane) 1))
    (hb : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (hharm : ∀ z ∈ Metric.ball (0 : LoopPlane) 1, m65PlaneTension D f z = 0)
    {gamma : LoopCircle → M} (hgamma : Function.Injective gamma)
    {beta : LoopCircle → LoopCircle} (hbeta : Function.Surjective beta)
    (htrace : ∀ z : LoopCircle, f z = gamma (beta z))
    {x : LoopPlane} (hx : x ∈ Metric.ball (0 : LoopPlane) 1) :
    ¬∀ᶠ y in 𝓝 x, mfderiv (𝓡 2) (𝓡 3) f y = 0 := by
  intro hzero
  have hD := differential_zero_interior_of_local_zero D hf hb hharm hx hzero
  have hG : ContDiffOn ℝ ∞ (e ∘ f) (Metric.ball (0 : LoopPlane) 1) :=
    (he.comp_contMDiffOn hf).contDiffOn
  have hDG (z : LoopPlane) (hz : z ∈ Metric.ball (0 : LoopPlane) 1) :
      fderiv ℝ (e ∘ f) z = 0 := by
    have hd := mfderiv_comp z ((he (f z)).mdifferentiableAt (by simp))
      ((hf.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv, hD z hz, ContinuousLinearMap.comp_zero] at hd
    exact hd
  have h0 : (0 : LoopPlane) ∈ Metric.ball (0 : LoopPlane) 1 := Metric.mem_ball_self zero_lt_one
  have hconst : EqOn f (fun _ => f 0) (Metric.ball (0 : LoopPlane) 1) := by
    intro z hz
    apply hei
    exact Metric.isOpen_ball.is_const_of_fderiv_eq_zero
      (convex_ball (0 : LoopPlane) 1).isPreconnected (hG.differentiableOn (by simp))
      (fun w hw => hDG w hw) hz h0
  have hclosed : EqOn f (fun _ => f 0) loopDiskSet :=
    hconst.of_subset_closure hb.continuousOn continuousOn_const Metric.ball_subset_closedBall (by
      rw [closure_ball (0 : LoopPlane) one_ne_zero]
      exact Subset.rfl)
  have hne : m65LoopAngular 0 ≠ m65LoopAngular Real.pi := by
    intro hh
    have hc := congrArg (fun z : LoopCircle => (z : LoopPlane) 0) hh
    norm_num [m65LoopAngular, Proofs.M58.angularPoint] at hc
  obtain ⟨a, ha⟩ := hbeta (m65LoopAngular 0)
  obtain ⟨b, hb'⟩ := hbeta (m65LoopAngular Real.pi)
  have hcircle (z : LoopCircle) : (z : LoopPlane) ∈ loopDiskSet := by
    simpa only [loopDiskSet, mem_closedBall_zero_iff, z.property] using (le_refl (1 : ℝ))
  apply hne
  apply hgamma
  rw [← ha, ← hb', ← htrace a, ← htrace b, hclosed (hcircle a), hclosed (hcircle b)]

end PoincareConjecture.M65StrictTrace
