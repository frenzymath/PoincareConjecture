import PoincareConjecture.Proofs.M28.Generalized.StrongNeckCurvatureOperator
import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M30

open SpacetimeBounds

set_option maxHeartbeats 800000 in

theorem tendstoUniformlyOn_metricTwoJet_of_uniform_spatial_jets
    {ι A : Type*} {n : ℕ} {l : Filter ι}
    {f : ι → A → EuclideanSpace ℝ (Fin n) → MetricCoefficient n}
    {g : A → EuclideanSpace ℝ (Fin n) → MetricCoefficient n}
    {K : Set (A × EuclideanSpace ℝ (Fin n))}
    (h : ∀ m ≤ 2, TendstoUniformlyOn
      (fun k p => iteratedFDeriv ℝ m (f k p.1) p.2)
      (fun p => iteratedFDeriv ℝ m (g p.1) p.2) l K) :
    TendstoUniformlyOn
      (fun k p => metricTwoJet (f k p.1) p.2)
      (fun p => metricTwoJet (g p.1) p.2) l K := by
  let E := EuclideanSpace ℝ (Fin n)
  have hshift {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {a : ι → A → E → F} {a0 : A → E → F} {m : ℕ}
      (ha : TendstoUniformlyOn (fun k p => iteratedFDeriv ℝ (m + 1) (a k p.1) p.2)
        (fun p => iteratedFDeriv ℝ (m + 1) (a0 p.1) p.2) l K) :
      TendstoUniformlyOn (fun k p => iteratedFDeriv ℝ m (fderiv ℝ (a k p.1)) p.2)
        (fun p => iteratedFDeriv ℝ m (fderiv ℝ (a0 p.1)) p.2) l K := by
    have heq (q : E → F) (x : E) : continuousMultilinearCurryRightEquiv' ℝ m E F
        (iteratedFDeriv ℝ (m + 1) q x) = iteratedFDeriv ℝ m (fderiv ℝ q) x := by
      rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
        LinearIsometryEquiv.apply_symm_apply]
    have H := (continuousMultilinearCurryRightEquiv' ℝ m E F).isometry.uniformContinuous
      |>.comp_tendstoUniformlyOn ha
    simpa only [Function.comp_def, heq] using H
  have h0 := (ContinuousMultilinearMap.uniformContinuous_eval_const
    (0 : Fin 0 → E)).comp_tendstoUniformlyOn (h 0 (by omega))
  have hd1 := hshift (a := f) (a0 := g) (m := 0) (h 1 (by omega))
  have hd2 := hshift (a := f) (a0 := g) (m := 1) (h 2 (by omega))
  have hdd := hshift (a := fun k t => fderiv ℝ (f k t))
    (a0 := fun t => fderiv ℝ (g t)) (m := 0) hd2
  have h1 := (ContinuousMultilinearMap.uniformContinuous_eval_const
    (0 : Fin 0 → E)).comp_tendstoUniformlyOn hd1
  have h2 := (ContinuousMultilinearMap.uniformContinuous_eval_const
    (0 : Fin 0 → E)).comp_tendstoUniformlyOn hdd
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro delta hdelta
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h0 delta hdelta,
    Metric.tendstoUniformlyOn_iff.mp h1 delta hdelta,
    Metric.tendstoUniformlyOn_iff.mp h2 delta hdelta] with k hk0 hk1 hk2
  intro p hp
  exact max_lt (hk0 p hp) (max_lt (hk1 p hp) (hk2 p hp))

theorem tendstoUniformlyOn_jetCurvatureNorm_of_uniform_jets
    {ι X : Type*} [TopologicalSpace X] {l : Filter ι}
    {A : ι → X → MetricTwoJet 3} {A0 : X → MetricTwoJet 3} {K : Set X}
    (hK : IsCompact K) (hcontinuous : ContinuousOn A0 K)
    (hinvertible : ∀ x ∈ K, (A0 x).1.IsInvertible)
    (hjets : TendstoUniformlyOn A A0 l K) :
    TendstoUniformlyOn (fun k x => M28.jetCurvatureNorm (A k x))
      (fun x => M28.jetCurvatureNorm (A0 x)) l K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro delta hdelta
  obtain ⟨eta, heta, hmodulus⟩ := M28.exists_jetCurvatureNorm_uniform_modulus
    (hK.image_of_continuousOn hcontinuous)
    (by rintro _ ⟨x, hx, rfl⟩; exact hinvertible x hx) hdelta
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hjets eta heta] with k hk
  intro x hx
  simpa only [Real.dist_eq, abs_sub_comm] using
    hmodulus (A0 x) (mem_image_of_mem _ hx) (A k x)
      (by simpa only [dist_comm] using hk x hx)

end PoincareConjecture.M30
