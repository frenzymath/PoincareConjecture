import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.Jacobi.Potential
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.RegularLevels
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.SegmentSpeed
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

theorem eq_of_potential_eq_at_nondegenerate_critical_point (D : LeviCivitaData g)
    (hc : MetricComplete g) {f : M → ℝ} {lambda : ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    {p q : M} (hcrit : D.gradient f p = 0)
    (hR : D.scalarCurvature p ≠ 2 * lambda) (hpq : f p = f q) : p = q := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 2) M
  by_contra hne
  let L := (g.edist p q).toReal
  have hL : 0 < L := ENNReal.toReal_pos (by
    change edist p q ≠ 0
    exact mt edist_eq_zero.mp hne) (g.edist_ne_top p q)
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hc p q
  have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have h0 := hI (show (0 : ℝ) ∈ Icc 0 1 by simp)
  obtain ⟨C, hC⟩ := hγ.exists_constant_tangentNorm (by linarith)
  have hv := (hγ.hasDerivAt_chart_at h0 p (by
    simpa only [hγ0] using mem_extChartAt_source p)).1
  have hC0 : g.tangentNorm p (deriv (fun t => extChartAt (𝓡 2) p (γ t)) 0) = C := by
    simpa only [RiemannianMetric.chartCoefficients_self, RiemannianMetric.tangentNorm] using
      (hγ.tangentNorm_initial h0 hγ0 hv).symm.trans (hC 0 h0)
  have hCL : (C : ℝ) = L := by
    have h := hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hv hmin
    rw [hC0] at h
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ (C : ℝ) from C.2)] using
      congrArg ENNReal.toReal h
  have hspeed (t : ℝ) (ht : t ∈ Ioo (-ε) (1 + ε)) :
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) = L := by
    rw [← hCL]
    exact hC t ht
  obtain ⟨t, ht, hturn⟩ := exists_deriv_eq_zero (by norm_num : (0 : ℝ) < 1)
    (hf.continuous.comp_continuousOn (hγ.contMDiffOn.continuousOn.mono hI))
    (by simpa only [Function.comp_apply, hγ0, hγ1] using hpq)
  apply D.deriv_potential_ne_zero_inside_minimizing hf hsol hε hL hγ hspeed
    (by rw [hγ0, hγ1]; exact (ENNReal.ofReal_toReal (g.edist_ne_top p q)).symm)
    (by rw [hγ0]; exact hcrit) (by simpa only [hγ0] using hR) ht hturn

theorem eq_of_potential_eq_at_critical_point_of_not_round (D : LeviCivitaData g)
    (hc : MetricComplete g) {f : M → ℝ} {lambda : ℝ} (hlambda : 0 < lambda)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (hnot : ¬ ConstantPositiveSectionalCurvature g D)
    {p q : M} (hcrit : D.gradient f p = 0) (hpq : f p = f q) : p = q := by
  apply D.eq_of_potential_eq_at_nondegenerate_critical_point hc hf hsol hcrit _ hpq
  intro hR
  exact hnot (D.round_of_degenerate_critical_point hlambda hf hsol hcrit hR)

end PoincareConjecture.LeviCivitaData
