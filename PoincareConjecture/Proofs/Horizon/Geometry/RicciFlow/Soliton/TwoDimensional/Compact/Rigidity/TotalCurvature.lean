import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.VolumeDensity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.TotalCurvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [PreconnectedSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

theorem density_mul_scalar_difference_le_integral (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (hRnonneg : ∀ x, 0 ≤ D.scalarCurvature x)
    {p z : M} (hpz : f p < f z) {c : ℝ}
    (hslab : ∀ s t : ℝ, f p < s → t < f z → s ≤ t →
      ∀ H : ℝ → ℝ, Continuous H →
        (∫ x in f ⁻¹' Icc s t, H (f x) ∂g.volumeMeasure) =
          c * ∫ u in Icc s t, H u) :
    c * (D.scalarCurvature z - D.scalarCurvature p) ≤
      ∫ x, D.scalarCurvature x ∂g.volumeMeasure := by
  let r : ℝ → ℝ := fun t => D.scalarCurvature p * Real.exp (t - f p)
  have hr : Continuous r := by fun_prop
  have hrd (t : ℝ) : HasDerivAt r (r t) t := by
    convert ((hasDerivAt_id t).sub_const (f p)).exp.const_mul (D.scalarCurvature p)
      using 1 <;> first | rfl | simp [r]
  have hR (x : M) : D.scalarCurvature x = r (f x) :=
    D.scalar_eq_exp_potential_difference_of_surface_soliton hf hsol p x
  have hbound (s t : ℝ) (hps : f p < s) (htz : t < f z) (hst : s ≤ t) :
      c * (r t - r s) ≤ ∫ x, D.scalarCurvature x ∂g.volumeMeasure := by
    have h := hslab s t hps htz hst r hr
    have hi : (∫ u in Icc s t, r u) = r t - r s := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hst]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hrd u)
        (hr.intervalIntegrable s t)
    rw [hi] at h
    have hleft : (∫ x in f ⁻¹' Icc s t, r (f x) ∂g.volumeMeasure) =
        ∫ x in f ⁻¹' Icc s t, D.scalarCurvature x ∂g.volumeMeasure := by
      exact integral_congr_ae (Eventually.of_forall fun x => (hR x).symm)
    rw [hleft] at h
    rw [← h]
    exact setIntegral_le_integral D.integrable_scalarCurvature
      (Eventually.of_forall hRnonneg)
  obtain ⟨u, v, hu, hv, hua, hvb, huv, hlimu, hlimv⟩ :=
    exists_seq_strictAnti_strictMono_tendsto hpz
  have hlim := ((hr.tendsto (f z)).comp hlimv).sub ((hr.tendsto (f p)).comp hlimu)
  have hbound' := le_of_tendsto' (hlim.const_mul c)
    (fun n => hbound (u n) (v n) (hua n).1 (hvb n).2 (huv n n).le)
  rwa [← hR z, ← hR p] at hbound'

omit [PreconnectedSpace M] in

theorem density_mul_scalar_difference_le_eight_pi [ConnectedSpace M]
    (D : LeviCivitaData g) {f : M → ℝ} {lambda : ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (hRnonneg : ∀ x, 0 ≤ D.scalarCurvature x)
    {p z : M} (hpz : f p < f z) {c : ℝ}
    (hslab : ∀ s t : ℝ, f p < s → t < f z → s ≤ t →
      ∀ H : ℝ → ℝ, Continuous H →
        (∫ x in f ⁻¹' Icc s t, H (f x) ∂g.volumeMeasure) =
          c * ∫ u in Icc s t, H u) :
    c * (D.scalarCurvature z - D.scalarCurvature p) ≤ 8 * Real.pi :=
  (D.density_mul_scalar_difference_le_integral hf hsol hRnonneg hpz hslab).trans
    D.integral_scalarCurvature_le_eight_pi

end PoincareConjecture.LeviCivitaData
