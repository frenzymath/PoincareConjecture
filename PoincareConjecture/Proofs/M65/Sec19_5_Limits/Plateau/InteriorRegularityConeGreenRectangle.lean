import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityConeGreenIntegrability
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityConeFluxIntegral
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M65Interior

theorem coneGreen_rectangle {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {v d : ℝ → EuclideanSpace ℝ (Fin 3)} {v0 : EuclideanSpace ℝ (Fin 3)}
    {r ρ K : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hv : AbsolutelyContinuousOnInterval v (-Real.pi) Real.pi)
    (hper : v (-Real.pi) = v Real.pi)
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ)
    (hvb : MapsTo v (Icc (-Real.pi) Real.pi) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc (-Real.pi) Real.pi)))
    (hinc : ∀ t ∈ Icc (-Real.pi) Real.pi, ∀ u ∈ Icc (-Real.pi) Real.pi,
      v u - v t = ∫ θ in t..u, d θ)
    (hD : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ, ‖fderiv ℝ g y‖ ≤ K)
    (x : LoopPlane) (test : LoopPlane → ℝ) (ht : ContDiff ℝ 1 test) (i : Fin 2) :
    (∫ p in Icc (0 : ℝ) r ×ˢ Icc (-Real.pi) Real.pi,
      p.1 * (coneCartesianField g r v0 v d p.1 p.2 i * test (polarPlane x p) +
        g (coneCoordinates r v0 v p.1 p.2) *
          fderiv ℝ test (polarPlane x p) (EuclideanSpace.basisFun (Fin 2) ℝ i))) =
      r * ∫ θ in (-Real.pi)..Real.pi,
        g (v θ) * test (polarPlane x (r, θ)) * Proofs.M58.angularPoint θ i := by
  let S : Set (ℝ × ℝ) := Icc 0 r ×ˢ Icc (-Real.pi) Real.pi
  let R (p : ℝ × ℝ) := deriv (fun s => coneRadialFlux g r v0 v x test i s p.2) p.1
  let Q (p : ℝ × ℝ) := deriv (fun θ => coneAngularFlux g r v0 v x test i p.1 θ) p.2
  have hπ : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  have hvc : ContinuousOn v (Icc (-Real.pi) Real.pi) := by
    simpa only [uIcc_of_le hπ.le] using hv.continuousOn
  have hI : IntervalIntegrable d volume (-Real.pi) Real.pi :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hπ.le).mpr
      (hd.integrable (by norm_num : (1 : ENNReal) ≤ 2))
  have hR : IntegrableOn R S :=
    (coneRadialFlux_deriv_continuous hr hρ hvc hg h0 hvb x test ht i).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hQ : IntegrableOn Q S :=
    coneAngularFlux_deriv_integrable hr hρ hK hπ hvc hg h0 hvb hd hinc hD x test ht i
  have hprod : ∀ᵐ p ∂volume.restrict S, HasDerivAt v (d p.2) p.2 := by
    have h := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc (0 : ℝ) r))).ae (increment_ae_hasDerivAt hπ hI hinc)
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  have heq : (fun p : ℝ × ℝ =>
      p.1 * (coneCartesianField g r v0 v d p.1 p.2 i * test (polarPlane x p) +
        g (coneCoordinates r v0 v p.1 p.2) *
          fderiv ℝ test (polarPlane x p) (EuclideanSpace.basisFun (Fin 2) ℝ i)))
      =ᵐ[volume.restrict S] fun p => R p + Q p := by
    filter_upwards [hprod, ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)]
      with p hp hpS
    have hm : coneCoordinates r v0 v p.1 p.2 ∈
        ball (0 : EuclideanSpace ℝ (Fin 3)) (2 * ρ) :=
      (closedBall_subset_ball (by linarith))
        (coneCoordinates_mem_closedBall hr h0 (hvb hpS.2) hpS.1)
    exact (coneFlux_derivative_sum r v0 v d x test i p.1 p.2 hp
      ((hg.contDiffAt (isOpen_ball.mem_nhds hm)).differentiableAt one_ne_zero)
      (ht.differentiable one_ne_zero _)).symm
  have hRp : Integrable R
      ((volume.restrict (Icc (0 : ℝ) r)).prod (volume.restrict (Icc (-Real.pi) Real.pi))) := by
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hQp : Integrable Q
      ((volume.restrict (Icc (0 : ℝ) r)).prod (volume.restrict (Icc (-Real.pi) Real.pi))) := by
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hrad : (∫ p in S, R p) = r * ∫ θ in (-Real.pi)..Real.pi,
      g (v θ) * test (polarPlane x (r, θ)) * Proofs.M58.angularPoint θ i := by
    have hf := integral_prod_symm R hRp
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hf
    calc
      _ = ∫ θ in Icc (-Real.pi) Real.pi, ∫ s in Icc (0 : ℝ) r, R (s, θ) := hf
      _ = ∫ θ in Icc (-Real.pi) Real.pi,
          r * (g (v θ) * test (polarPlane x (r, θ)) * Proofs.M58.angularPoint θ i) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro θ hθ
        dsimp only
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.le]
        change (∫ s in (0 : ℝ)..r,
          deriv (fun q => coneRadialFlux g r v0 v x test i q θ) s) = _
        rw [coneRadialFlux_integral_deriv v hr hρ hg h0 θ (hvb hθ) x test ht i]
        ring
      _ = _ := by
        rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le hπ.le]
  have hang : (∫ p in S, Q p) = 0 := by
    have hf := integral_prod Q hQp
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hf
    calc
      _ = ∫ s in Icc (0 : ℝ) r, ∫ θ in Icc (-Real.pi) Real.pi, Q (s, θ) := hf
      _ = ∫ _s in Icc (0 : ℝ) r, (0 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro s hs
        dsimp only
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hπ.le]
        exact coneAngularFlux_integral_deriv hr hρ hv hper hg h0 hvb hI hinc hs x test ht i
      _ = 0 := integral_zero _ _
  change (∫ p in S, _) = _
  rw [integral_congr_ae heq, integral_add hR hQ, hrad, hang, add_zero]

end PoincareConjecture.M65Interior
