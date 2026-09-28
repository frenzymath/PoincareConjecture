import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityConeFlux
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityConeL2
import Mathlib.MeasureTheory.Function.LocallyIntegrable












set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M65Interior




theorem coneRadialFlux_deriv_continuous {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {v : ℝ → EuclideanSpace ℝ (Fin 3)} {v0 : EuclideanSpace ℝ (Fin 3)}
    {r ρ a b : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hv : ContinuousOn v (Icc a b))
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ) (hvb : MapsTo v (Icc a b) (closedBall 0 ρ))
    (x : LoopPlane) (test : LoopPlane → ℝ) (ht : ContDiff ℝ 1 test) (i : Fin 2) :
    ContinuousOn (fun p : ℝ × ℝ =>
      deriv (fun s => coneRadialFlux g r v0 v x test i s p.2) p.1)
      (Icc 0 r ×ˢ Icc a b) := by
  let S : Set (ℝ × ℝ) := Icc 0 r ×ˢ Icc a b
  have hQ := (cone_reconstruction_continuous hr hρ hv hg h0 hvb).1
  have hA := (cone_reconstruction_continuous hr hρ hv hg h0 hvb).2
  have hvp : ContinuousOn (fun p : ℝ × ℝ => v p.2 - v0) S :=
    (hv.comp continuous_snd.continuousOn (fun _ hp => hp.2)).sub continuousOn_const
  have heV : Continuous (fun p : ℝ × ℝ => Proofs.M58.angularPoint p.2) :=
    Proofs.M58.contDiff_angularPoint.continuous.comp continuous_snd
  have he : Continuous (fun p : ℝ × ℝ => Proofs.M58.angularPoint p.2 i) :=
    (EuclideanSpace.proj i : LoopPlane →L[ℝ] ℝ).continuous.comp heV
  have hp : Continuous (polarPlane x) := continuous_const.add (continuous_fst.smul heV)
  have hψ := ht.continuous.comp hp
  have hψD := ((ht.continuous_fderiv one_ne_zero).comp hp).clm_apply heV
  have hR : ContinuousOn (fun p : ℝ × ℝ =>
      Proofs.M58.angularPoint p.2 i * g (coneCoordinates r v0 v p.1 p.2) *
          test (polarPlane x p) +
        p.1 * Proofs.M58.angularPoint p.2 i *
          (r⁻¹ * fderiv ℝ g (coneCoordinates r v0 v p.1 p.2) (v p.2 - v0) *
              test (polarPlane x p) +
            g (coneCoordinates r v0 v p.1 p.2) *
              fderiv ℝ test (polarPlane x p) (Proofs.M58.angularPoint p.2))) S :=
    ((he.continuousOn.mul hQ).mul hψ.continuousOn).add
      ((continuous_fst.continuousOn.mul he.continuousOn).mul
        (((continuousOn_const.mul (hA.clm_apply hvp)).mul hψ.continuousOn).add
          (hQ.mul hψD.continuousOn)))
  apply hR.congr
  intro p hpS
  have hm : coneCoordinates r v0 v p.1 p.2 ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (2 * ρ) :=
    (closedBall_subset_ball (by linarith))
      (coneCoordinates_mem_closedBall hr h0 (hvb hpS.2) hpS.1)
  exact (coneRadialFlux_hasDerivAt r v0 v x test i p.1 p.2
    ((hg.contDiffAt (isOpen_ball.mem_nhds hm)).differentiableAt one_ne_zero)
    (ht.differentiable one_ne_zero _)).deriv




theorem coneGreen_integrable {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {v d : ℝ → EuclideanSpace ℝ (Fin 3)} {v0 : EuclideanSpace ℝ (Fin 3)}
    {r ρ a b K : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hv : ContinuousOn v (Icc a b))
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ) (hvb : MapsTo v (Icc a b) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc a b)))
    (hD : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ, ‖fderiv ℝ g y‖ ≤ K)
    (x : LoopPlane) (test : LoopPlane → ℝ) (ht : ContDiff ℝ 1 test) (i : Fin 2) :
    IntegrableOn (fun p : ℝ × ℝ =>
      p.1 * (coneCartesianField g r v0 v d p.1 p.2 i * test (polarPlane x p) +
        g (coneCoordinates r v0 v p.1 p.2) *
          fderiv ℝ test (polarPlane x p) (EuclideanSpace.basisFun (Fin 2) ℝ i)))
      (Icc 0 r ×ˢ Icc a b) := by
  let S : Set (ℝ × ℝ) := Icc 0 r ×ˢ Icc a b
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  have hfield : IntegrableOn
      (fun p : ℝ × ℝ => coneCartesianField g r v0 v d p.1 p.2 i) S :=
    (coneCartesianField_memLp hr hρ hK hv hg h0 hvb hd hD i).integrable
      (by norm_num : (1 : ENNReal) ≤ 2)
  have hp : Continuous (polarPlane x) := continuous_const.add
    (continuous_fst.smul (Proofs.M58.contDiff_angularPoint.continuous.comp continuous_snd))
  have hψ := ht.continuous.comp hp
  have hψD : Continuous (fun p =>
      fderiv ℝ test (polarPlane x p) (EuclideanSpace.basisFun (Fin 2) ℝ i)) :=
    ((ht.continuous_fderiv one_ne_zero).comp hp).clm_apply continuous_const
  have hQ := (cone_reconstruction_continuous hr hρ hv hg h0 hvb).1
  exact IntegrableOn.continuousOn_mul continuous_fst.continuousOn
    ((hfield.mul_continuousOn hψ.continuousOn hS).add
      ((hQ.mul hψD.continuousOn).integrableOn_compact hS)) hS





theorem coneAngularFlux_deriv_integrable {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {v d : ℝ → EuclideanSpace ℝ (Fin 3)} {v0 : EuclideanSpace ℝ (Fin 3)}
    {r ρ a b K : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hK : 0 ≤ K) (hab : a < b)
    (hv : ContinuousOn v (Icc a b))
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ) (hvb : MapsTo v (Icc a b) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc a b)))
    (hinc : ∀ t ∈ Icc a b, ∀ u ∈ Icc a b, v u - v t = ∫ θ in t..u, d θ)
    (hD : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ, ‖fderiv ℝ g y‖ ≤ K)
    (x : LoopPlane) (test : LoopPlane → ℝ) (ht : ContDiff ℝ 1 test) (i : Fin 2) :
    IntegrableOn (fun p : ℝ × ℝ =>
      deriv (fun θ => coneAngularFlux g r v0 v x test i p.1 θ) p.2)
      (Icc 0 r ×ˢ Icc a b) := by
  have hI : IntervalIntegrable d volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr
      (hd.integrable (by norm_num : (1 : ENNReal) ≤ 2))
  have hθ := increment_ae_hasDerivAt hab hI hinc
  have hprod : ∀ᵐ p ∂volume.restrict (Icc (0 : ℝ) r ×ˢ Icc a b),
      HasDerivAt v (d p.2) p.2 := by
    have h := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc (0 : ℝ) r))).ae hθ
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  have hR : IntegrableOn (fun p : ℝ × ℝ =>
      deriv (fun s => coneRadialFlux g r v0 v x test i s p.2) p.1) (Icc 0 r ×ˢ Icc a b) :=
    (coneRadialFlux_deriv_continuous hr hρ hv hg h0 hvb x test ht i).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  apply ((coneGreen_integrable hr hρ hK hv hg h0 hvb hd hD x test ht i).sub hR).congr
  filter_upwards [hprod, ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp hpS
  have hm : coneCoordinates r v0 v p.1 p.2 ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (2 * ρ) :=
    (closedBall_subset_ball (by linarith))
      (coneCoordinates_mem_closedBall hr h0 (hvb hpS.2) hpS.1)
  have h := coneFlux_derivative_sum r v0 v d x test i p.1 p.2 hp
    ((hg.contDiffAt (isOpen_ball.mem_nhds hm)).differentiableAt one_ne_zero)
    (ht.differentiable one_ne_zero _)
  dsimp only [Pi.sub_apply]
  linarith

end PoincareConjecture.M65Interior
