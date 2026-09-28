import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityHalfCone
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.PolarDivergence
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff intervalIntegral

namespace PoincareConjecture.M65Boundary

theorem integral_divergence_halfDisk (X : LoopPlane → LoopPlane)
    (hX : ContDiff ℝ 1 X) {r : ℝ} (hr : 0 < r) :
    (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}, ∑ i : Fin 2,
      inner ℝ (fderiv ℝ X z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      r * (∫ θ in (0 : ℝ)..Real.pi,
        inner ℝ (X (r • Proofs.M58.angularPoint θ)) (Proofs.M58.angularPoint θ)) +
      ∫ s in (0 : ℝ)..r,
        m65PolarAngularFlux X s Real.pi - m65PolarAngularFlux X s 0 := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let D := fun z => ∑ i : Fin 2, inner ℝ (fderiv ℝ X z (b i)) (b i)
  let polar := fun p : ℝ × ℝ => p.1 • Proofs.M58.angularPoint p.2
  let P : ℝ × ℝ → ℝ := Function.uncurry (m65PolarRadialFlux X)
  let Q : ℝ × ℝ → ℝ := Function.uncurry (m65PolarAngularFlux X)
  let K := Icc (0 : ℝ) r ×ˢ Icc (0 : ℝ) Real.pi
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hpolar : ContDiff ℝ 1 polar :=
    contDiff_fst.smul ((Proofs.M58.contDiff_angularPoint.of_le (by simp)).comp contDiff_snd)
  have hτ : ContDiff ℝ 1 Proofs.M58.angularVector := by
    apply contDiff_euclidean.mpr
    intro i
    fin_cases i
    · exact Real.contDiff_sin.neg
    · exact Real.contDiff_cos
  have hP : ContDiff ℝ 1 P :=
    contDiff_fst.mul ((hX.comp hpolar).inner ℝ
      ((Proofs.M58.contDiff_angularPoint.of_le (by simp)).comp contDiff_snd))
  have hQ : ContDiff ℝ 1 Q := (hX.comp hpolar).inner ℝ (hτ.comp contDiff_snd)
  have hD (p : ℝ × ℝ) :
      fderiv ℝ P p (1, 0) + fderiv ℝ Q p (0, 1) = p.1 * D (polar p) := by
    have hPr : fderiv ℝ P p (1, 0) =
        deriv (fun s : ℝ => m65PolarRadialFlux X s p.2) p.1 := by
      have h := (hP.differentiable one_ne_zero p).hasFDerivAt.comp_hasDerivAt p.1
        ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
      simpa +instances only [P, Function.comp_def, Function.uncurry_apply_pair,
        Prod.eta, id_eq] using! h.deriv.symm
    have hQr : fderiv ℝ Q p (0, 1) =
        deriv (fun t : ℝ => m65PolarAngularFlux X p.1 t) p.2 := by
      have h := (hQ.differentiable one_ne_zero p).hasFDerivAt.comp_hasDerivAt p.2
        ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
      simpa +instances only [Q, Function.comp_def, Function.uncurry_apply_pair,
        Prod.eta, id_eq] using! h.deriv.symm
    rw [hPr, hQr, m65PolarDivergencePointwise X hX.contDiffAt, m65PolarTrace_eq]
  have hdiv : Continuous (fun p : ℝ × ℝ =>
      fderiv ℝ P p (1, 0) + fderiv ℝ Q p (0, 1)) :=
    ((hP.continuous_fderiv one_ne_zero).clm_apply continuous_const).add
      ((hQ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hdivI : IntegrableOn (fun p : ℝ × ℝ =>
      fderiv ℝ P p (1, 0) + fderiv ℝ Q p (0, 1)) K :=
    hdiv.continuousOn.integrableOn_compact hK
  have hweightI : IntegrableOn (fun p : ℝ × ℝ => p.1 * D (polar p)) K := by
    exact hdivI.congr (ae_of_all _ hD)
  have hrect := integral2_divergence_prod_of_hasFDerivAt
    P Q (fderiv ℝ P) (fderiv ℝ Q) 0 0 r Real.pi
    hP.continuous.continuousOn hQ.continuous.continuousOn
    (fun p _ => (hP.differentiable one_ne_zero p).hasFDerivAt)
    (fun p _ => (hQ.differentiable one_ne_zero p).hasFDerivAt)
    (by simpa only [uIcc_of_le hr.le, uIcc_of_le Real.pi_pos.le] using hdivI)
  have hpolarI : (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}, D z) =
      ∫ s in (0 : ℝ)..r, ∫ θ in (0 : ℝ)..Real.pi, s * D (polar (s, θ)) := by
    have hh := halfDisk_integral_polar D 0 r
    simp only [PiLp.zero_apply, M65Interior.polarPlane, zero_add] at hh
    rw [hh]
    have hpI : Integrable (fun p : ℝ × ℝ => p.1 * D (polar p))
        ((volume.restrict (Icc (0 : ℝ) r)).prod
          (volume.restrict (Icc (0 : ℝ) Real.pi))) := by
      rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hf := integral_prod (fun p : ℝ × ℝ => p.1 * D (polar p)) hpI
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hf
    rw [hf, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.le]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
  have hid : (∫ s in (0 : ℝ)..r, ∫ θ in (0 : ℝ)..Real.pi, s * D (polar (s, θ))) =
      ∫ s in (0 : ℝ)..r, ∫ θ in (0 : ℝ)..Real.pi,
        fderiv ℝ P (s, θ) (1, 0) + fderiv ℝ Q (s, θ) (0, 1) := by
    apply intervalIntegral.integral_congr
    intro s _
    apply intervalIntegral.integral_congr
    intro θ _
    exact (hD (s, θ)).symm
  change (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}, D z) = _
  rw [hpolarI, hid, hrect]
  simp only [P, Q, Function.uncurry_apply_pair, m65PolarRadialFlux, zero_mul,
    intervalIntegral.integral_zero, sub_zero, intervalIntegral.integral_const_mul]
  have hqI (t : ℝ) : IntervalIntegrable (fun s => m65PolarAngularFlux X s t) volume 0 r :=
    (hQ.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub (hqI Real.pi) (hqI 0)]
  ring

theorem smooth_halfDisk_green (f test : LoopPlane → ℝ)
    (hf : ContDiff ℝ 1 f) (ht : ContDiff ℝ 1 test) (i : Fin 2)
    {r : ℝ} (hr : 0 < r) :
    (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
      fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i) * test z +
        f z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      r * (∫ θ in (0 : ℝ)..Real.pi,
        f (r • Proofs.M58.angularPoint θ) * test (r • Proofs.M58.angularPoint θ) *
          Proofs.M58.angularPoint θ i) +
      ∫ s in (0 : ℝ)..r,
        (f (s • Proofs.M58.angularPoint Real.pi) * test (s • Proofs.M58.angularPoint Real.pi) *
          Proofs.M58.angularVector Real.pi i) -
        (f (s • Proofs.M58.angularPoint 0) * test (s • Proofs.M58.angularPoint 0) *
          Proofs.M58.angularVector 0 i) := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let X := fun z => (f z * test z) • b i
  have hX : ContDiff ℝ 1 X := (hf.mul ht).smul contDiff_const
  have hdiv (z : LoopPlane) :
      (∑ j : Fin 2, inner ℝ (fderiv ℝ X z (b j)) (b j)) =
        fderiv ℝ f z (b i) * test z + f z * fderiv ℝ test z (b i) := by
    have hd := ((hf.differentiable one_ne_zero z).hasFDerivAt.mul
      (ht.differentiable one_ne_zero z).hasFDerivAt).smul_const (b i)
    change HasFDerivAt X _ z at hd
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.smulRight_apply, real_inner_smul_left]
    rw [Finset.sum_eq_single i]
    · simp only [b.inner_eq_one, mul_one, add_apply, smul_apply, smul_eq_mul]
      ring
    · intro j _ hji
      rw [b.inner_eq_zero hji.symm, mul_zero]
    · simp
  have heq := integral_divergence_halfDisk X hX hr
  change (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
    ∑ j : Fin 2, inner ℝ (fderiv ℝ X z (b j)) (b j)) = _ at heq
  simp_rw [hdiv] at heq
  simpa only [X, m65PolarAngularFlux, real_inner_smul_left,
    b, EuclideanSpace.basisFun_inner] using heq

end PoincareConjecture.M65Boundary
