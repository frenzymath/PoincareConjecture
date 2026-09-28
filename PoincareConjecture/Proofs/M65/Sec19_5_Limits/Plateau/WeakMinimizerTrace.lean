import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.DiskDivergence
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakDerivatives

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology SchwartzMap LineDeriv InnerProductSpace ContDiff intervalIntegral

namespace PoincareConjecture

noncomputable def m65DiskTestL2 (test : 𝓢(LoopPlane, ℝ)) :
    Lp ℝ 2 (volume.restrict loopDiskSet) :=
  ((test.memLp 2 volume).restrict loopDiskSet).toLp test

noncomputable def m65DiskBoundaryTest (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (θ : ℝ) : ℝ :=
  test (Proofs.M58.angularPoint θ) * Proofs.M58.angularPoint θ i

private theorem m65DiskBoundaryTest_memLp (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) :
    MemLp (m65DiskBoundaryTest test i) 2
      (volume.restrict (Icc (-Real.pi) Real.pi)) := by
  have hc : Continuous (m65DiskBoundaryTest test i) :=
    (test.continuous.comp Proofs.M58.contDiff_angularPoint.continuous).mul
      ((contDiff_euclidean.mp Proofs.M58.contDiff_angularPoint i).continuous)
  exact (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
    ((hc.pow 2).continuousOn.integrableOn_compact isCompact_Icc)

noncomputable def m65DiskBoundaryTestL2 (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) :
    Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi)) :=
  (m65DiskBoundaryTest_memLp test i).toLp (m65DiskBoundaryTest test i)

def M65DiskWeakTrace (u : Lp ℝ 2 (volume.restrict loopDiskSet))
    (d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet))
    (b : Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi))) : Prop :=
  ∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2),
    ⟪d i, m65DiskTestL2 test⟫_ℝ +
      ⟪u, m65DiskTestL2 (∂_{EuclideanSpace.basisFun (Fin 2) ℝ i} test)⟫_ℝ =
        ⟪b, m65DiskBoundaryTestL2 test i⟫_ℝ

theorem m65DiskWeakTrace_of_limit
    {u : ℕ → Lp ℝ 2 (volume.restrict loopDiskSet)}
    {u0 : Lp ℝ 2 (volume.restrict loopDiskSet)}
    {d : ℕ → Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)}
    {d0 : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)}
    {b : ℕ → Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi))}
    {b0 : Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi))}
    (htrace : ∀ n, M65DiskWeakTrace (u n) (d n) (b n))
    (hu : Tendsto u atTop (𝓝 u0))
    (hd : ∀ i v, Tendsto (fun n => ⟪d n i, v⟫_ℝ) atTop (𝓝 ⟪d0 i, v⟫_ℝ))
    (hb : Tendsto b atTop (𝓝 b0)) : M65DiskWeakTrace u0 d0 b0 := by
  intro test i
  have hleft := (hd i (m65DiskTestL2 test)).add
    (hu.inner (tendsto_const_nhds (x :=
      m65DiskTestL2 (∂_{EuclideanSpace.basisFun (Fin 2) ℝ i} test))))
  have hright : Tendsto (fun n => ⟪b n, m65DiskBoundaryTestL2 test i⟫_ℝ)
      atTop (𝓝 ⟪b0, m65DiskBoundaryTestL2 test i⟫_ℝ) := hb.inner tendsto_const_nhds
  exact tendsto_nhds_unique hleft (hright.congr fun n => (htrace n test i).symm)

private theorem m65C1_diskGreen (f : LoopPlane → ℝ) (hf : ContDiff ℝ 1 f)
    (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) :
    (∫ z in loopDiskSet, fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i) * test z +
      f z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
        ∫ θ in (-Real.pi)..Real.pi,
          f (Proofs.M58.angularPoint θ) * m65DiskBoundaryTest test i θ := by
  let B := EuclideanSpace.basisFun (Fin 2) ℝ
  let X := fun z : LoopPlane => (f z * test z) • B i
  have hX : ContDiff ℝ 1 X := (hf.mul (test.smooth 1)).smul contDiff_const
  have hdiv (z : LoopPlane) :
      (∑ j : Fin 2, inner ℝ (fderiv ℝ X z (B j)) (B j)) =
        fderiv ℝ f z (B i) * test z + f z * fderiv ℝ test z (B i) := by
    have hd := ((hf.differentiable one_ne_zero z).hasFDerivAt.mul
      (test.differentiableAt (x := z)).hasFDerivAt).smul_const (B i)
    change (∑ j : Fin 2, inner ℝ (fderiv ℝ (fun w => (f w * test w) • B i) z
      (B j)) (B j)) = _
    erw [hd.fderiv]
    simp only [ContinuousLinearMap.smulRight_apply, real_inner_smul_left]
    rw [Finset.sum_eq_single i]
    · simp only [B.inner_eq_one, mul_one, add_apply, smul_apply, smul_eq_mul]
      ring
    · intro j _ hji
      rw [B.inner_eq_zero (Ne.symm hji), mul_zero]
    · simp
  calc
    _ = ∫ z in loopDiskSet, ∑ j : Fin 2,
        inner ℝ (fderiv ℝ X z (B j)) (B j) := by
      apply setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet
      intro z _
      exact (hdiv z).symm
    _ = ∫ θ in (-Real.pi)..Real.pi,
        inner ℝ (X (Proofs.M58.angularPoint θ)) (Proofs.M58.angularPoint θ) :=
      m65Integral_divergence_loopDisk X (fun _ _ => hX.contDiffAt)
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [X, real_inner_smul_left, B, EuclideanSpace.basisFun_inner,
        m65DiskBoundaryTest]
      ring

theorem m65DiskWeakTrace_of_C1 (f : LoopPlane → ℝ) (hf : ContDiff ℝ 1 f)
    (hfL2 : MemLp f 2 (volume.restrict loopDiskSet))
    (hdL2 : ∀ i : Fin 2, MemLp
      (fun z => fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i)) 2
        (volume.restrict loopDiskSet))
    (hbL2 : MemLp (fun θ => f (Proofs.M58.angularPoint θ)) 2
      (volume.restrict (Icc (-Real.pi) Real.pi))) :
    M65DiskWeakTrace (hfL2.toLp f)
      (fun i => (hdL2 i).toLp
        (fun z => fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i)))
      (hbL2.toLp (fun θ => f (Proofs.M58.angularPoint θ))) := by
  intro test i
  have htest := (test.memLp 2 volume).restrict loopDiskSet
  have htestD := ((∂_{EuclideanSpace.basisFun (Fin 2) ℝ i} test).memLp 2 volume).restrict
    loopDiskSet
  have hleft : ⟪(hdL2 i).toLp
        (fun z => fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i)),
      m65DiskTestL2 test⟫_ℝ =
      ∫ z in loopDiskSet, fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i) * test z := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hdL2 i).coeFn_toLp, htest.coeFn_toLp] with z hz ht
    simp only [hz, m65DiskTestL2, ht, Real.inner_apply]
  have hright : ⟪hfL2.toLp f,
      m65DiskTestL2 (∂_{EuclideanSpace.basisFun (Fin 2) ℝ i} test)⟫_ℝ =
      ∫ z in loopDiskSet, f z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hfL2.coeFn_toLp, htestD.coeFn_toLp] with z hz ht
    simp only [hz, m65DiskTestL2, ht, Real.inner_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hboundary : ⟪hbL2.toLp (fun θ => f (Proofs.M58.angularPoint θ)),
      m65DiskBoundaryTestL2 test i⟫_ℝ =
      ∫ θ in (-Real.pi)..Real.pi,
        f (Proofs.M58.angularPoint θ) * m65DiskBoundaryTest test i θ := by
    rw [L2.inner_def, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
    apply integral_congr_ae
    filter_upwards [hbL2.coeFn_toLp, (m65DiskBoundaryTest_memLp test i).coeFn_toLp] with θ hθ ht
    simp only [hθ, m65DiskBoundaryTestL2, ht, Real.inner_apply]
  have hDI : IntegrableOn (fun z => f z *
      fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) loopDiskSet volume := by
    have h := hfL2.integrable_mul htestD
    change Integrable (fun z => f z * (∂_{EuclideanSpace.basisFun (Fin 2) ℝ i} test) z)
      (volume.restrict loopDiskSet) at h
    simpa only [IntegrableOn, SchwartzMap.lineDerivOp_apply_eq_fderiv] using h
  have hLI : IntegrableOn (fun z =>
      fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i) * test z) loopDiskSet volume :=
    (hdL2 i).integrable_mul htest
  rw [hleft, hright, hboundary]
  exact (integral_add hLI hDI).symm.trans (m65C1_diskGreen f hf test i)

end PoincareConjecture
