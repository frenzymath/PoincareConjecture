import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerTrace
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2Restriction
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped Topology SchwartzMap LineDeriv InnerProductSpace ContDiff

namespace PoincareConjecture




theorem m65WeakTrace_green_integral
    {u : Lp ℝ 2 (volume.restrict loopDiskSet)}
    {d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)}
    {b : Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi))}
    (htrace : M65DiskWeakTrace u d b) (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) :
    (∫ z in loopDiskSet, d i z * test z) +
      (∫ z in loopDiskSet, u z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
        ∫ θ in Icc (-Real.pi) Real.pi, b θ * m65DiskBoundaryTest test i θ := by
  have hleft (v : Lp ℝ 2 (volume.restrict loopDiskSet)) (φ : 𝓢(LoopPlane, ℝ)) :
      ⟪v, m65DiskTestL2 φ⟫_ℝ = ∫ z in loopDiskSet, v z * φ z := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [((φ.memLp 2 volume).restrict loopDiskSet).coeFn_toLp] with z hz
    simp only [m65DiskTestL2, hz, Real.inner_apply]
  have hright : ⟪b, m65DiskBoundaryTestL2 test i⟫_ℝ =
      ∫ θ in Icc (-Real.pi) Real.pi, b θ * m65DiskBoundaryTest test i θ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    have hae : m65DiskBoundaryTestL2 test i =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
        m65DiskBoundaryTest test i := by
      unfold m65DiskBoundaryTestL2
      exact MemLp.coeFn_toLp _
    filter_upwards [hae] with θ hθ
    simp only [hθ, Real.inner_apply]
  simpa only [hleft, hright, SchwartzMap.lineDerivOp_apply_eq_fderiv] using htrace test i





theorem m65WeakTrace_interior_integral
    {u : Lp ℝ 2 (volume.restrict loopDiskSet)}
    {d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)}
    {b : Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi))}
    (htrace : M65DiskWeakTrace u d b) (test : 𝓢(LoopPlane, ℝ))
    (hsupport : tsupport test ⊆ ball (0 : LoopPlane) 1) (i : Fin 2) :
    (∫ z in loopDiskSet, d i z * test z) =
      -(∫ z in loopDiskSet, u z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
  have hz (θ : ℝ) : test (Proofs.M58.angularPoint θ) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hx
    have hh := hsupport hx
    simp only [mem_ball_zero_iff, Proofs.M58.norm_angularPoint, lt_self_iff_false] at hh
  have hbzero : (∫ θ in Icc (-Real.pi) Real.pi,
      b θ * m65DiskBoundaryTest test i θ) = 0 := by
    apply integral_eq_zero_of_ae
    exact ae_of_all _ (fun θ => by
      simp only [m65DiskBoundaryTest, hz θ, zero_mul, mul_zero, Pi.zero_apply])
  have h := m65WeakTrace_green_integral htrace test i
  rw [hbzero] at h
  exact eq_neg_of_add_eq_zero_left h

private theorem m65Schwartz_mul_disk_memLp (θ : 𝓢(LoopPlane, ℝ))
    (u : Lp ℝ 2 (volume.restrict loopDiskSet)) :
    MemLp (fun z => θ z * u z) 2 (volume.restrict loopDiskSet) := by
  apply (Lp.memLp u).of_le_mul (c := SchwartzMap.seminorm ℝ 0 0 θ)
    (θ.continuous.aestronglyMeasurable.mul (Lp.memLp u).1)
  exact ae_of_all _ (fun z => by
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (θ.norm_le_seminorm ℝ z) (norm_nonneg _))

private theorem m65Disk_zeroExtension_inner (f : LoopPlane → ℝ)
    (hf : MemLp f 2 (volume.restrict loopDiskSet)) (φ : 𝓢(LoopPlane, ℝ)) :
    let hF := (memLp_indicator_iff_restrict
      (show MeasurableSet loopDiskSet from measurableSet_closedBall)).mpr hf
    ⟪hF.toLp (loopDiskSet.indicator f), φ.toLp 2 volume⟫_ℝ =
      ∫ z in loopDiskSet, f z * φ z := by
  intro hF
  rw [L2.inner_def, ← integral_indicator
    (show MeasurableSet loopDiskSet from measurableSet_closedBall)]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp, φ.coeFn_toLp 2 volume] with z hz hφ
  rw [hz, hφ, Real.inner_apply]
  by_cases hzd : z ∈ loopDiskSet
  · rw [indicator_of_mem hzd, indicator_of_mem hzd]
  · rw [indicator_of_notMem hzd, indicator_of_notMem hzd, zero_mul]





theorem m65WeakTrace_cutoff_global
    {u : Lp ℝ 2 (volume.restrict loopDiskSet)}
    {d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)}
    {b : Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi))}
    (htrace : M65DiskWeakTrace u d b) (θ : 𝓢(LoopPlane, ℝ))
    (hsupport : tsupport θ ⊆ ball (0 : LoopPlane) 1) :
    ∃ (U : Lp ℝ 2 (volume : Measure LoopPlane))
      (D : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane)),
      (U =ᵐ[volume] loopDiskSet.indicator (fun z => θ z * u z)) ∧
      (∀ i, D i =ᵐ[volume] loopDiskSet.indicator (fun z => θ z * d i z +
        fderiv ℝ θ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * u z)) ∧
      ∀ i (φ : 𝓢(LoopPlane, ℝ)),
        ⟪D i, φ.toLp 2 volume⟫_ℝ = -⟪U,
          (∂_{EuclideanSpace.basisFun (Fin 2) ℝ i} φ).toLp 2 volume⟫_ℝ := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let A (i : Fin 2) (z : LoopPlane) := θ z * d i z + fderiv ℝ θ z (e i) * u z
  have hU := m65Schwartz_mul_disk_memLp θ u
  have hA (i : Fin 2) : MemLp (A i) 2 (volume.restrict loopDiskSet) :=
    (m65Schwartz_mul_disk_memLp θ (d i)).add
      (m65Schwartz_mul_disk_memLp (∂_{e i} θ) u)
  have hUG := (memLp_indicator_iff_restrict measurableSet_closedBall).mpr hU
  have hAG (i : Fin 2) := (memLp_indicator_iff_restrict measurableSet_closedBall).mpr (hA i)
  let U := hUG.toLp (loopDiskSet.indicator (fun z => θ z * u z))
  let D (i : Fin 2) := (hAG i).toLp (loopDiskSet.indicator (A i))
  refine ⟨U, D, hUG.coeFn_toLp, fun i => (hAG i).coeFn_toLp, ?_⟩
  intro i φ
  let p := SchwartzMap.smulLeftCLM ℝ θ φ
  have hp : (p : LoopPlane → ℝ) = fun z => θ z * φ z := by
    exact SchwartzMap.smulLeftCLM_apply θ.hasTemperateGrowth φ
  have hpSupport : tsupport p ⊆ ball (0 : LoopPlane) 1 :=
    (SchwartzMap.tsupport_smulLeftCLM_subset θ φ).trans
      ((inter_subset_right).trans hsupport)
  have hpD (z : LoopPlane) :
      fderiv ℝ p z (e i) = θ z * fderiv ℝ φ z (e i) +
        fderiv ℝ θ z (e i) * φ z := by
    rw [hp]
    change fderiv ℝ ((θ : LoopPlane → ℝ) * (φ : LoopPlane → ℝ)) z (e i) = _
    rw [fderiv_mul θ.differentiableAt φ.differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hφL2 := (φ.memLp 2 volume).restrict loopDiskSet
  have hφDL2 := ((∂_{e i} φ).memLp 2 volume).restrict loopDiskSet
  have hsum : (∫ z in loopDiskSet, A i z * φ z) +
      (∫ z in loopDiskSet, θ z * u z * fderiv ℝ φ z (e i)) =
      (∫ z in loopDiskSet, d i z * p z) +
      (∫ z in loopDiskSet, u z * fderiv ℝ p z (e i)) := by
    have hL := integral_add ((hA i).integrable_mul hφL2) (hU.integrable_mul hφDL2)
    have hR := integral_add ((Lp.memLp (d i)).integrable_mul
      ((p.memLp 2 volume).restrict loopDiskSet))
      ((Lp.memLp u).integrable_mul
        (((∂_{e i} p).memLp 2 volume).restrict loopDiskSet))
    simp only [Pi.mul_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv] at hL hR
    rw [← hL, ← hR]
    apply integral_congr_ae
    apply ae_of_all
    intro z
    dsimp only
    rw [hpD, hp]
    dsimp only [A]
    ring
  have hweak := m65WeakTrace_interior_integral htrace p hpSupport i
  have hUI := m65Disk_zeroExtension_inner (fun z => θ z * u z) hU (∂_{e i} φ)
  have hDI := m65Disk_zeroExtension_inner (A i) (hA i) φ
  change ⟪D i, φ.toLp 2 volume⟫_ℝ = -⟪U, (∂_{e i} φ).toLp 2 volume⟫_ℝ
  rw [hDI, hUI]
  change (∫ z in loopDiskSet, A i z * φ z) =
    -(∫ z in loopDiskSet, θ z * u z * fderiv ℝ φ z (e i))
  linarith only [hsum, hweak]

end PoincareConjecture
