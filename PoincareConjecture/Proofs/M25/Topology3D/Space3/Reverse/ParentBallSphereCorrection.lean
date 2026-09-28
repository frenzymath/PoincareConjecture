import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereCollarCorrection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FixedSphereBallPreservation
import PoincareConjecture.Proofs.M25.Topology3D.Services











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem exists_sphere_fixed_patch_extension
    (T : E3 → E3) {K U : Set E3}
    (hK : IsCompact K) (hKS : K ⊆ sphere (0 : E3) 1)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hT : ContDiffOn ℝ ∞ T U)
    (hfixed : ∀ y ∈ U, ‖y‖ = 1 → T y = y)
    (hn : ∀ y ∈ U, ‖y‖ = 1 → 0 < ⟪y, fderiv ℝ T y y⟫_ℝ) :
    ∃ F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      (∀ y ∈ sphere (0 : E3) 1, F y = y) ∧
      F '' ball (0 : E3) 1 = ball 0 1 ∧
      F '' closedBall (0 : E3) 1 = closedBall 0 1 ∧
      (∀ᶠ y in 𝓝ˢ K, F y = T y) ∧
      ∃ L : Set E3, IsCompact L ∧ ∀ y, y ∉ L → F y = y := by
  obtain ⟨ρ, hρ, _, hsupport, hnear, hrange⟩ := exists_compact_smooth_cutoff hK hU hKU
  let f : E3 → E3 := fun y => y + ρ y • (T y - y)
  have hf : ContDiff ℝ ∞ f := contDiff_id.add
    (contDiff_cutoff_smul hU ρ hρ hsupport (fun y => T y - y)
      (hT.sub contDiffOn_id))
  have hoff (y : E3) (hy : y ∉ U) : f =ᶠ[𝓝 y] (fun z => z) := by
    have hys : y ∉ tsupport ρ := fun hh => hy (hsupport hh)
    filter_upwards [(isClosed_tsupport ρ).isOpen_compl.mem_nhds hys] with z hz
    simp only [f, image_eq_zero_of_notMem_tsupport hz, zero_smul, add_zero]
  have hffixed (y : E3) (hy : y ∈ sphere (0 : E3) 1) : f y = y := by
    by_cases hyU : y ∈ U
    · simp only [f, hfixed y hyU (mem_sphere_zero_iff_norm.mp hy), sub_self,
        smul_zero, add_zero]
    · exact (hoff y hyU).self_of_nhds
  have hfn (y : E3) (hy : y ∈ sphere (0 : E3) 1) :
      0 < ⟪y, fderiv ℝ f y y⟫_ℝ := by
    have hyn := mem_sphere_zero_iff_norm.mp hy
    by_cases hyU : y ∈ U
    · have hyT : DifferentiableAt ℝ T y :=
        (hT.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)
      have hyρ : DifferentiableAt ℝ ρ y := hρ.differentiable (by simp) y
      have hdf := (hasFDerivAt_id y).fun_add
        (hyρ.hasFDerivAt.fun_smul (hyT.hasFDerivAt.fun_sub (hasFDerivAt_id y)))
      change HasFDerivAt f _ y at hdf
      have hformula : fderiv ℝ f y y = y + ρ y • (fderiv ℝ T y y - y) := by
        rw [hdf.fderiv]
        change y + (ρ y • (fderiv ℝ T y y - y) +
          (fderiv ℝ ρ y y) • (T y - y)) = _
        rw [hfixed y hyU hyn, sub_self, smul_zero, add_zero]
      rw [hformula, inner_add_right, real_inner_smul_right, inner_sub_right,
        real_inner_self_eq_norm_sq, hyn, one_pow]
      have hnormal := hn y hyU hyn
      have ht := hrange y
      by_cases hz : ρ y = 0
      · rw [hz, zero_mul, add_zero]
        exact zero_lt_one
      · have htpos : 0 < ρ y := lt_of_le_of_ne ht.1 (Ne.symm hz)
        have hprod := mul_pos htpos hnormal
        nlinarith only [ht.2, hprod]
    · have hdf : HasFDerivAt f (ContinuousLinearMap.id ℝ E3) y :=
        (hasFDerivAt_id y).congr_of_eventuallyEq (hoff y hyU)
      rw [hdf.fderiv]
      change 0 < ⟪y, y⟫_ℝ
      rw [real_inner_self_eq_norm_sq, hyn, one_pow]
      exact zero_lt_one
  obtain ⟨Φ, hΦ, hΦ0, hΦfixed, hΦnear, L, hL, hΦsupport⟩ :=
    exists_sphere_collar_correction f isOpen_univ (subset_univ _)
      hf.contDiffOn hffixed hfn
  have hpaths (y : E3) : ContinuousOn (fun t : ℝ => (Φ t).toHomeomorph y) (Icc 0 1) :=
    (hΦ.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hfixed' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (y : E3) (hy : ‖y‖ = 1) :
      (Φ t).toHomeomorph y = y := hΦfixed t ht y (mem_sphere_zero_iff_norm.mpr hy)
  obtain ⟨hball, hclosed⟩ := fixedSphere_isotopy_image_balls
    (fun t => (Φ t).toHomeomorph) hpaths hΦ0 hfixed' (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  refine ⟨Φ 1, hΦfixed 1 (by norm_num), hball, hclosed, ?_, L, hL, hΦsupport 1⟩
  filter_upwards [hΦnear.filter_mono (nhdsSet_mono hKS), hnear] with y hy hρy
  rw [hy]
  simp only [f, hρy, one_smul, add_sub_cancel]

end PoincareConjecture.M25.Topology3D
