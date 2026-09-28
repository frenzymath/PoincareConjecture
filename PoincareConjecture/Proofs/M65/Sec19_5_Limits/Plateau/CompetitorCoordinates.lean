import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.CompetitorEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric Complex
open scoped Topology ContDiff Matrix.Norms.Elementwise

namespace PoincareConjecture

private theorem complex_isothermal_real_matrix
    (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K.IsHermitian)
    (φ : ℂ → ℂ) (z : LoopPlane) (hφ : DifferentiableAt ℝ φ
      (orthonormalBasisOneI.repr.symm z)) (c : ℝ)
    (hq : ∀ v : ℂ,
      K 0 0 * (fderiv ℝ φ (orthonormalBasisOneI.repr.symm z) v).re ^ 2 +
        2 * K 0 1 * (fderiv ℝ φ (orthonormalBasisOneI.repr.symm z) v).re *
          (fderiv ℝ φ (orthonormalBasisOneI.repr.symm z) v).im +
        K 1 1 * (fderiv ℝ φ (orthonormalBasisOneI.repr.symm z) v).im ^ 2 =
          c * ‖v‖ ^ 2) :
    let Φ := fun w : LoopPlane =>
      orthonormalBasisOneI.repr (φ (orthonormalBasisOneI.repr.symm w))
    let B := LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (fderiv ℝ Φ z).toLinearMap
    B.transpose * K * B = c • 1 := by
  let e := orthonormalBasisOneI.repr
  let A := fderiv ℝ φ (e.symm z)
  let Φ := fun w : LoopPlane => e (φ (e.symm w))
  let B := LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (fderiv ℝ Φ z).toLinearMap
  have hd := e.toContinuousLinearEquiv.hasFDerivAt.comp z
    (hφ.hasFDerivAt.comp z e.symm.toContinuousLinearEquiv.hasFDerivAt)
  change HasFDerivAt Φ _ z at hd
  have hb (i j : Fin 2) : B i j =
      (e (A (e.symm (EuclideanSpace.basisFun (Fin 2) ℝ j)))) i := by
    simp only [B, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr]
    rw [hd.fderiv]
    rfl
  have hb00 : B 0 0 = (A 1).re := by
    rw [hb]
    simp [e, orthonormalBasisOneI_repr_apply, EuclideanSpace.basisFun_apply]
  have hb10 : B 1 0 = (A 1).im := by
    rw [hb]
    simp [e, orthonormalBasisOneI_repr_apply, EuclideanSpace.basisFun_apply]
  have hb01 : B 0 1 = (A I).re := by
    rw [hb]
    simp [e, orthonormalBasisOneI_repr_apply, EuclideanSpace.basisFun_apply]
  have hb11 : B 1 1 = (A I).im := by
    rw [hb]
    simp [e, orthonormalBasisOneI_repr_apply, EuclideanSpace.basisFun_apply]
  have h0 := hq 1
  have h1 := hq I
  have h2 := hq (1 + I)
  change K 0 0 * (A 1).re ^ 2 + 2 * K 0 1 * (A 1).re * (A 1).im +
    K 1 1 * (A 1).im ^ 2 = c * ‖(1 : ℂ)‖ ^ 2 at h0
  change K 0 0 * (A I).re ^ 2 + 2 * K 0 1 * (A I).re * (A I).im +
    K 1 1 * (A I).im ^ 2 = c * ‖I‖ ^ 2 at h1
  change K 0 0 * (A (1 + I)).re ^ 2 +
    2 * K 0 1 * (A (1 + I)).re * (A (1 + I)).im +
    K 1 1 * (A (1 + I)).im ^ 2 = c * ‖1 + I‖ ^ 2 at h2
  simp only [norm_one, norm_I, one_pow, mul_one] at h0 h1
  simp only [map_add, add_re, add_im, ← normSq_eq_norm_sq, normSq_apply,
    one_re, one_im, I_re, I_im, add_zero, zero_add] at h2
  have hsym : K 1 0 = K 0 1 := by simpa only [star_trivial] using hK.apply 0 1
  change B.transpose * K * B = c • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      hb00, hb10, hb01, hb11, hsym] <;>
    nlinarith only [h0, h1, h2]

theorem m65Exists_disk_isothermal_coordinates
    (K : LoopPlane → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ContDiff ℝ ∞ K) (hpos : ∀ z, (K z).PosDef) (δ : ℝ)
    (hzero : ∀ᶠ z in 𝓝 (0 : LoopPlane), K z = δ • 1)
    (hout : ∀ z, 1 ≤ ‖z‖ → K z = δ • 1) :
    ∃ Φ : LoopPlane ≃ₜ LoopPlane,
      ContDiff ℝ ∞ (Φ : LoopPlane → LoopPlane) ∧
      ContDiff ℝ ∞ (Φ.symm : LoopPlane → LoopPlane) ∧
      (∀ z, ‖Φ z‖ ≤ 1 ↔ ‖z‖ ≤ 1) ∧ (∀ z, ‖Φ z‖ < 1 ↔ ‖z‖ < 1) ∧
      ∀ z ∈ loopDiskSet, ∃ c : ℝ, 0 < c ∧
        let B := LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
            (fderiv ℝ (Φ : LoopPlane → LoopPlane) z).toLinearMap
        B.transpose * K (Φ z) * B = c • 1 := by
  let e := orthonormalBasisOneI.repr
  have hzeroC : ∀ᶠ z in 𝓝 (0 : ℂ), K (e z) = δ • 1 := by
    have ht : Tendsto e (𝓝 (0 : ℂ)) (𝓝 (0 : LoopPlane)) := by
      simpa only [map_zero] using e.continuous.tendsto (0 : ℂ)
    exact ht.eventually hzero
  obtain ⟨φ, hφ, hψ, _, _, hclosed, hopen, hiso⟩ :=
    Complex.exists_smooth_disk_isothermal_coordinates (fun z => K (e z))
      (hK.comp e.toContinuousLinearEquiv.contDiff) (fun z => hpos (e z)) δ hzeroC
      (fun z hz => hout (e z) (by simpa only [e.norm_map] using hz))
  let Φ : LoopPlane ≃ₜ LoopPlane := e.symm.toHomeomorph.trans (φ.trans e.toHomeomorph)
  have hΦ : ContDiff ℝ ∞ (Φ : LoopPlane → LoopPlane) :=
    e.toContinuousLinearEquiv.contDiff.comp
      (hφ.comp e.symm.toContinuousLinearEquiv.contDiff)
  have hΨ : ContDiff ℝ ∞ (Φ.symm : LoopPlane → LoopPlane) :=
    e.toContinuousLinearEquiv.contDiff.comp
      (hψ.comp e.symm.toContinuousLinearEquiv.contDiff)
  refine ⟨Φ, hΦ, hΨ, ?_, ?_, ?_⟩
  · intro z
    change ‖e (φ (e.symm z))‖ ≤ 1 ↔ ‖z‖ ≤ 1
    simpa only [e.norm_map, e.symm.norm_map] using hclosed (e.symm z)
  · intro z
    change ‖e (φ (e.symm z))‖ < 1 ↔ ‖z‖ < 1
    simpa only [e.norm_map, e.symm.norm_map] using hopen (e.symm z)
  · intro z hz
    have hzc : ‖e.symm z‖ ≤ 1 := by
      simpa only [e.symm.norm_map] using mem_closedBall_zero_iff.mp hz
    obtain ⟨c, hc, hq⟩ := hiso (e.symm z) hzc
    exact ⟨c, hc, complex_isothermal_real_matrix (K (Φ z))
      (hpos (Φ z)).isHermitian φ z ((hφ.differentiable (by simp)).differentiableAt) c hq⟩

end PoincareConjecture
