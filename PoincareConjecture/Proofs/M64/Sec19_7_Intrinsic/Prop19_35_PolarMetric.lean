import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NoConjugate
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegularExponential

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_pullbackDensity_eq_sqrt_det_orthonormal
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (x : AnnulusCoordinates) (b : OrthonormalBasis (Fin 2) ℝ AnnulusCoordinates) :
    N.metric.pullbackVolumeDensity e x =
      Real.sqrt (Matrix.of (fun i j : Fin 2 =>
        N.metric.pullbackCoefficients e x (b i) (b j))).det := by
  let c := EuclideanSpace.basisFun (Fin 2) ℝ
  let B := (N.metric.pullbackCoefficients e x).toBilinForm
  have hchange := congrArg Matrix.det
    (LinearMap.BilinForm.toMatrix_mul_basis_toMatrix c.toBasis b.toBasis B)
  simp only [Matrix.det_mul, Matrix.det_transpose, b.coe_toBasis] at hchange
  have hdet : (c.toBasis.toMatrix b).det ^ 2 = 1 := by
    rcases c.det_to_matrix_orthonormalBasis_real b with h | h
    · rw [Module.Basis.det_apply] at h
      rw [h]
      norm_num
    · rw [Module.Basis.det_apply] at h
      rw [h]
      norm_num
  have hgram : (LinearMap.BilinForm.toMatrix c.toBasis B).det =
      (LinearMap.BilinForm.toMatrix b.toBasis B).det := by
    calc
      _ = (c.toBasis.toMatrix b).det ^ 2 *
          (LinearMap.BilinForm.toMatrix c.toBasis B).det := by rw [hdet, one_mul]
      _ = (c.toBasis.toMatrix b).det *
          (LinearMap.BilinForm.toMatrix c.toBasis B).det *
            (c.toBasis.toMatrix b).det := by ring
      _ = _ := hchange
  calc
    _ = Real.sqrt (LinearMap.BilinForm.toMatrix c.toBasis B).det := by
      unfold RiemannianMetric.pullbackVolumeDensity
      congr 2
      ext i j
      rw [LinearMap.BilinForm.toMatrix_apply]
      rfl
    _ = Real.sqrt (LinearMap.BilinForm.toMatrix b.toBasis B).det := by rw [hgram]
    _ = _ := by
      congr 2
      ext i j
      rw [LinearMap.BilinForm.toMatrix_apply]
      rfl

theorem m64Intrinsic_radial_pullback_first_row
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (b : OrthonormalBasis (Fin 2) ℝ AnnulusCoordinates)
    {r : ℝ} (hr : 0 < r)
    (hgauss : ∀ w : AnnulusCoordinates,
      N.metric.pullbackCoefficients e (r • b 0) (r • b 0) w = inner ℝ (r • b 0) w)
    (w : AnnulusCoordinates) :
    N.metric.pullbackCoefficients e (r • b 0) (b 0) w = inner ℝ (b 0) w := by
  have h := hgauss w
  simp only [map_smul, smul_apply, smul_eq_mul,
    real_inner_smul_left] at h
  exact mul_left_cancel₀ hr.ne' h

theorem m64Intrinsic_radial_transverse_metric_eq_density_sq
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (b : OrthonormalBasis (Fin 2) ℝ AnnulusCoordinates)
    {r : ℝ} (hr : 0 < r)
    (hgauss : ∀ w : AnnulusCoordinates,
      N.metric.pullbackCoefficients e (r • b 0) (r • b 0) w = inner ℝ (r • b 0) w) :
    N.metric.pullbackCoefficients e (r • b 0) (b 1) (b 1) =
      N.metric.pullbackVolumeDensity e (r • b 0) ^ 2 := by
  have hrow := m64Intrinsic_radial_pullback_first_row N e b hr hgauss
  have h00 : N.metric.pullbackCoefficients e (r • b 0) (b 0) (b 0) = 1 := by
    rw [hrow]
    simp
  have h01 : N.metric.pullbackCoefficients e (r • b 0) (b 0) (b 1) = 0 := by
    rw [hrow]
    simp
  have hnonneg : 0 ≤ N.metric.pullbackCoefficients e (r • b 0) (b 1) (b 1) := by
    let v := mfderiv (𝓡 2) (𝓡 2) e (r • b 0) (b 1)
    change 0 ≤ N.metric.inner (e (r • b 0)) v v
    by_cases hv : v = 0
    · simp only [hv, map_zero, le_refl]
    · exact (N.metric.pos _ _ hv).le
  rw [m64Intrinsic_pullbackDensity_eq_sqrt_det_orthonormal N e _ b,
    Matrix.det_fin_two, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply,
    Matrix.of_apply, h00, h01, one_mul, zero_mul, sub_zero, Real.sq_sqrt hnonneg]

theorem m64Intrinsic_radial_pullback_metric
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (b : OrthonormalBasis (Fin 2) ℝ AnnulusCoordinates)
    {r : ℝ} (hr : 0 < r)
    (hgauss : ∀ w : AnnulusCoordinates,
      N.metric.pullbackCoefficients e (r • b 0) (r • b 0) w = inner ℝ (r • b 0) w)
    (w : AnnulusCoordinates) :
    N.metric.pullbackCoefficients e (r • b 0) w w =
      inner ℝ (b 0) w ^ 2 +
        N.metric.pullbackVolumeDensity e (r • b 0) ^ 2 * inner ℝ (b 1) w ^ 2 := by
  have hrow := m64Intrinsic_radial_pullback_first_row N e b hr hgauss
  have hcol : N.metric.pullbackCoefficients e (r • b 0) (b 1) (b 0) = 0 := by
    change N.metric.inner (e (r • b 0))
      (mfderiv (𝓡 2) (𝓡 2) e (r • b 0) (b 1))
      (mfderiv (𝓡 2) (𝓡 2) e (r • b 0) (b 0)) = 0
    rw [N.metric.symm]
    change N.metric.pullbackCoefficients e (r • b 0) (b 0) (b 1) = 0
    rw [hrow]
    simp
  have hw : inner ℝ (b 0) w • b 0 + inner ℝ (b 1) w • b 1 = w := by
    simpa only [Fin.sum_univ_two] using b.sum_repr' w
  conv_lhs => rw [← hw]
  simp only [map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul, hrow, b.inner_eq_ite,
    Fin.zero_ne_one, if_false, if_true, hcol,
    m64Intrinsic_radial_transverse_metric_eq_density_sq N e b hr hgauss]
  ring

theorem m64Intrinsic_radial_christoffel_pairing
    (N : IntrinsicAnnulus) {e : AnnulusCoordinates → AnnulusCoordinates}
    (b : OrthonormalBasis (Fin 2) ℝ AnnulusCoordinates)
    {r : ℝ} (hr : 0 < r)
    (he : ContMDiffAt (𝓡 2) (𝓡 2) ∞ e (r • b 0))
    (hi : Function.Injective (mfderiv (𝓡 2) (𝓡 2) e (r • b 0)))
    (hgauss : ∀ᶠ s in 𝓝 r, ∀ w : AnnulusCoordinates,
      N.metric.pullbackCoefficients e (s • b 0) (s • b 0) w = inner ℝ (s • b 0) w)
    (w : AnnulusCoordinates) :
    let ρ : ℝ → ℝ := fun s => N.metric.pullbackVolumeDensity e (s • b 0)
    N.metric.pullbackCoefficients e (r • b 0)
      (coordinateChristoffel (N.metric.pullbackCoefficients e)
        (r • b 0) (r • b 0) w) w =
      r * ρ r * deriv ρ r * inner ℝ (b 1) w ^ 2 := by
  let B : AnnulusCoordinates → AnnulusCoordinates →L[ℝ] AnnulusCoordinates →L[ℝ] ℝ :=
    N.metric.pullbackCoefficients e
  let ρ : ℝ → ℝ := fun s => N.metric.pullbackVolumeDensity e (s • b 0)
  have hB : DifferentiableAt ℝ B (r • b 0) :=
    (N.metric.contDiffAt_pullbackCoefficients he).differentiableAt (by simp)
  have hρ : DifferentiableAt ℝ ρ r := by
    exact ((N.metric.contDiffAt_pullbackVolumeDensity he hi).1.comp
      (f := fun s : ℝ => s • b 0) r (by fun_prop)).differentiableAt (by simp)
  have hline : HasDerivAt (fun s : ℝ => s • b 0) (b 0) r := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id r).smul_const (b 0)
  have hpair : HasDerivAt (fun s => B (s • b 0) w w)
      (fderiv ℝ B (r • b 0) (b 0) w w) r := by
    have hBd : HasDerivAt (fun s => B (s • b 0))
        (fderiv ℝ B (r • b 0) (b 0)) r := by
      exact HasFDerivAt.comp_hasDerivAt (l := B) (f := fun s : ℝ => s • b 0)
        r hB.hasFDerivAt hline
    simpa only [map_zero, add_zero] using
      (hBd.clm_apply (hasDerivAt_const r w)).clm_apply (hasDerivAt_const r w)
  have hscalar : HasDerivAt
      (fun s => inner ℝ (b 0) w ^ 2 + ρ s ^ 2 * inner ℝ (b 1) w ^ 2)
      (2 * ρ r * deriv ρ r * inner ℝ (b 1) w ^ 2) r := by
    convert! ((hρ.hasDerivAt.pow 2).mul_const (inner ℝ (b 1) w ^ 2)).const_add
      (inner ℝ (b 0) w ^ 2) using 1
    norm_num
  have heq : (fun s => B (s • b 0) w w) =ᶠ[𝓝 r]
      (fun s => inner ℝ (b 0) w ^ 2 + ρ s ^ 2 * inner ℝ (b 1) w ^ 2) := by
    filter_upwards [hgauss, Ioi_mem_nhds hr] with s hgs hs
    exact m64Intrinsic_radial_pullback_metric N e b hs hgs w
  have hd : fderiv ℝ B (r • b 0) (b 0) w w =
      2 * ρ r * deriv ρ r * inner ℝ (b 1) w ^ 2 :=
    hpair.deriv.symm.trans (heq.deriv_eq.trans hscalar.deriv)
  have hsymm : ∀ᶠ x in 𝓝 (r • b 0), ∀ u v, B x u v = B x v u :=
    Eventually.of_forall fun _ _ _ => N.metric.symm _ _ _
  have hm := CoordinateExponential.fderiv_metric_eq_christoffel hB
    (N.metric.isInvertible_pullbackCoefficients hi) hsymm w w (r • b 0)
  rw [hsymm.self_of_nhds w (coordinateChristoffel B (r • b 0) (r • b 0) w)] at hm
  simp only [map_smul, smul_apply, smul_eq_mul, hd] at hm
  change B (r • b 0)
    (coordinateChristoffel B (r • b 0) (r • b 0) w) w =
      r * ρ r * deriv ρ r * inner ℝ (b 1) w ^ 2
  nlinarith [hm]

end PoincareConjecture
