import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerConformalNormalization
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.CompetitorCoordinates











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Complex Matrix
open scoped Topology Manifold ContDiff Bundle Matrix.Norms.Elementwise

universe u

namespace PoincareConjecture

private def m65WeakBeltramiMetric (mu : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 + mu.re) ^ 2 + mu.im ^ 2, 2 * mu.im;
    2 * mu.im, (1 - mu.re) ^ 2 + mu.im ^ 2]

private theorem m65WeakBeltramiMetric_pos {mu : ℂ} (hmu : ‖mu‖ < 1) :
    (m65WeakBeltramiMetric mu).PosDef := by
  let S : Matrix (Fin 2) (Fin 2) ℝ := !![1 + mu.re, mu.im; mu.im, 1 - mu.re]
  have hd : 0 < S.det := by
    have hsq : mu.re ^ 2 + mu.im ^ 2 < 1 := by
      have hn : ‖mu‖ ^ 2 = mu.re ^ 2 + mu.im ^ 2 := by
        rw [← normSq_eq_norm_sq, normSq_apply]
        ring
      nlinarith [mul_self_lt_mul_self (norm_nonneg mu) hmu]
    simp only [S, det_fin_two, of_apply, cons_val_zero, cons_val_one,
      cons_val_fin_one]
    nlinarith only [hsq]
  have hS : Function.Injective S.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det S).mpr
      (isUnit_iff_ne_zero.mpr hd.ne'))
  have hrep : m65WeakBeltramiMetric mu = S.conjTranspose * S := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [m65WeakBeltramiMetric, S, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [hrep]
  exact Matrix.PosDef.conjTranspose_mul_self S hS

private theorem m65WeakBeltramiMetric_weight {mu : ℂ} (hmu : ‖mu‖ < 1)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (hH : H 1 0 = H 0 1) :
    Matrix.isothermalEnergyWeight (m65WeakBeltramiMetric mu) H =
      ((1 + ‖mu‖ ^ 2) * ((H 0 0 + H 1 1) / 2) -
        mu.re * (H 0 0 - H 1 1) - 2 * mu.im * H 0 1) / (1 - ‖mu‖ ^ 2) := by
  let d := 1 - ‖mu‖ ^ 2
  have hd : 0 < d := by
    have hh := (sq_lt_sq₀ (norm_nonneg mu) (by norm_num : (0 : ℝ) ≤ 1)).mpr hmu
    dsimp only [d]
    nlinarith only [hh]
  have hnorm : ‖mu‖ ^ 2 = mu.re ^ 2 + mu.im ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]
    ring
  have hdet : (m65WeakBeltramiMetric mu).det = d ^ 2 := by
    simp only [m65WeakBeltramiMetric, det_fin_two, of_apply, cons_val_zero,
      cons_val_one, cons_val_fin_one, d, hnorm]
    ring
  rw [Matrix.isothermalEnergyWeight, hdet, Real.sqrt_sq hd.le,
    Matrix.inv_def, hdet, Ring.inverse_eq_inv, Matrix.adjugate_fin_two]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
    smul_eq_mul, m65WeakBeltramiMetric, of_apply, cons_val_zero, cons_val_one,
    cons_val_fin_one, hH]
  change _ = _ / d
  rw [hnorm]
  dsimp only [d] at hd ⊢
  rw [hnorm] at hd ⊢
  field_simp [hd.ne']
  ring

private theorem m65Weak_gram_chain {N : ℕ}
    (H : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (d : Fin 2 → EuclideanSpace ℝ (Fin N)) (A : LoopPlane →L[ℝ] LoopPlane) :
    let B := LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis A.toLinearMap
    let G : Matrix (Fin 2) (Fin 2) ℝ := fun i j => H (d i) (d j)
    (1 / 2 : ℝ) * ∑ i : Fin 2,
      H (∑ j : Fin 2, (A (EuclideanSpace.basisFun (Fin 2) ℝ i)) j • d j)
        (∑ j : Fin 2, (A (EuclideanSpace.basisFun (Fin 2) ℝ i)) j • d j) =
      (1 / 2 : ℝ) * (B.transpose * G * B).trace := by
  dsimp only
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_repr, ContinuousLinearMap.coe_coe,
    map_add, map_smul, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)}
  {gamma : LoopCircle → M}

private theorem m65Beltrami_metric_symm (g : RiemannianMetric 3 M)
    (p : M) (v w : EuclideanSpace ℝ (Fin N)) :
    m65EmbeddingMetric g e p v w = m65EmbeddingMetric g e p w v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have : FiniteDimensional ℝ (TangentSpace (𝓡 3) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) p
  have : CompleteSpace (TangentSpace (𝓡 3) p) := FiniteDimensional.complete ℝ _
  unfold m65EmbeddingMetric
  exact M65Interior.ambientMetric_symmetric _ v w





def M65WeakDisk.beltramiEnergyDensity (F : M65WeakDisk e gamma)
    (g : RiemannianMetric 3 M) (mu : LoopPlane → ℂ) (z : LoopPlane) : ℝ :=
  let H := m65EmbeddingMetric g e (F.value z)
  let a := H (F.derivative 0 z) (F.derivative 0 z)
  let b := H (F.derivative 0 z) (F.derivative 1 z)
  let c := H (F.derivative 1 z) (F.derivative 1 z)
  ((1 + ‖mu z‖ ^ 2) * ((a + c) / 2) - (mu z).re * (a - c) -
    2 * (mu z).im * b) / (1 - ‖mu z‖ ^ 2)

set_option maxHeartbeats 1600000 in






theorem m65WeakDisk_beltrami_change (g : RiemannianMetric 3 M)
    (he : Continuous e) (hgamma : Continuous gamma) (F : M65WeakDisk e gamma)
    (mu : LoopPlane → ℂ) (hmu : ContDiff ℝ ∞ mu)
    (hzero : ∀ᶠ z in 𝓝 (0 : LoopPlane), mu z = 0)
    (hout : ∀ z, 1 ≤ ‖z‖ → mu z = 0) (hsub : ∀ z, ‖mu z‖ < 1) :
    ∃ G : M65WeakDisk e gamma,
      G.energy g = ∫ z in loopDiskSet, F.beltramiEnergyDensity g mu z := by
  let K := fun z => m65WeakBeltramiMetric (mu z)
  have hK : ContDiff ℝ ∞ K := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    have hr := Complex.reCLM.contDiff.comp hmu
    have hi := Complex.imCLM.contDiff.comp hmu
    fin_cases i <;> fin_cases j
    · exact ((contDiff_const.add hr).pow 2).add (hi.pow 2)
    · exact contDiff_const.mul hi
    · exact contDiff_const.mul hi
    · exact ((contDiff_const.sub hr).pow 2).add (hi.pow 2)
  have hKid : m65WeakBeltramiMetric 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [m65WeakBeltramiMetric]
  have hzK : ∀ᶠ z in 𝓝 (0 : LoopPlane), K z = (1 : ℝ) • 1 := by
    filter_upwards [hzero] with z hz
    simp only [K, hz, hKid, one_smul]
  have hoK (z : LoopPlane) (hz : 1 ≤ ‖z‖) : K z = (1 : ℝ) • 1 := by
    simp only [K, hout z hz, hKid, one_smul]
  obtain ⟨Phi, hPhi, hPsi, hclosed, hopen, hiso⟩ :=
    m65Exists_disk_isothermal_coordinates K hK (fun z => m65WeakBeltramiMetric_pos (hsub z))
      1 hzK hoK
  have hPhiDisk : MapsTo Phi loopDiskSet loopDiskSet := by
    intro z hz
    exact mem_closedBall_zero_iff.mpr ((hclosed z).mpr (mem_closedBall_zero_iff.mp hz))
  have hPsiDisk : MapsTo Phi.symm loopDiskSet loopDiskSet := by
    intro z hz
    apply mem_closedBall_zero_iff.mpr
    apply (hclosed (Phi.symm z)).mp
    simpa only [Phi.apply_symm_apply] using mem_closedBall_zero_iff.mp hz
  have hPhiCircle (z : LoopPlane) (hz : ‖z‖ = 1) : ‖Phi z‖ = 1 := by
    apply le_antisymm ((hclosed z).mpr hz.le)
    exact le_of_not_gt (fun hh => hz.not_lt ((hopen z).mp hh))
  have hPsiCircle (z : LoopPlane) (hz : ‖z‖ = 1) : ‖Phi.symm z‖ = 1 := by
    have hl : ‖Phi.symm z‖ ≤ 1 := by
      apply (hclosed (Phi.symm z)).mp
      simpa only [Phi.apply_symm_apply] using hz.le
    apply le_antisymm hl
    apply le_of_not_gt
    intro hh
    have hh' := (hopen (Phi.symm z)).mpr hh
    simp only [Phi.apply_symm_apply, hz, lt_self_iff_false] at hh'
  obtain ⟨G, hvalue, _hparameter, hderivative⟩ := m65WeakDisk_smooth_change he hgamma F
    Phi Phi.symm (hPhi.of_le (by simp)) (fun z _ => (hPsi.of_le (by simp)).contDiffAt)
    hPhiDisk hPsiDisk hPhiCircle hPsiCircle (fun z _ => Phi.symm_apply_apply z)
    (fun z _ => Phi.apply_symm_apply z)
  let H (z : LoopPlane) : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => m65EmbeddingMetric g e (F.value z) (F.derivative i z) (F.derivative j z)
  have hweight (z : LoopPlane) : Matrix.isothermalEnergyWeight (K z) (H z) =
      F.beltramiEnergyDensity g mu z :=
    m65WeakBeltramiMetric_weight (hsub z) (H z) (m65Beltrami_metric_symm g _ _ _)
  have hdensity : m65EmbeddedEnergyDensity g e G.value (fun i z => G.derivative i z)
      =ᵐ[volume.restrict loopDiskSet] fun z =>
        |(fderiv ℝ (Phi : LoopPlane → LoopPlane) z).det| •
          F.beltramiEnergyDensity g mu (Phi z) := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall,
      ae_all_iff.mpr hderivative] with z hz hdz
    obtain ⟨c, hc, hiso⟩ := hiso z hz
    let B := LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
        (fderiv ℝ (Phi : LoopPlane → LoopPlane) z).toLinearMap
    change (1 / 2 : ℝ) * ∑ i : Fin 2,
      m65EmbeddingMetric g e (G.value z) (G.derivative i z) (G.derivative i z) = _
    simp_rw [hdz, hvalue]
    rw [m65Weak_gram_chain]
    change (1 / 2 : ℝ) * (B.transpose * H (Phi z) * B).trace = _
    rw [Matrix.isothermal_energy_change (K (Phi z)) B (H (Phi z))
      (m65WeakBeltramiMetric_pos (hsub (Phi z))) hc hiso, hweight]
    have hdet : B.det = (fderiv ℝ (Phi : LoopPlane → LoopPlane) z).det :=
      LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis _
    rw [hdet]
    rfl
  refine ⟨G, ?_⟩
  change (∫ z in loopDiskSet,
    m65EmbeddedEnergyDensity g e G.value (fun i z => G.derivative i z) z) = _
  rw [integral_congr_ae hdensity]
  have himage : Phi '' loopDiskSet = loopDiskSet := by
    apply Subset.antisymm hPhiDisk.image_subset
    intro z hz
    exact ⟨Phi.symm z, hPsiDisk hz, Phi.apply_symm_apply z⟩
  calc
    _ = ∫ z in Phi '' loopDiskSet, F.beltramiEnergyDensity g mu z :=
      (integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_closedBall
        (fun z _ => (hPhi.differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt)
        (show InjOn Phi loopDiskSet from Phi.injective.injOn)
        (F.beltramiEnergyDensity g mu)).symm
    _ = _ := by rw [himage]

end PoincareConjecture
