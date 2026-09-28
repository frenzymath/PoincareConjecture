import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetResidualPlane
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.MinimalDiskInteriorFactor
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.MinimalDiskConformal
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceBoundaryDifferential











set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.M65Gauss

open M65Branch



def complexResidualEnergy {n : ℕ}
    (G : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (q : Fin n → ℂ) : ℝ :=
  (G (residualRealColumn q) (residualRealColumn q) +
    G (residualImagColumn q) (residualImagColumn q)) / 2




theorem complexResidualEnergy_pos {n : ℕ}
    (G : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hG : ∀ v, v ≠ 0 → 0 < G v v) {q : Fin n → ℂ} (hq : q ≠ 0) :
    0 < complexResidualEnergy G q := by
  have hnon (v : EuclideanSpace ℝ (Fin n)) : 0 ≤ G v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (hG v hv).le
  apply div_pos _ (by norm_num : (0 : ℝ) < 2)
  by_cases ha : residualRealColumn q = 0
  · have hb : residualImagColumn q ≠ 0 := by
      intro hb
      apply hq
      rw [← residual_columns_recover q, ha, hb, map_zero, smul_zero, sub_zero]
    exact add_pos_of_nonneg_of_pos (hnon _) (hG _ hb)
  · exact add_pos_of_pos_of_nonneg (hG _ ha) (hnon _)




theorem complexResidualEnergy_smul {n : ℕ}
    (G : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (s : ℂ) (q : Fin n → ℂ) :
    complexResidualEnergy G (s • q) = ‖s‖ ^ 2 * complexResidualEnergy G q := by
  obtain ⟨ha, hb⟩ := residual_columns_smul s q
  simp only [complexResidualEnergy, ha, hb, map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul, Complex.sq_norm, Complex.normSq_apply]
  ring

end PoincareConjecture.M65Gauss

namespace PoincareConjecture.M65MinimalDisk

open M65Branch M65StrictTrace M65Gauss

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}





theorem interior_conformalFactor_power (S : M65MinimalDisk g connection gamma)
    {x : LoopPlane} (hx : x ∈ ball (0 : LoopPlane) 1) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let z0 := e.symm x
    ∃ (m : ℕ) (rho : ℂ → ℝ), ContDiffAt ℝ 1 rho z0 ∧ 0 < rho z0 ∧
      ∀ᶠ z in 𝓝 z0,
        S.conformalFactor (e z) = ‖z - z0‖ ^ (2 * m) * rho z := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let z0 := e.symm x
  let chart := chartAt LoopAmbient (S.disk.map x)
  let G := chart ∘ S.disk.map
  let H := G ∘ e
  obtain ⟨gE, DE, V, hV, hxV, hVdisk, hsource, hG, hmetric, _heq⟩ :=
    S.exists_harmonic_chart_neighborhood hx
  obtain ⟨m, Q, hQ, hQ0, hfac⟩ := S.interior_branch_power_factor hx
  have he0 : e z0 = x := e.apply_symm_apply x
  have hH : ContDiffAt ℝ ∞ H z0 := by
    have hGG : ContDiffAt ℝ ∞ G x := hG.contDiffAt (hV.mem_nhds hxV)
    exact (he0.symm ▸ hGG).comp z0 e.contDiff.contDiffAt
  let rho := fun z => complexResidualEnergy (gE.euclideanCoefficients (H z)) (Q z)
  have hGc : ContDiffAt ℝ 1 (fun z => gE.euclideanCoefficients (H z)) z0 :=
    ((gE.contDiffAt_euclideanCoefficients (H z0)).of_le (by simp)).comp z0
      (hH.of_le (by simp))
  have hRa := residualRealColumn.contDiff.contDiffAt.comp z0 hQ
  have hRb := residualImagColumn.contDiff.contDiffAt.comp z0 hQ
  have hrho : ContDiffAt ℝ 1 rho z0 :=
    (((hGc.clm_apply hRa).clm_apply hRa).add
      ((hGc.clm_apply hRb).clm_apply hRb)).div_const 2
  refine ⟨m, rho, hrho, complexResidualEnergy_pos _ (gE.pos (H z0)) hQ0, ?_⟩
  have hpre : ∀ᶠ z in 𝓝 z0, e z ∈ V := by
    have he : Tendsto e (𝓝 z0) (𝓝 x) := by
      have hh : Tendsto e (𝓝 z0) (𝓝 (e z0)) := e.continuous.continuousAt
      simpa only [ContinuousAt, he0] using hh
    exact he (hV.mem_nhds hxV)
  let K := ball (0 : ℂ) 1
  have hmap : MapsTo (orthonormalBasisOneI.repr ∘ (fun z : ℂ => z)) K loopDiskSet := by
    intro z hz
    rw [loopDiskSet, mem_closedBall_zero_iff]
    change ‖orthonormalBasisOneI.repr z‖ ≤ 1
    rw [orthonormalBasisOneI.repr.norm_map]
    exact (mem_ball_zero_iff.mp hz).le
  filter_upwards [hpre, hfac] with z hzV hzfac
  change complexGradient H z = (z - z0) ^ m • Q z at hzfac
  have hzK : z ∈ K := by
    have hz := hVdisk hzV
    rw [mem_ball_zero_iff] at hz ⊢
    change ‖orthonormalBasisOneI.repr z‖ < 1 at hz
    rwa [orthonormalBasisOneI.repr.norm_map] at hz
  have hnorm (v : ℂ) :
      gE.euclideanCoefficients (H z) (fderiv ℝ H z v) (fderiv ℝ H z v) =
        S.conformalFactor (e z) * ‖v‖ ^ 2 := by
    have hh := complex_parameter_within_conformal_norm g gE (S.disk.map x)
      S.boundary_regular S.weakly_conformal (isOpen_ball.uniqueDiffOn z hzK) hzK
      (hasDerivAt_id z) hmap (hsource hzV) (hmetric (e z) hzV) v
    dsimp only at hh
    rw [fderivWithin_of_mem_nhds (isOpen_ball.mem_nhds hzK)] at hh
    simpa +instances only [Function.comp_id, id_eq, norm_one, one_pow, mul_one,
      H, G, chart, e, conformalFactor, boundaryColumn, diskConformalFactor, diskColumn] using! hh
  have he : complexResidualEnergy (gE.euclideanCoefficients (H z))
      (complexGradient H z) = S.conformalFactor (e z) := by
    rw [complexResidualEnergy, (residual_columns_complexGradient H z).1,
      (residual_columns_complexGradient H z).2, hnorm 1, hnorm I]
    simp only [norm_one, norm_I, one_pow, mul_one]
    ring
  calc
    S.conformalFactor (e z) = complexResidualEnergy (gE.euclideanCoefficients (H z))
        (complexGradient H z) := he.symm
    _ = ‖(z - z0) ^ m‖ ^ 2 * rho z := by
      rw [hzfac, complexResidualEnergy_smul]
    _ = ‖z - z0‖ ^ (2 * m) * rho z := by rw [norm_pow, ← pow_mul, Nat.mul_comm m 2]

end PoincareConjecture.M65MinimalDisk
