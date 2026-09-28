import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetFrameConnection
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetMinimalDiskPotential











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M65Gauss

open M65Branch M65StrictTrace





theorem boundaryCoordinate_logarithmic_radial
    {lambda localFactor : ℂ → ℝ} {p z : ℂ} (hp : ‖p‖ = 1)
    (hlambda : DifferentiableAt ℝ lambda (boundaryCoordinate p z))
    (hne : lambda (boundaryCoordinate p z) ≠ 0)
    (heq : localFactor =ᶠ[𝓝 z] fun w =>
      lambda (boundaryCoordinate p w) * ‖I * boundaryCoordinate p w‖ ^ 2) :
    -fderiv ℝ (fun w => Real.log (localFactor w)) z I / 2 =
      fderiv ℝ (fun w => Real.log (lambda w))
        (boundaryCoordinate p z) (boundaryCoordinate p z) / 2 + 1 := by
  let P := boundaryCoordinate p
  have hP := (hasDerivAt_boundaryCoordinate p z).hasFDerivAt.restrictScalars ℝ
  have hPI : fderiv ℝ P z I = -P z := by
    rw [hP.fderiv]
    change I * (I * P z) = -P z
    rw [← mul_assoc, I_mul_I, neg_one_mul]
  have hnear : ∀ᶠ w in 𝓝 z, lambda (P w) ≠ 0 :=
    (hlambda.continuousAt.comp hP.continuousAt).eventually_ne hne
  have hlogs : (fun w => Real.log (localFactor w)) =ᶠ[𝓝 z]
      fun w => Real.log (lambda (P w)) - 2 * w.im := by
    filter_upwards [heq, hnear] with w hw hn
    rw [hw, norm_mul, norm_I, one_mul, norm_boundaryCoordinate hp,
      Real.log_mul hn (pow_ne_zero 2 (Real.exp_ne_zero _)), Real.log_pow, Real.log_exp]
    change Real.log (lambda (P w)) + (2 : ℝ) * -w.im = _
    ring
  have hD := ((hlambda.log hne).hasFDerivAt.comp z hP.differentiableAt.hasFDerivAt).sub
    (Complex.imCLM.hasFDerivAt.const_mul (2 : ℝ))
  have hv := congrArg (fun L : ℂ →L[ℝ] ℝ => L I) hD.fderiv
  change fderiv ℝ (fun w => Real.log (lambda (P w)) - 2 * w.im) z I = _ at hv
  simp only [sub_apply, ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul,
    Complex.imCLM_apply, I_im, mul_one] at hv
  dsimp only [P] at hPI
  rw [hPI, map_neg] at hv
  rw [hlogs.fderiv_eq]
  linarith only [hv]






theorem residual_boundary_radial_le {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g) (m : ℕ)
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {Q : ℂ → Fin n → ℂ}
    {lambda : ℂ → ℝ} {p z : ℂ} (hp : ‖p‖ = 1) (hz : 0 < z.im)
    (hH : ContDiffAt ℝ ∞ H z) (hQ : DifferentiableAt ℝ Q z) (hQne : Q z ≠ 0)
    (hlambda : DifferentiableAt ℝ lambda (boundaryCoordinate p z))
    (hfactor : ∀ᶠ w in 𝓝 z, complexGradient H w = w ^ m • Q w)
    (hnorm : ∀ᶠ w in 𝓝 z, ∀ v : ℂ,
      g.inner (H w) (fderiv ℝ H w v) (fderiv ℝ H w v) =
        lambda (boundaryCoordinate p w) * ‖I * boundaryCoordinate p w‖ ^ 2 * ‖v‖ ^ 2) :
    let F := fun w => normalizedResidualFrame (g.euclideanCoefficients (H w)) (Q w)
    fderiv ℝ (fun w => Real.log (lambda w))
        (boundaryCoordinate p z) (boundaryCoordinate p z) / 2 ≤
      g.inner (H z) (covariantDerivativeAlongMap D H (fun w => (F w).1) z 1)
        (F z).2 - 1 := by
  let localFactor := fun w => g.inner (H w) (fderiv ℝ H w 1) (fderiv ℝ H w 1)
  have hconf : ∀ᶠ w in 𝓝 z,
      g.inner (H w) (fderiv ℝ H w 1) (fderiv ℝ H w 1) =
        g.inner (H w) (fderiv ℝ H w I) (fderiv ℝ H w I) ∧
      g.inner (H w) (fderiv ℝ H w 1) (fderiv ℝ H w I) = 0 := by
    filter_upwards [hnorm] with w hw
    have h1 := hw 1
    have hI := hw I
    have hsum := hw (1 + I)
    have hnormsum : ‖(1 : ℂ) + I‖ ^ 2 = 2 := by
      norm_num [Complex.sq_norm, Complex.normSq_apply]
    simp only [norm_one, norm_I, one_pow, mul_one] at h1 hI
    rw [hnormsum, map_add] at hsum
    simp only [map_add, add_apply] at hsum
    rw [g.symm (H w) (fderiv ℝ H w I) (fderiv ℝ H w 1)] at hsum
    exact ⟨h1.trans hI.symm, by linarith⟩
  have heq : localFactor =ᶠ[𝓝 z] fun w =>
      lambda (boundaryCoordinate p w) * ‖I * boundaryCoordinate p w‖ ^ 2 := by
    filter_upwards [hnorm] with w hw
    simpa only [norm_one, one_pow, mul_one] using hw 1
  have hzne : z ≠ 0 := by
    intro h
    simp only [h, zero_im, lt_self_iff_false] at hz
  have hgradne : complexGradient H z ≠ 0 := by
    rw [hfactor.self_of_nhds]
    exact smul_ne_zero (pow_ne_zero m hzne) hQne
  have hpos : 0 < localFactor z := by
    have hh := residual_columns_factor_pos (g.euclideanCoefficients (H z))
      (g.pos (H z)) hgradne
      (by simpa +instances only [(residual_columns_complexGradient H z).1,
        (residual_columns_complexGradient H z).2] using! hconf.self_of_nhds.1.symm)
    simpa +instances only [localFactor, (residual_columns_complexGradient H z).1] using! hh
  have hne : lambda (boundaryCoordinate p z) ≠ 0 := by
    intro h
    have he : localFactor z =
        lambda (boundaryCoordinate p z) * ‖I * boundaryCoordinate p z‖ ^ 2 := heq.self_of_nhds
    rw [he, h, zero_mul] at hpos
    exact (lt_irrefl 0) hpos
  have hradial := boundaryCoordinate_logarithmic_radial hp hlambda hne heq
  have hconnection := (residual_frame_connection_log D m hz hH hQ hQne hfactor hconf).2
  dsimp only at hconnection ⊢
  linarith only [hradial, hconnection]

end PoincareConjecture.M65Gauss

namespace PoincareConjecture.M65MinimalDisk

open M65Branch M65StrictTrace M65Gauss MeasureTheory
open scoped Manifold

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}

set_option maxHeartbeats 1200000 in







theorem boundary_branch_radial_connection (S : M65MinimalDisk g connection gamma)
    (hinj : Function.Injective (gamma : LoopCircle → M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ s : ℝ, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) s ≠ 0)
    {x : LoopPlane} (hx : ‖x‖ = 1) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let p := e.symm x
    let chart := chartAt LoopAmbient (S.disk.map x)
    let P := e ∘ boundaryCoordinate p
    let H := chart ∘ S.disk.map ∘ P
    ∃ (gE : RiemannianMetric 3 LoopAmbient) (DE : LeviCivitaData gE)
      (r : ℝ) (m : ℕ) (Q : ℂ → Fin 3 → ℂ), 0 < r ∧ Even m ∧
      let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
      let W := ball (0 : ℂ) r ∩ {z | 0 < z.im}
      let F := fun z => normalizedResidualFrame (gE.euclideanCoefficients (H z)) (Q z)
      MapsTo P K loopDiskSet ∧ MapsTo (S.disk.map ∘ P) K chart.source ∧
      ContDiffOn ℝ 1 H K ∧ ContDiffOn ℝ ∞ H W ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 (H z), ∀ a b : LoopAmbient,
        gE.inner y a b = g.inner (chart.symm y)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y a)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y b)) ∧
      (∀ z ∈ K, ∀ v : ℂ,
        gE.inner (H z) (fderivWithin ℝ H K z v) (fderivWithin ℝ H K z v) =
          diskConformalFactor g S.disk.map (P z) *
            ‖I * boundaryCoordinate p z‖ ^ 2 * ‖v‖ ^ 2) ∧
      ContinuousOn Q K ∧ ContDiffOn ℝ 1 Q W ∧
      (∀ z ∈ K, Q z ≠ 0) ∧
      (∀ z ∈ K, halfDiskGradient H r z = z ^ m • Q z) ∧
      ContinuousOn F K ∧ ContDiffOn ℝ 1 F W ∧
      (∀ z ∈ K, gE.inner (H z) (F z).1 (F z).1 = 1 ∧
        gE.inner (H z) (F z).1 (F z).2 = 0 ∧
        gE.inner (H z) (F z).2 (F z).2 = 1) ∧
      MemLp (fun z => fderiv ℝ F z 1) 2 (volume.restrict W) ∧
      MemLp (fun z => fderiv ℝ F z I) 2 (volume.restrict W) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ w ∈ K,
        ‖F z - F w‖ ≤ C * Real.sqrt ‖z - w‖) ∧
      ∀ z ∈ W,
        fderiv ℝ (fun w => Real.log (S.conformalFactor (e w)))
            (boundaryCoordinate p z) (boundaryCoordinate p z) / 2 ≤
          gE.inner (H z) (covariantDerivativeAlongMap DE H (fun w => (F w).1) z 1)
            (F z).2 - 1 := by
  obtain ⟨gE, DE, r, m, Q, hr, hm, hP, hsource, hH, hHi, hg, hn, _heq,
      hQc, hQi, hQne, hf, hFc, hFi, hForth, hF1, hFI, hholder⟩ :=
    S.boundary_branch_frame hinj hsmooth hregular hx
  refine ⟨gE, DE, r, m, Q, hr, hm, hP, hsource, hH, hHi, hg, hn,
    hQc, hQi, hQne, hf, hFc, hFi, hForth, hF1, hFI, hholder, ?_⟩
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let p := e.symm x
  let P := e ∘ boundaryCoordinate p
  let H := (chartAt LoopAmbient (S.disk.map x)) ∘ S.disk.map ∘ P
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let W := ball (0 : ℂ) r ∩ {z | 0 < z.im}
  have hp : ‖p‖ = 1 := by
    change ‖orthonormalBasisOneI.repr.symm x‖ = 1
    rw [orthonormalBasisOneI.repr.symm.norm_map, hx]
  have hW : IsOpen W := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hWK : W ⊆ K := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  intro z hz
  have hzin : boundaryCoordinate p z ∈ ball (0 : ℂ) 1 :=
    mem_ball_zero_iff.mpr ((boundaryCoordinate_interior_iff hp z).mpr hz.2)
  apply residual_boundary_radial_le DE m hp hz.2
    (hHi.contDiffAt (hW.mem_nhds hz))
    ((hQi.contDiffAt (hW.mem_nhds hz)).differentiableAt one_ne_zero) (hQne z (hWK hz))
    ((S.conformalFactor_complex_contDiffOn.contDiffAt
      (isOpen_ball.mem_nhds hzin)).differentiableAt (by simp))
  · filter_upwards [hW.mem_nhds hz] with w hw
    have hh := hf w (hWK hw)
    simp only [halfDiskGradient, fderivWithin_of_mem_nhds (halfDisk_mem_nhds hw)] at hh
    exact hh
  · filter_upwards [hW.mem_nhds hz] with w hw
    intro v
    have hh := hn w (hWK hw) v
    rw [fderivWithin_of_mem_nhds (halfDisk_mem_nhds hw)] at hh
    simpa +instances only [conformalFactor, boundaryColumn, diskConformalFactor,
      diskColumn, Function.comp_apply, e, p, P, H] using! hh

end PoincareConjecture.M65MinimalDisk
