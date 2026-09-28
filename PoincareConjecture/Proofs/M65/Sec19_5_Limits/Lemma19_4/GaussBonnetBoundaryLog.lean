import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryIntegrability
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetLogIntegrability

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric MeasureTheory
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.M65Branch

open M65StrictTrace M65Gauss

theorem halfDisk_logarithmicDensity_integrable {n : ℕ} [Nonempty (Fin n)]
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {Q : ℂ → Fin n → ℂ}
    {r : ℝ} (hr : 0 < r) (m : ℕ)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hHi : ContDiffOn ℝ ∞ H (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (hQ : ContinuousOn Q (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hQ1 : ContDiffOn ℝ 1 Q (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (hQne : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}, Q z ≠ 0)
    (hfactor : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      halfDiskGradient H r z = z ^ m • Q z)
    (hconf : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      let T := fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z
      g.inner (H z) (T 1) (T 1) = g.inner (H z) (T I) (T I) ∧
        g.inner (H z) (T 1) (T I) = 0)
    (hDQ1 : MemLp (fun z => fderiv ℝ Q z 1)
      2 (volume.restrict (ball (0 : ℂ) r ∩ {z | 0 < z.im})))
    (hDQI : MemLp (fun z => fderiv ℝ Q z I)
      2 (volume.restrict (ball (0 : ℂ) r ∩ {z | 0 < z.im}))) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
    let W := ball (0 : ℂ) r ∩ {z | 0 < z.im}
    let F := H ∘ e.symm
    let lam := fun z => g.inner (F z)
      (fderivWithin ℝ H K (e.symm z) 1) (fderivWithin ℝ H K (e.symm z) 1)
    IntegrableOn (fun z => -(∑ i : Fin 2, fderiv ℝ (fun y =>
      fderiv ℝ (fun w => Real.log (lam w)) y (EuclideanSpace.basisFun (Fin 2) ℝ i))
        z (EuclideanSpace.basisFun (Fin 2) ℝ i)) / 2) (e.symm ⁻¹' W) volume := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let W := ball (0 : ℂ) r ∩ {z | 0 < z.im}
  let Kp := e.symm ⁻¹' K
  let Wp := e.symm ⁻¹' W
  let F := H ∘ e.symm
  let lamC := fun z => g.euclideanCoefficients (H z)
    (fderivWithin ℝ H K z 1) (fderivWithin ℝ H K z 1)
  let lam := lamC ∘ e.symm
  obtain ⟨hW, _hKclosed, hKun, _hclosure⟩ := halfDisk_differential_domain hr
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) r).inter_right
    (isClosed_le continuous_const continuous_im)
  have hWK : W ⊆ K := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  have hKp : IsCompact Kp := e.symm.toHomeomorph.isCompact_preimage.mpr hK
  have hWp : IsOpen Wp := hW.preimage e.symm.continuous
  have hWpKp : Wp ⊆ Kp := preimage_mono hWK
  have hFs : ContDiffOn ℝ ∞ F Wp := hHi.comp e.symm.contDiff.contDiffOn (fun _ hz => hz)
  have hFc : ContinuousOn F Kp :=
    hH.continuousOn.comp e.symm.continuous.continuousOn (fun _ hz => hz)
  have hGc : ContinuousOn (fun z => g.euclideanCoefficients (H z)) K :=
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).continuous.comp_continuousOn
      hH.continuousOn
  have hDc : ContinuousOn (fun z => fderivWithin ℝ H K z 1) K :=
    (hH.continuousOn_fderivWithin hKun le_rfl).clm_apply continuousOn_const
  have hlam : ContinuousOn lam Kp :=
    ((hGc.clm_apply hDc).clm_apply hDc).comp e.symm.continuous.continuousOn
      (fun _ hz => hz)
  have he0 : e.symm (b 0) = (1 : ℂ) := by
    apply e.injective
    rw [e.apply_symm_apply]
    ext k
    fin_cases k <;> simp [e, b, orthonormalBasisOneI_repr_apply, EuclideanSpace.basisFun_apply]
  have heI : e.symm (b 1) = I := by
    apply e.injective
    rw [e.apply_symm_apply]
    ext k
    fin_cases k <;> simp [e, b, orthonormalBasisOneI_repr_apply, EuclideanSpace.basisFun_apply]
  have hF0 (z : LoopPlane) : fderiv ℝ F z (b 0) = fderiv ℝ H (e.symm z) 1 := by
    rw [e.symm.comp_right_fderiv]
    change fderiv ℝ H (e.symm z) (e.symm (b 0)) = _
    rw [he0]
  have hF1 (z : LoopPlane) : fderiv ℝ F z (b 1) = fderiv ℝ H (e.symm z) I := by
    rw [e.symm.comp_right_fderiv]
    change fderiv ℝ H (e.symm z) (e.symm (b 1)) = _
    rw [heI]
  have hlamEq (z : LoopPlane) (hz : z ∈ Wp) :
      lam z = g.euclideanCoefficients (F z)
        (fderiv ℝ H (e.symm z) 1) (fderiv ℝ H (e.symm z) 1) := by
    change g.euclideanCoefficients (H (e.symm z))
      (fderivWithin ℝ H K (e.symm z) 1) (fderivWithin ℝ H K (e.symm z) 1) = _
    rw [fderivWithin_of_mem_nhds (halfDisk_mem_nhds hz)]
    rfl
  have hGs : ContDiffOn ℝ ∞ (fun z => g.euclideanCoefficients (F z)) Wp :=
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).comp_contDiffOn hFs
  have hDs : ContDiffOn ℝ ∞ (fun z => fderiv ℝ F z (b 0)) Wp :=
    (hFs.fderiv_of_isOpen (m := ∞) hWp (by simp)).clm_apply contDiffOn_const
  have hlams : ContDiffOn ℝ ∞ lam Wp := by
    apply ((hGs.clm_apply hDs).clm_apply hDs).congr
    intro z hz
    rw [hlamEq z hz, hF0]
  obtain ⟨_hPC, _hPCeq, hpos, _hP1, _hPI⟩ :=
    halfDisk_residual_projection g hr m hH hQ hQ1 hQne hfactor hconf hDQ1 hDQI
  have hGram (z : LoopPlane) (hz : z ∈ Wp) :
      0 < lam z ∧ m60AreaGram g F z = lam z • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    have hc := hconf (e.symm z) (hWK hz)
    dsimp only at hc
    rw [fderivWithin_of_mem_nhds (halfDisk_mem_nhds hz)] at hc
    change g.euclideanCoefficients (F z) (fderiv ℝ H (e.symm z) 1)
        (fderiv ℝ H (e.symm z) 1) = g.euclideanCoefficients (F z)
          (fderiv ℝ H (e.symm z) I) (fderiv ℝ H (e.symm z) I) ∧
      g.euclideanCoefficients (F z) (fderiv ℝ H (e.symm z) 1)
        (fderiv ℝ H (e.symm z) I) = 0 at hc
    refine ⟨by rw [hlamEq z hz]; exact hpos (e.symm z) hz, ?_⟩
    have hpair (a d : Fin 2) :
        g.euclideanCoefficients (F z) (fderiv ℝ F z (b a)) (fderiv ℝ F z (b d)) =
          if a = d then lam z else 0 := by
      fin_cases a <;> fin_cases d
      · change g.euclideanCoefficients (F z) (fderiv ℝ F z (b 0))
          (fderiv ℝ F z (b 0)) = lam z
        rw [hF0, hlamEq z hz]
      · change g.euclideanCoefficients (F z) (fderiv ℝ F z (b 0))
          (fderiv ℝ F z (b 1)) = 0
        rw [hF0, hF1]
        exact hc.2
      · change g.euclideanCoefficients (F z) (fderiv ℝ F z (b 1))
          (fderiv ℝ F z (b 0)) = 0
        rw [hF1, hF0]
        exact (g.symm _ _ _).trans hc.2
      · change g.euclideanCoefficients (F z) (fderiv ℝ F z (b 1))
          (fderiv ℝ F z (b 1)) = lam z
        rw [hF1, hlamEq z hz]
        exact hc.1.symm
    ext a d
    simpa +instances only [m60AreaGram, mfderiv_eq_fderiv, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, b] using! hpair a d
  have hN (i j : Fin 2) : IntegrableOn (fun z =>
      let B := normalHessian D F z (b i) (b j)
      g.inner (F z) B B / lam z) (Kp ∩ Wp) volume := by
    rw [inter_eq_right.mpr hWpKp]
    exact halfDisk_normalHessian_integrable D hr m hH hHi hQ hQ1 hQne hfactor
      hconf hDQ1 hDQI i j
  have hh := logarithmicDensity_integrableOn D hKp hWp hFc hFs hlam hlams hGram hN
  rw [inter_eq_right.mpr hWpKp] at hh
  exact hh

end PoincareConjecture.M65Branch

namespace PoincareConjecture.M65MinimalDisk

open M65Branch M65StrictTrace M65Gauss

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}

theorem boundary_logarithmicDensity_integrable (S : M65MinimalDisk g connection gamma)
    (hinj : Function.Injective (gamma : LoopCircle → M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ s : ℝ, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) s ≠ 0)
    {x : LoopPlane} (hx : ‖x‖ = 1) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let p := e.symm x
    let chart := chartAt LoopAmbient (S.disk.map x)
    let P := e ∘ boundaryCoordinate p
    let H := chart ∘ S.disk.map ∘ P
    ∃ (gE : RiemannianMetric 3 LoopAmbient) (DE : LeviCivitaData gE) (r : ℝ),
      0 < r ∧
      let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
      let W := ball (0 : ℂ) r ∩ {z | 0 < z.im}
      let F := H ∘ e.symm
      let lam := fun z => gE.inner (F z)
        (fderivWithin ℝ H K (e.symm z) 1) (fderivWithin ℝ H K (e.symm z) 1)
      MapsTo P K loopDiskSet ∧ MapsTo (S.disk.map ∘ P) K chart.source ∧
      ContDiffOn ℝ 1 H K ∧ ContDiffOn ℝ ∞ H W ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 (H z), ∀ a b : LoopAmbient,
        gE.inner y a b = g.inner (chart.symm y)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y a)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y b)) ∧
      (∀ z ∈ K, ∀ v : ℂ,
        gE.inner (H z) (fderivWithin ℝ H K z v) (fderivWithin ℝ H K z v) =
          diskConformalFactor g S.disk.map (P z) *
            ‖Complex.I * boundaryCoordinate p z‖ ^ 2 * ‖v‖ ^ 2) ∧
      (∀ z ∈ W, dbar (complexGradient H) z =
        harmonicMatrix DE H z (complexGradient H z)) ∧
      IntegrableOn (fun z => -(∑ i : Fin 2, fderiv ℝ (fun y =>
        fderiv ℝ (fun w => Real.log (lam w)) y (EuclideanSpace.basisFun (Fin 2) ℝ i))
          z (EuclideanSpace.basisFun (Fin 2) ℝ i)) / 2) (e.symm ⁻¹' W) volume := by
  obtain ⟨gE, DE, r, m, Q, hr, hmap, hsource, hH, hHi, hmetric, hnorm,
      heq, hQ, hQ1, hQne, hfactor, hDQ1, hDQI⟩ :=
    S.boundary_branch_residual hinj hsmooth hregular hx
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let p := e.symm x
  let H := (chartAt LoopAmbient (S.disk.map x)) ∘ S.disk.map ∘ e ∘ boundaryCoordinate p
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  have hconf (z : ℂ) (hz : z ∈ K) :
      let T := fderivWithin ℝ H K z
      gE.inner (H z) (T 1) (T 1) = gE.inner (H z) (T I) (T I) ∧
        gE.inner (H z) (T 1) (T I) = 0 := by
    let T := fderivWithin ℝ H K z
    have h1 := hnorm z hz 1
    have hI := hnorm z hz I
    have hsum := hnorm z hz (1 + I)
    have hs : ‖(1 : ℂ) + I‖ ^ 2 = 2 := by
      norm_num [Complex.sq_norm, Complex.normSq_apply]
    simp only [norm_one, norm_I, one_pow, mul_one] at h1 hI
    rw [hs, map_add] at hsum
    change gE.inner (H z) (T 1 + T I) (T 1 + T I) = _ at hsum
    simp only [map_add, add_apply] at hsum
    rw [gE.symm (H z) (T I) (T 1)] at hsum
    exact ⟨h1.trans hI.symm, by linarith⟩
  refine ⟨gE, DE, r, hr, hmap, hsource, hH, hHi, hmetric, hnorm, heq, ?_⟩
  exact halfDisk_logarithmicDensity_integrable DE hr m hH hHi hQ hQ1 hQne hfactor
    hconf hDQ1 hDQI

end PoincareConjecture.M65MinimalDisk
