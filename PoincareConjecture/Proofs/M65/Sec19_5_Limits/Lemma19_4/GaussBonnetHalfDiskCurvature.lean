import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetHalfDiskProjection
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetNormalDensity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

open M65StrictTrace M65Gauss





theorem halfDisk_normalHessian_integrable {n : ℕ} [Nonempty (Fin n)]
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
      2 (volume.restrict (ball (0 : ℂ) r ∩ {z | 0 < z.im}))) (i j : Fin 2) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
    let W := ball (0 : ℂ) r ∩ {z | 0 < z.im}
    let F := H ∘ e.symm
    let lam := fun z => g.inner (F z)
      (fderivWithin ℝ H K (e.symm z) 1) (fderivWithin ℝ H K (e.symm z) 1)
    IntegrableOn (fun z =>
      let B := normalHessian D F z (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ j)
      g.inner (F z) B B / lam z) (e.symm ⁻¹' W) volume := by
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
  let PC := fun z => twoPlaneProjection (g.euclideanCoefficients (H z))
    (residualRealColumn (Q z)) (residualImagColumn (Q z))
  let P := PC ∘ e.symm
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
  have hlamC : ContinuousOn lamC K := (hGc.clm_apply hDc).clm_apply hDc
  have hlam : ContinuousOn lam Kp :=
    hlamC.comp e.symm.continuous.continuousOn (fun _ hz => hz)
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
  obtain ⟨hPC, hPCeq, hpos, hP1, hPI⟩ :=
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
  have hP : ContinuousOn P Kp :=
    hPC.comp e.symm.continuous.continuousOn (fun _ hz => hz)
  have hPeq (z : LoopPlane) (hz : z ∈ Wp) : P z = conformalTangentProjection g F z := by
    change PC (e.symm z) = twoPlaneProjection (g.euclideanCoefficients (F z))
      (fderiv ℝ F z (b 0)) (fderiv ℝ F z (b 1))
    rw [hF0, hF1]
    exact hPCeq (e.symm z) hz
  have hDP (a : Fin 2) : MemLp (fun z => fderiv ℝ P z (b a))
      2 (volume.restrict (Kp ∩ Wp)) := by
    rw [inter_eq_right.mpr hWpKp]
    have heμ := orthonormalBasisOneI.measurePreserving_repr_symm.restrict_preimage_emb
      e.symm.toHomeomorph.measurableEmbedding W
    have hraw : MemLp (fun z => fderiv ℝ PC (e.symm z) (e.symm (b a)))
        2 (volume.restrict Wp) := by
      fin_cases a
      · change MemLp (fun z => fderiv ℝ PC (e.symm z) (e.symm (b 0)))
          2 (volume.restrict Wp)
        rw [he0]
        exact hP1.comp_measurePreserving heμ
      · change MemLp (fun z => fderiv ℝ PC (e.symm z) (e.symm (b 1)))
          2 (volume.restrict Wp)
        rw [heI]
        exact hPI.comp_measurePreserving heμ
    apply hraw.ae_eq
    filter_upwards with z
    rw [e.symm.comp_right_fderiv]
    rfl
  have hh := normalHessian_density_integrableOn D hKp hWp hFc hFs hlam hGram
    hP hPeq i j (hDP i)
  rw [inter_eq_right.mpr hWpKp] at hh
  exact hh

end PoincareConjecture.M65Branch
