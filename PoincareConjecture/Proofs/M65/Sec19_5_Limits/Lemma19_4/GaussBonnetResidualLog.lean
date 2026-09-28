import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryLog











set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

open M65Gauss






theorem residual_logarithmicDensity_integrable {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {Q : ℂ → Fin n → ℂ}
    {K U : Set ℂ} (hK : IsCompact K) (hKU : UniqueDiffOn ℝ K)
    (hU : IsOpen U) (hUK : U ⊆ K) (hclosure : K ⊆ closure U)
    (hH : ContDiffOn ℝ ∞ H K) (hQ : ContDiffOn ℝ 1 Q K)
    (hQne : ∀ z ∈ K, Q z ≠ 0)
    (hfactor : ∀ z ∈ U, ∃ s : ℂ, s ≠ 0 ∧ complexGradient H z = s • Q z)
    (hconf : ∀ z ∈ K,
      let T := fderivWithin ℝ H K z
      g.inner (H z) (T 1) (T 1) = g.inner (H z) (T I) (T I) ∧
        g.inner (H z) (T 1) (T I) = 0) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let F := H ∘ e.symm
    let lam := fun z => g.inner (F z)
      (fderivWithin ℝ H K (e.symm z) 1) (fderivWithin ℝ H K (e.symm z) 1)
    IntegrableOn (fun z => -(∑ i : Fin 2, fderiv ℝ (fun y =>
      fderiv ℝ (fun w => Real.log (lam w)) y (EuclideanSpace.basisFun (Fin 2) ℝ i))
        z (EuclideanSpace.basisFun (Fin 2) ℝ i)) / 2) (e.symm ⁻¹' U) volume := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let Kp := e.symm ⁻¹' K
  let Up := e.symm ⁻¹' U
  let F := H ∘ e.symm
  let G := fun z => g.euclideanCoefficients (H z)
  let PC := fun z => twoPlaneProjection (G z)
    (residualRealColumn (Q z)) (residualImagColumn (Q z))
  let P := PC ∘ e.symm
  let lam := fun z => G (e.symm z)
    (fderivWithin ℝ H K (e.symm z) 1) (fderivWithin ℝ H K (e.symm z) 1)
  have hG : ContDiffOn ℝ 1 G K :=
    ((contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).of_le
      (by simp)).comp_contDiffOn (hH.of_le (by simp))
  have hnhds (z : ℂ) (hz : z ∈ U) : K ∈ 𝓝 z :=
    mem_of_superset (hU.mem_nhds hz) hUK
  have hconfU (z : ℂ) (hz : z ∈ U) :
      G z (fderiv ℝ H z 1) (fderiv ℝ H z I) = 0 ∧
        G z (fderiv ℝ H z I) (fderiv ℝ H z I) = G z (fderiv ℝ H z 1) (fderiv ℝ H z 1) := by
    have hh := hconf z (hUK hz)
    dsimp only at hh
    rw [fderivWithin_of_mem_nhds (hnhds z hz)] at hh
    exact ⟨hh.2, hh.1.symm⟩
  have hpart (v : ℂ) : ContinuousOn PC K ∧
      (∀ z ∈ U, PC z = twoPlaneProjection (G z) (fderiv ℝ H z 1) (fderiv ℝ H z I)) ∧
      MemLp (fun z => fderiv ℝ PC z v) 2 (volume.restrict U) := by
    have hh := residual_projection_extension_memLp hK hU hUK hclosure hG.continuousOn
      (hG.mono hUK) (fun z _ v w => g.symm (H z) v w)
      (fun z _ v hv => g.pos (H z) v hv) hQ.continuousOn (hQ.mono hUK) hQne
      hfactor hconfU v (compact_within_derivative_memLp hK hKU hU hUK hG v)
      (compact_within_derivative_memLp hK hKU hU hUK hQ v)
    change ContinuousOn PC K ∧
      (∀ z ∈ U, PC z = twoPlaneProjection (G z) (fderiv ℝ H z 1) (fderiv ℝ H z I)) ∧
      MemLp (fun z => fderiv ℝ PC z v) 2 (volume.restrict (K ∩ U)) at hh
    rwa [inter_eq_right.mpr hUK] at hh
  have hpos (z : ℂ) (hz : z ∈ U) : 0 < G z (fderiv ℝ H z 1) (fderiv ℝ H z 1) := by
    obtain ⟨s, hs, hf⟩ := hfactor z hz
    have hne : complexGradient H z ≠ 0 := by
      rw [hf]
      exact smul_ne_zero hs (hQne z (hUK hz))
    obtain ⟨ha, hb⟩ := residual_columns_complexGradient H z
    have hh := residual_columns_factor_pos (G z) (fun v hv => g.pos (H z) v hv) hne
      (by simpa only [ha, hb] using (hconfU z hz).2)
    simpa only [ha] using hh
  have hKp : IsCompact Kp := e.symm.toHomeomorph.isCompact_preimage.mpr hK
  have hUp : IsOpen Up := hU.preimage e.symm.continuous
  have hUpKp : Up ⊆ Kp := preimage_mono hUK
  have hFs : ContDiffOn ℝ ∞ F Up :=
    (hH.mono hUK).comp e.symm.contDiff.contDiffOn (fun _ hz => hz)
  have hFc : ContinuousOn F Kp :=
    hH.continuousOn.comp e.symm.continuous.continuousOn (fun _ hz => hz)
  have hDc : ContinuousOn (fun z => fderivWithin ℝ H K z 1) K :=
    (hH.continuousOn_fderivWithin hKU (by simp)).clm_apply continuousOn_const
  have hlam : ContinuousOn lam Kp :=
    ((hG.continuousOn.clm_apply hDc).clm_apply hDc).comp e.symm.continuous.continuousOn
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
  have hlamEq (z : LoopPlane) (hz : z ∈ Up) :
      lam z = G (e.symm z) (fderiv ℝ H (e.symm z) 1) (fderiv ℝ H (e.symm z) 1) := by
    dsimp only [lam]
    rw [fderivWithin_of_mem_nhds (hnhds (e.symm z) hz)]
  have hGs : ContDiffOn ℝ ∞ (fun z => g.euclideanCoefficients (F z)) Up :=
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).comp_contDiffOn hFs
  have hDs : ContDiffOn ℝ ∞ (fun z => fderiv ℝ F z (b 0)) Up :=
    (hFs.fderiv_of_isOpen (m := ∞) hUp (by simp)).clm_apply contDiffOn_const
  have hlams : ContDiffOn ℝ ∞ lam Up := by
    apply ((hGs.clm_apply hDs).clm_apply hDs).congr
    intro z hz
    rw [hlamEq z hz, hF0]
    rfl
  have hGram (z : LoopPlane) (hz : z ∈ Up) :
      0 < lam z ∧ m60AreaGram g F z = lam z • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    have hc := hconfU (e.symm z) hz
    refine ⟨by rw [hlamEq z hz]; exact hpos (e.symm z) hz, ?_⟩
    have hpair (a d : Fin 2) :
        g.euclideanCoefficients (F z) (fderiv ℝ F z (b a)) (fderiv ℝ F z (b d)) =
          if a = d then lam z else 0 := by
      fin_cases a <;> fin_cases d
      · change G (e.symm z) (fderiv ℝ F z (b 0)) (fderiv ℝ F z (b 0)) = lam z
        rw [hF0, hlamEq z hz]
      · change G (e.symm z) (fderiv ℝ F z (b 0)) (fderiv ℝ F z (b 1)) = 0
        rw [hF0, hF1]
        exact hc.1
      · change G (e.symm z) (fderiv ℝ F z (b 1)) (fderiv ℝ F z (b 0)) = 0
        rw [hF1, hF0]
        exact (g.symm _ _ _).trans hc.1
      · change G (e.symm z) (fderiv ℝ F z (b 1)) (fderiv ℝ F z (b 1)) = lam z
        rw [hF1, hlamEq z hz]
        exact hc.2
    ext a d
    simpa +instances only [m60AreaGram, mfderiv_eq_fderiv, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, b] using! hpair a d
  have hP : ContinuousOn P Kp :=
    (hpart 1).1.comp e.symm.continuous.continuousOn (fun _ hz => hz)
  have hPeq (z : LoopPlane) (hz : z ∈ Up) : P z = conformalTangentProjection g F z := by
    change PC (e.symm z) = twoPlaneProjection (g.euclideanCoefficients (F z))
      (fderiv ℝ F z (b 0)) (fderiv ℝ F z (b 1))
    rw [hF0, hF1]
    exact (hpart 1).2.1 (e.symm z) hz
  have hDP (i : Fin 2) : MemLp (fun z => fderiv ℝ P z (b i))
      2 (volume.restrict (Kp ∩ Up)) := by
    rw [inter_eq_right.mpr hUpKp]
    have heμ := orthonormalBasisOneI.measurePreserving_repr_symm.restrict_preimage_emb
      e.symm.toHomeomorph.measurableEmbedding U
    have hraw := (hpart (e.symm (b i))).2.2.comp_measurePreserving heμ
    apply hraw.ae_eq
    filter_upwards with z
    rw [e.symm.comp_right_fderiv]
    rfl
  have hN (i j : Fin 2) :=
    normalHessian_density_integrableOn D hKp hUp hFc hFs hlam hGram hP hPeq i j (hDP i)
  have hh := logarithmicDensity_integrableOn D hKp hUp hFc hFs hlam hlams hGram hN
  rwa [inter_eq_right.mpr hUpKp] at hh

end PoincareConjecture.M65Branch
