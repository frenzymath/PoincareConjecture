import PoincareConjecture.Proofs.M35.Uniqueness.Heat.EquivalentIntegralHeat
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.MixedDilation
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TimeDilationRegularity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {W V H : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

theorem contDiffAt_equivalent_weak_value
    (I : V →L[ℝ] H) (hIc : IsCompactOperator I) (hId : DenseRange I)
    (hIi : Function.Injective I) (e : W ≃L[ℝ] V)
    (hJn : ‖I.comp e.toContinuousLinearMap‖ ≤ 1)
    {T B M q C : ℝ} (hT : 0 < T) (hTB : 2 * T ≤ B)
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hC : 0 ≤ C) (he : ‖e.toContinuousLinearMap‖ ≤ M)
    (P : ℝ → V →L[ℝ] V) (hP : ContDiffOn ℝ ∞ P (Icc 0 B))
    (hPb : ∀ t ∈ Icc 0 T, ‖P 0 - P t‖ ≤ q)
    (L : ℝ → V →L[ℝ] H) (hL : ContDiffOn ℝ ∞ L (Icc 0 B))
    (hLb : ∀ t ∈ Icc 0 T, ‖L t‖ ≤ C)
    (hbase : ∀ w u : W, inner ℝ w u =
      inner ℝ (I (e w)) (I (e u)) + inner ℝ (e w) (P 0 (e u)))
    (hsmall : (T + 1) * (M * (q * M)) +
      (Real.sqrt T * (Real.sqrt T + 1)) * (C * M) < 1)
    {v : ℝ → V} (hv : MemLp v 2 (timeMeasure B)) {U : ℝ → H}
    (hUc : ContinuousOn U (Icc 0 B)) (hgraph : ∀ᵐ t ∂timeMeasure B, I (v t) = U t)
    (heq : ∀ t ∈ Icc 0 B, ∀ w : V,
      inner ℝ (I w) (U t) = inner ℝ (I w) (U 0) +
        ∫ s in (0 : ℝ)..t, inner ℝ (I w) (L s (v s)) - inner ℝ w (P s (v s)))
    {t : ℝ} (ht : t ∈ Ioc 0 T) : ContDiffAt ℝ ∞ U t := by
  let E := e.toContinuousLinearMap
  let J : W →L[ℝ] H := I.comp E
  let R : ℝ → W →L[ℝ] W := fun s => E.adjoint.comp ((P 0 - P s).comp E)
  let LW : ℝ → W →L[ℝ] H := fun s => (L s).comp E
  let A := equivalentHeatGenerator I e P L
  have hB : 0 < B := (mul_pos (by norm_num) hT).trans_le hTB
  have hsub : Icc (0 : ℝ) T ⊆ Icc 0 B :=
    Icc_subset_Icc le_rfl (by linarith only [hT, hTB])
  have hJc : IsCompactOperator J := hIc.comp_clm E
  have hJd : DenseRange J := hId.comp e.surjective.denseRange I.continuous
  have hJi : Function.Injective J := hIi.comp e.injective
  have hAc : ContDiffOn ℝ ∞ A (Icc 0 B) := contDiffOn_equivalentHeatGenerator I e P L hP hL
  have hRc : ContinuousOn R (Icc 0 T) :=
    continuousOn_const.clm_comp
      ((continuousOn_const.sub (hP.continuousOn.mono hsub)).clm_comp continuousOn_const)
  have hLc : ContinuousOn LW (Icc 0 T) :=
    (hL.continuousOn.mono hsub).clm_comp continuousOn_const
  let : SecondCountableTopologyEither ℝ (W →L[ℝ] W) := ⟨Or.inl inferInstance⟩
  let : SecondCountableTopologyEither ℝ (W →L[ℝ] H) := ⟨Or.inl inferInstance⟩
  have hRm : AEStronglyMeasurable R (timeMeasure T) :=
    (hRc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hLm : AEStronglyMeasurable LW (timeMeasure T) :=
    (hLc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hRa : ∀ᵐ s ∂timeMeasure T, ‖R s‖ ≤ M * (q * M) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    calc
      ‖R s‖ ≤ ‖E.adjoint‖ * ‖(P 0 - P s).comp E‖ := E.adjoint.opNorm_comp_le _
      _ ≤ M * (q * M) := mul_le_mul
        (by simpa only [LinearIsometryEquiv.norm_map] using he)
        (((P 0 - P s).opNorm_comp_le E).trans
          (mul_le_mul (hPb s (Ioc_subset_Icc_self hs)) he (norm_nonneg _) hq))
        (norm_nonneg _) hM
  have hLa : ∀ᵐ s ∂timeMeasure T, ‖LW s‖ ≤ C * M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact ((L s).opNorm_comp_le E).trans
      (mul_le_mul (hLb s (Ioc_subset_Icc_self hs)) he (norm_nonneg _) hC)
  have hsmall' := norm_normalizedDilationLp_response_lt_one J hJc hJd hJi hJn
    (a := 1 / 2) (b := 2) (by norm_num) (by norm_num) hT.le hTB hB
    (by norm_num) (by positivity) (by positivity) A hAc R hRm hRa LW hLm hLa
    (fun s _ => equivalentHeatGenerator_normalized I e P L hbase s) hsmall
  have hgraph' : ∀ᵐ s ∂timeMeasure B, J (e.symm (v s)) = U s := by
    filter_upwards [hgraph] with s hs
    simpa only [J, E, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, e.apply_symm_apply] using hs
  exact contDiffAt_weak_value_of_dilation J hJc hJd hJi hJn
    (a := 1 / 2) (b := 2) (by norm_num) (by norm_num) (by norm_num) hT hTB hB A hAc
    hsmall' (fun s => e.symm (v s)) (e.symm.toContinuousLinearMap.comp_memLp' hv) U hUc
    hgraph' (equivalent_tested_integral_adjoint I e P L hP.continuousOn hL.continuousOn hv heq) ht

end PoincareConjecture.M35.Uniqueness.Heat
