
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.RegionTopology
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.OperatorReaction.Logarithmic
import PoincareConjecture.Proofs.M05.Geometry.Curvature.Operator.Reaction












namespace Poincare.HamiltonIvey

open Set
open scoped BigOperators ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem toMatrix_endomorphismReaction_eq_curvatureReaction
    (e : OrthonormalBasis (Fin 3) ℝ E) (A : E →ₗ[ℝ] E) :
    LinearMap.toMatrix e.toBasis e.toBasis (endomorphismReaction A) =
      Poincare.Geometry.Curvature.Operator.curvatureReaction
        (LinearMap.toMatrix e.toBasis e.toBasis A) := by
  rw [toMatrix_endomorphismReaction]
  simp [operatorReaction, Geometry.Curvature.Operator.curvatureReaction,
    ← Nat.cast_smul_eq_nsmul ℝ]

theorem endomorphismReaction_smul (c : ℝ) (A : E →ₗ[ℝ] E) :
    endomorphismReaction (c • A) = c ^ 2 • endomorphismReaction A := by
  simp only [endomorphismReaction, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_mul_assoc, mul_smul_comm, smul_smul,
    map_smul, smul_eq_mul, smul_add, smul_sub]
  congr 2 <;> ring_nf

private theorem hasDerivAt_unscaled_operator
    {A : ℝ → E →ₗ[ℝ] E} {t : ℝ} (ht : 0 ≤ t)
    (hderiv : ∀ v : E, HasDerivAt (fun s => A s v)
      ((1 + t)⁻¹ • (A t v + endomorphismReaction (A t) v)) t) :
    ∀ v : E, HasDerivAt (fun s => ((1 + s)⁻¹ • A s) v)
      (endomorphismReaction ((1 + t)⁻¹ • A t) v) t := by
  intro v
  have hc : 1 + t ≠ 0 := by linarith
  have hinv := ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).inv hc
  have hd := hinv.smul (hderiv v)
  convert hd using 1
  · rfl
  · dsimp
    simp only [endomorphismReaction_smul, LinearMap.smul_apply,
      smul_add, smul_smul, zero_add, neg_div, one_div, ← inv_pow]
    module

theorem scaled_operator_reaction_invariance
    (hn : Module.finrank ℝ E = 3) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {A : ℝ → E →ₗ[ℝ] E}
    (hcont : ∀ v : E, ContinuousOn (fun t => A t v) (Set.Icc a b))
    (hsymm : ∀ t ∈ Set.Icc a b, (A t).IsSymmetric)
    (hderiv : ∀ t ∈ Set.Ioo a b, ∀ v : E,
      HasDerivAt (fun s => A s v)
        ((1 + t)⁻¹ • (A t v + endomorphismReaction (A t) v)) t)
    (hinit : A a ∈ region hn 0) :
    ∀ t ∈ Set.Icc a b, A t ∈ region hn 0 := by
  let B : ℝ → E →ₗ[ℝ] E := fun t => (1 + t)⁻¹ • A t
  have hc : ∀ t ∈ Icc a b, 1 + t ≠ 0 := by
    intro t ht
    linarith [ht.1]
  have hrecover : ∀ t ∈ Icc a b, (1 + t) • B t = A t := by
    intro t ht
    simp only [B, smul_smul, mul_inv_cancel₀ (hc t ht), one_smul]
  have hBc : ∀ v : E, ContinuousOn (fun t => B t v) (Icc a b) := by
    intro v
    exact ((continuousOn_const.add continuousOn_id).inv₀ hc).smul (hcont v)
  have hBs : ∀ t ∈ Icc a b, (B t).IsSymmetric := fun t ht =>
    (hsymm t ht).smul (by simp)
  have hBd : ∀ t ∈ Ioo a b, ∀ v : E,
      HasDerivAt (fun s => B s v) (endomorphismReaction (B t) v) t := by
    intro t ht
    exact hasDerivAt_unscaled_operator (ha.trans ht.1.le) (hderiv t ht)
  have hBi : B a ∈ region hn a := by
    apply (region_scale_iff hn ha (B a)).mpr
    rwa [hrecover a ⟨le_rfl, hab⟩]
  have hpres := operator_reaction_invariance hn ha hab hBc hBs hBd hBi
  intro t ht
  have h := (region_scale_iff hn (ha.trans ht.1) (B t)).mp (hpres t ht)
  rwa [hrecover t ht] at h

theorem logarithmic_pinching_of_mem_region
    (hn : Module.finrank ℝ E = 3) {t : ℝ} (ht : 0 ≤ t)
    {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric) (hmem : A ∈ region hn t) :
    let X := max (-(hA.eigenvalues hn 2)) 0
    0 < X → 2 * X * (Real.log X + Real.log (1 + t) - 3) ≤
      2 * LinearMap.trace ℝ E A := by
  intro X hX
  obtain ⟨_, hmem⟩ := hmem
  have htrace := hA.trace_eq_sum_eigenvalues hn
  simp only [Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    RCLike.ofReal_real_eq_id, id_eq] at htrace
  have h := PoincareConjecture.logarithmic_pinching_of_scalar_region ht
    (hA.eigenvalues_antitone hn (by decide : (0 : Fin 3) ≤ 1))
    (hA.eigenvalues_antitone hn (by decide : (1 : Fin 3) ≤ 2))
    (by simpa only [htrace, add_assoc] using hmem) hX
  simpa only [X, htrace, add_assoc] using h

theorem scaled_continuous_operator_reaction_invariance
    (hn : Module.finrank ℝ E = 3) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {A : ℝ → E →L[ℝ] E}
    (hcont : ContinuousOn A (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, (A t).toLinearMap.IsSymmetric)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt A
      ((1 + t)⁻¹ • (A t + (endomorphismReaction (A t).toLinearMap).toContinuousLinearMap)) t)
    (hinit : A a ∈ continuousRegion hn 0) :
    ∀ t ∈ Icc a b, A t ∈ continuousRegion hn 0 := by
  apply scaled_operator_reaction_invariance hn ha hab (A := fun t => (A t).toLinearMap)
    (fun v => (ContinuousLinearMap.apply ℝ E v).continuous.comp_continuousOn hcont)
    hsymm _ hinit
  intro t ht v
  simpa using (hderiv t ht).clm_apply (hasDerivAt_const t v)

theorem contDiff_continuousEndomorphismReaction :
    ContDiff ℝ ∞ (fun A : E →L[ℝ] E =>
      (endomorphismReaction A.toLinearMap).toContinuousLinearMap) := by
  let tr : (E →L[ℝ] E) →L[ℝ] ℝ :=
    ((LinearMap.trace ℝ E).comp
      (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E)).symm.toLinearMap
      ).toContinuousLinearMap
  have htr : ContDiff ℝ ∞ tr := tr.contDiff
  have hsq : ContDiff ℝ ∞ (fun A : E →L[ℝ] E => A * A) := contDiff_id.mul contDiff_id
  convert ((hsq.const_smul (4 : ℝ)).sub
    (((contDiff_const (c := (2 : ℝ))).mul htr).smul contDiff_id)).add
    ((htr.pow 2 |>.sub (htr.comp hsq)).smul
      (contDiff_const (c := (1 : E →L[ℝ] E)))) using 1
  ext A v
  simp [endomorphismReaction, tr, ← Nat.cast_smul_eq_nsmul ℝ]

end Poincare.HamiltonIvey
