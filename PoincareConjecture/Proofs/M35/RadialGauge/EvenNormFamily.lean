import PoincareConjecture.Proofs.M35.RadialGauge.AxisDivisionFamily

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

open SmoothRadial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private noncomputable def evenProfileDerivative (f : ℝ → ℝ → ℝ) (p : ℝ × E) :
    (ℝ × E) →L[ℝ] ℝ :=
  (ContinuousLinearMap.toSpanSingleton ℝ (profileTimePartial f p.1 ‖p.2‖)).coprod
    (axisDivision (profileRadiusPartial f p.1) ‖p.2‖ • innerSL ℝ p.2)

private theorem evenNormFamily_hasFDerivAt
    {f : ℝ → ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (J ×ˢ univ))
    (he : ∀ t ∈ J, Function.Even (f t))
    {p : ℝ × E} (hp : p.1 ∈ J) :
    HasFDerivAt (fun q : ℝ × E => f q.1 ‖q.2‖) (evenProfileDerivative f p) p := by
  let timeMap : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hW : IsOpen (J ×ˢ (univ : Set E)) := hJ.prod isOpen_univ
  have hnorm : ContinuousOn (fun q : ℝ × E => (q.1, ‖q.2‖)) (J ×ˢ univ) :=
    (continuous_fst.prodMk continuous_snd.norm).continuousOn
  have hmaps : MapsTo (fun q : ℝ × E => (q.1, ‖q.2‖)) (J ×ˢ univ) (J ×ˢ univ) :=
    fun _ hq => ⟨hq.1, mem_univ _⟩
  have htc : ContinuousOn (fun q : ℝ × E => timeMap (profileTimePartial f q.1 ‖q.2‖))
      (J ×ˢ univ) := timeMap.continuous.comp_continuousOn
        ((profileTimePartial_contDiffOn hJ hf).continuousOn.comp hnorm hmaps)
  have hqcProfile : ContinuousOn
      (fun q : ℝ × ℝ => axisDivision (profileRadiusPartial f q.1) q.2) (J ×ˢ univ) :=
    (axisDivision_family_contDiffOn hJ (profileRadiusPartial_contDiffOn hJ hf)).continuousOn
  have hqc : ContinuousOn
      (fun q : ℝ × E => axisDivision (profileRadiusPartial f q.1) ‖q.2‖ • innerSL ℝ q.2)
      (J ×ˢ univ) :=
    (hqcProfile.comp hnorm hmaps).smul
      ((innerSL ℝ).continuous.comp continuous_snd).continuousOn
  exact (hasStrictFDerivAt_uncurry_coprod
    (f := fun (t : ℝ) (x : E) => f t ‖x‖)
    (f₁ := fun t x => timeMap (profileTimePartial f t ‖x‖))
    (f₂ := fun t x => axisDivision (profileRadiusPartial f t) ‖x‖ • innerSL ℝ x)
    (by
      filter_upwards [hW.mem_nhds ⟨hp, mem_univ _⟩] with q hq
      exact (profileFamily_hasDerivAt_time hJ hf hq.1 ‖q.2‖).hasFDerivAt)
    (by
      filter_upwards [hW.mem_nhds ⟨hp, mem_univ _⟩] with q hq
      change HasFDerivAt (fun x : E => f q.1 ‖x‖)
        (axisDivision (profileRadiusPartial f q.1) ‖q.2‖ • innerSL ℝ q.2) q.2
      rw [profileRadiusPartial_eq_deriv hJ hf hq.1]
      exact hasFDerivAt_even_norm (profileFamily_slice_contDiff hf hq.1) (he q.1 hq.1) q.2)
    (htc.continuousAt (hW.mem_nhds ⟨hp, mem_univ _⟩))
    (hqc.continuousAt (hW.mem_nhds ⟨hp, mem_univ _⟩))).hasFDerivAt

theorem evenNorm_family_contDiffOn
    {f : ℝ → ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (J ×ˢ univ))
    (he : ∀ t ∈ J, Function.Even (f t)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => f p.1 ‖p.2‖) (J ×ˢ univ) := by
  have hfinite : ∀ k : ℕ, ∀ f : ℝ → ℝ → ℝ,
      ContDiffOn ℝ ∞ (Function.uncurry f) (J ×ˢ univ) →
      (∀ t ∈ J, Function.Even (f t)) →
      ContDiffOn ℝ k (fun p : ℝ × E => f p.1 ‖p.2‖) (J ×ˢ univ) := by
    intro k
    induction k with
    | zero =>
      intro f hf _
      apply contDiffOn_zero.mpr
      exact hf.continuousOn.comp (continuous_fst.prodMk continuous_snd.norm).continuousOn
        (fun _ hp => ⟨hp.1, mem_univ _⟩)
    | succ k ih =>
      intro f hf he
      have ht := ih (profileTimePartial f) (profileTimePartial_contDiffOn hJ hf)
        (fun t ht => profileTimePartial_even hJ hf he ht)
      have hq := ih (fun t => axisDivision (profileRadiusPartial f t))
        (axisDivision_family_contDiffOn hJ (profileRadiusPartial_contDiffOn hJ hf))
        (fun t ht => by
          rw [profileRadiusPartial_eq_deriv hJ hf ht]
          exact axisDivision_deriv_even (profileFamily_slice_contDiff hf ht) (he t ht))
      let timeMap : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ) :=
        (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap
      have hdt : ContDiffOn ℝ k
          (fun p : ℝ × E => timeMap (profileTimePartial f p.1 ‖p.2‖)) (J ×ˢ univ) :=
        timeMap.contDiff.comp_contDiffOn ht
      have hdq : ContDiffOn ℝ k
          (fun p : ℝ × E => axisDivision (profileRadiusPartial f p.1) ‖p.2‖ • innerSL ℝ p.2)
          (J ×ˢ univ) := hq.smul ((innerSL ℝ).contDiff.comp_contDiffOn contDiffOn_snd)
      have hD : ContDiffOn ℝ k (evenProfileDerivative (E := E) f)
          (J ×ˢ (univ : Set E)) := by
        have h := (hdt.clm_comp (contDiffOn_const (c := ContinuousLinearMap.fst ℝ ℝ E))).add
          (hdq.clm_comp (contDiffOn_const (c := ContinuousLinearMap.snd ℝ ℝ E)))
        exact h.congr (fun _ _ =>
          (ContinuousLinearMap.comp_fst_add_comp_snd _ _).symm)
      rw [Nat.cast_add, Nat.cast_one]
      apply (contDiffOn_succ_iff_fderiv_of_isOpen (hJ.prod isOpen_univ)).mpr
      refine ⟨fun p hp =>
        (evenNormFamily_hasFDerivAt hJ hf he hp.1).differentiableAt.differentiableWithinAt,
        by simp, ?_⟩
      exact hD.congr (fun p hp => (evenNormFamily_hasFDerivAt hJ hf he hp.1).fderiv)
  exact contDiffOn_infty.mpr (fun k => hfinite k f hf he)

end PoincareConjecture.M35.RadialGauge
