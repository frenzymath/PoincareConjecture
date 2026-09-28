import PoincareConjecture.Proofs.M03.Existence.HilbertEigenbasisNative
import PoincareConjecture.Proofs.M03.Existence.SpectralL2ResponseNative









set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace PoincareConjecture.HilbertResolventNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]


def InGeneratorGraph (J : V →L[ℝ] H) (u a : H) : Prop := operator J (u + a) = u

theorem inGeneratorGraph_iff_variational (J : V →L[ℝ] H) (u a : H) :
    InGeneratorGraph J u a ↔
      ∃ v : V, J v = u ∧ ∀ w : V, inner ℝ w v = inner ℝ (J w) (u + a) := by
  constructor
  · intro h
    exact ⟨solution J (u + a), h, solution_pairing J (u + a)⟩
  · rintro ⟨v, hv, hpair⟩
    have heq := solution_unique J (u + a) v hpair
    change J (solution J (u + a)) = u
    rw [← heq, hv]

theorem inGeneratorGraph_unique (J : V →L[ℝ] H) (hd : DenseRange J)
    {u a b : H} (ha : InGeneratorGraph J u a) (hb : InGeneratorGraph J u b) : a = b := by
  exact add_left_cancel (operator_injective J hd (ha.trans hb.symm))

theorem inGeneratorGraph_iff_coeff (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hnorm : ‖J‖ ≤ 1) (u a : H) :
    InGeneratorGraph J u a ↔ ∀ i : EigenIndex J,
      (eigenbasis J hc hd).repr a i =
        (generatorParameters J hc hd hnorm i : ℝ) * (eigenbasis J hc hd).repr u i := by
  constructor
  · intro h i
    have hi := congrArg (fun x : H => (eigenbasis J hc hd).repr x i) h
    rw [repr_operator] at hi
    simp only [map_add, lp.coeFn_add, Pi.add_apply, generatorParameters_coe] at hi ⊢
    have hmu := i.1.property
    field_simp
    nlinarith [hi]
  · intro h
    apply (eigenbasis J hc hd).repr.injective
    apply lp.ext
    funext i
    rw [repr_operator]
    simp only [map_add, lp.coeFn_add, Pi.add_apply, h i, generatorParameters_coe]
    have hmu := i.1.property
    field_simp
    <;> ring

theorem inGeneratorGraph_nonneg (J : V →L[ℝ] H) (hnorm : ‖J‖ ≤ 1)
    {u a : H} (h : InGeneratorGraph J u a) : 0 ≤ inner ℝ u a := by
  obtain ⟨v, hv, hpair⟩ := (inGeneratorGraph_iff_variational J u a).mp h
  have hp := hpair v
  rw [hv, inner_add_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at hp
  have hbound : ‖u‖ ≤ ‖v‖ := by
    rw [← hv]
    calc
      ‖J v‖ ≤ ‖J‖ * ‖v‖ := J.le_opNorm v
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg v)
      _ = ‖v‖ := one_mul _
  have hs := (sq_le_sq₀ (norm_nonneg u) (norm_nonneg v)).mpr hbound
  linarith

open SpectralHeatNative (State timeMeasure)


theorem exists_response [SeparableSpace H]
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J) (hnorm : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) {F : ℝ → H} (hF : MemLp F 2 (timeMeasure T)) :
    ∃ U D G : ℝ → H,
      U 0 = 0 ∧ ContinuousOn U (Icc (0 : ℝ) T) ∧
      MemLp D 2 (timeMeasure T) ∧ MemLp G 2 (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T, HasDerivAt U (D t) t) ∧
      (∀ᵐ t ∂timeMeasure T, D t + G t = F t) ∧
      (∀ᵐ t ∂timeMeasure T, InGeneratorGraph J (U t) (G t)) ∧
      (∫ t, ‖D t‖ ^ 2 ∂timeMeasure T) + (∫ t, ‖G t‖ ^ 2 ∂timeMeasure T) ≤
        ∫ t, ‖F t‖ ^ 2 ∂timeMeasure T := by
  haveI : Countable (EigenIndex J) := eigenIndex_countable J hc
  let B := (eigenbasis J hc hd).repr
  let L : H →L[ℝ] State (EigenIndex J) := B.toContinuousLinearEquiv.toContinuousLinearMap
  let Q : State (EigenIndex J) →L[ℝ] H := B.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let lambda := generatorParameters J hc hd hnorm
  have hBF : MemLp (fun t => B (F t)) 2 (timeMeasure T) := L.comp_memLp' hF
  obtain ⟨U, D, G, hzero, hcont, hD, hG, hderiv, heq, hcoeff, henergy⟩ :=
    SpectralHeatNative.exists_spectralHeat_response_of_memLp hT lambda hBF
  refine ⟨fun t => B.symm (U t), fun t => B.symm (D t), fun t => B.symm (G t),
    ?_, ?_, Q.comp_memLp' hD, Q.comp_memLp' hG, ?_, ?_, ?_, ?_⟩
  · change B.symm (U 0) = 0
    rw [hzero, map_zero]
  · exact B.symm.continuous.comp_continuousOn hcont
  · filter_upwards [hderiv] with t ht
    exact Q.hasFDerivAt.comp_hasDerivAt t ht
  · filter_upwards [heq] with t ht
    rw [← map_add, ht, B.symm_apply_apply]
  · filter_upwards [hcoeff] with t ht
    apply (inGeneratorGraph_iff_coeff J hc hd hnorm _ _).mpr
    intro i
    change B (B.symm (G t)) i = (lambda i : ℝ) * B (B.symm (U t)) i
    simp only [B.apply_symm_apply]
    exact ht i
  · simpa only [B.symm.norm_map, B.norm_map] using henergy

end PoincareConjecture.HilbertResolventNative
