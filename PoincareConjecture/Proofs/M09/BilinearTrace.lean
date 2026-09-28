import PoincareConjecture.Proofs.M09.TraceDerivative
import PoincareConjecture.Proofs.M09.PositiveForm
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach









set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators RealInnerProductSpace

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def formOperator : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E) :=
  ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem formOperator_pairing (B : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    ⟪formOperator B v, w⟫ = B v w :=
  InnerProductSpace.continuousLinearMapOfBilin_apply B v w

theorem continuousTrace_formOperator {K : Type*} [Fintype K]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (b : OrthonormalBasis K ℝ E) :
    continuousTrace (formOperator B) = ∑ i, B (b i) (b i) := by
  rw [continuousTrace_apply, LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm]
  exact formOperator_pairing B (b i) (b i)

theorem formOperator_isUnit_of_positive (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hG : ∀ v : E, v ≠ 0 → 0 < G v v) : IsUnit (formOperator G) := by
  obtain ⟨e, he⟩ := positiveForm_isInvertible G hG
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  change Function.Bijective (fun v ↦ (InnerProductSpace.toDual ℝ E).symm (G v))
  rw [← he]
  exact (InnerProductSpace.toDual ℝ E).symm.bijective.comp e.bijective

noncomputable def metricFormTrace (G B : E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  continuousTrace (Ring.inverse (formOperator G) * formOperator B)

theorem metricFormTrace_pullback
    {V K : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Fintype K]
    (e : E ≃L[ℝ] V) (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hG : ∀ v w : E, G v w = ⟪e v, e w⟫)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (b : OrthonormalBasis K ℝ V) :
    metricFormTrace G (B.bilinearComp e.toContinuousLinearMap e.toContinuousLinearMap) =
      ∑ i, B (b i) (b i) := by
  have hunit : IsUnit (formOperator G) := formOperator_isUnit_of_positive G (by
    intro v hv
    rw [hG]
    exact real_inner_self_pos.mpr (e.map_eq_zero_iff.not.mpr hv))
  have hcancel (z : E) : formOperator G (Ring.inverse (formOperator G) z) = z := by
    obtain ⟨a, ha⟩ := hunit
    have h : formOperator G * Ring.inverse (formOperator G) = 1 := by
      rw [← ha, Ring.inverse_unit]
      exact a.mul_inv
    exact congrArg (fun L : E →L[ℝ] E ↦ L z) h
  have hintertwine (v : E) :
      e (Ring.inverse (formOperator G)
        (formOperator (B.bilinearComp e.toContinuousLinearMap e.toContinuousLinearMap) v)) =
        formOperator B (e v) := by
    apply ext_inner_right ℝ
    intro w
    obtain ⟨z, rfl⟩ := e.surjective w
    rw [← hG, ← formOperator_pairing, hcancel, formOperator_pairing,
      ContinuousLinearMap.bilinearComp_apply, formOperator_pairing]
    rfl
  have hconj : e.toLinearEquiv.conj
      (Ring.inverse (formOperator G) *
        formOperator (B.bilinearComp e.toContinuousLinearMap e.toContinuousLinearMap)).toLinearMap =
        (formOperator B).toLinearMap := by
    ext w
    change e (Ring.inverse (formOperator G)
      (formOperator (B.bilinearComp e.toContinuousLinearMap e.toContinuousLinearMap)
        (e.symm w))) = formOperator B w
    simpa using hintertwine (e.symm w)
  unfold metricFormTrace
  rw [continuousTrace_apply, ← LinearMap.trace_conj' _ e.toLinearEquiv, hconj]
  exact continuousTrace_formOperator B b

theorem metricFormTrace_hasDerivAt
    (G B : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (G' B' : E →L[ℝ] E →L[ℝ] ℝ)
    (t : ℝ) (hG : HasDerivAt G G' t) (hB : HasDerivAt B B' t)
    (hunit : IsUnit (formOperator (G t))) (P : E →L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] ℝ)
    (hG' : ∀ v w, G' v w = G t (P v) w + G t v (P w))
    (hB' : ∀ v w, B' v w = B t (P v) w + B t v (P w) + C v w) :
    HasDerivAt (fun s ↦ metricFormTrace (G s) (B s)) (metricFormTrace (G t) C) t := by
  have hGO : HasDerivAt (fun s ↦ formOperator (G s)) (formOperator G') t := by
    simpa only [Function.comp_def] using!
      ((formOperator (E := E)).hasFDerivAt (x := G t)).comp_hasDerivAt t hG
  have hBO : HasDerivAt (fun s ↦ formOperator (B s)) (formOperator B') t := by
    simpa only [Function.comp_def] using!
      ((formOperator (E := E)).hasFDerivAt (x := B t)).comp_hasDerivAt t hB
  apply inverseMetricTrace_hasDerivAt _ _ _ _ t hGO hBO hunit P P.adjoint (formOperator C)
  · ext v
    apply ext_inner_right ℝ
    intro w
    simpa only [add_apply, mul_apply_eq_comp,
      inner_add_left, ContinuousLinearMap.adjoint_inner_left, formOperator_pairing] using hG' v w
  · ext v
    apply ext_inner_right ℝ
    intro w
    simpa only [add_apply, mul_apply_eq_comp,
      inner_add_left, ContinuousLinearMap.adjoint_inner_left, formOperator_pairing] using hB' v w

end PoincareConjecture.Proofs.M09
