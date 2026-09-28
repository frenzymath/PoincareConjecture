import PoincareConjecture.Definitions.M27KappaAlternatives
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Constants

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {t epsilon C C' : ℝ}

def M26StrongCappedTube.mono_constant
    (N : M26StrongCappedTube K t epsilon C) (hC : C ≤ C') :
    M26StrongCappedTube K t epsilon C' := {
  N with
  constant_pos := N.constant_pos.trans_le hC
  cap := N.cap.mono_constant hC
}

theorem M27CompactPositiveGeometry.mono_constant
    (N : M27CompactPositiveGeometry K C) (hpos : 0 < C) (hC : C ≤ C')
    (hscalar : ∀ x, 0 < (K.flow.connection 0).scalarCurvature x) :
    M27CompactPositiveGeometry K C' := {
  N with
  diameter_lower := fun x => lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hpos hC (by norm_num))
      (Real.rpow_nonneg (hscalar x).le _)) (N.diameter_lower x)
  diameter_upper := fun x => (N.diameter_upper x).trans_le
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (hscalar x).le _))
  volume_lower := fun x => lt_of_le_of_lt
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (inv_anti₀ hpos hC)
      (Real.rpow_nonneg (hscalar x).le _))) (N.volume_lower x)
  volume_upper := fun x => (N.volume_upper x).trans_le
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC
      (Real.rpow_nonneg (hscalar x).le _)))
  sectional_bounds := fun x y a b ha hb hab =>
    ⟨lt_of_le_of_lt (mul_le_mul_of_nonneg_right (inv_anti₀ hpos hC) (hscalar x).le)
      (N.sectional_bounds x y a b ha hb hab).1,
     (N.sectional_bounds x y a b ha hb hab).2.trans_le
       (mul_le_mul_of_nonneg_right hC (hscalar x).le)⟩
}

theorem M27ScalarDerivativeBounds.horizon_mono_constant
    (N : M27ScalarDerivativeBounds K C) (hC : C ≤ C') :
    M27ScalarDerivativeBounds K C' := by
  obtain ⟨B, hB, hBC, hbound⟩ := N
  exact ⟨B, hB, hBC.trans_le hC, hbound⟩

theorem M27KappaNine93Conclusion.mono_constant
    (N : M27KappaNine93Conclusion K epsilon C) (hpos : 0 < C) (hC : C ≤ C')
    (hscalar : ∀ x, 0 < (K.flow.connection 0).scalarCurvature x) :
    M27KappaNine93Conclusion K epsilon C' := by
  cases N with
  | round hr hq => exact .round hr hq
  | compactPositive hg => exact .compactPositive (hg.mono_constant hpos hC hscalar)
  | doubleCapped ht hp htop hcov =>
    exact .doubleCapped (ht.mono_constant hC) hp htop hcov
  | cappedEuclidean ht hp hi hcov =>
    exact .cappedEuclidean (ht.mono_constant hC) hp hi hcov
  | cappedQuotient hm ht hcov => exact .cappedQuotient hm (ht.mono_constant hC) hcov
  | sphereLine hm ht => exact .sphereLine hm ht
  | projectivePlaneLine hm => exact .projectivePlaneLine hm

theorem RepairedKappaAlternativeCertificate.mono_constant
    (N : RepairedKappaAlternativeCertificate K epsilon C) (hC : C ≤ C') :
    RepairedKappaAlternativeCertificate K epsilon C' := by
  obtain ⟨B, hB, hBC, hbound⟩ := N.derivatives
  exact {
    epsilon_pos := N.epsilon_pos
    constant_pos := N.constant_pos.trans_le hC
    alternatives := N.alternatives.mono_constant N.constant_pos hC
      (fun x => (hbound 0 le_rfl x).1)
    derivatives := N.derivatives.horizon_mono_constant hC
  }

end PoincareConjecture
