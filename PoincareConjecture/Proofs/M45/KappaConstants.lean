import PoincareConjecture.Definitions.M27KappaAlternatives

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {t : ℝ} {x : M} {epsilon C C' : ℝ}

def M27CanonicalCap.mono_constant
    (N : M27CanonicalCap K t x epsilon C) (hCC' : C ≤ C') :
    M27CanonicalCap K t x epsilon C' :=
  { N with constant_le := N.constant_le.trans hCC' }

theorem M27CanonicalComponent.mono_constant
    (N : M27CanonicalComponent K t C) (hCC' : C ≤ C') :
    M27CanonicalComponent K t C' := by
  have hC' : 0 < C' := N.constant_pos.trans_le hCC'
  have hinv : C'⁻¹ ≤ C⁻¹ := (inv_le_inv₀ hC' N.constant_pos).2 hCC'
  have hdiam : 0 ≤ metricDiameter (K.flow.metric t) Set.univ := by
    unfold metricDiameter
    apply Real.sSup_nonneg
    rintro y ⟨p, rfl⟩
    exact ENNReal.toReal_nonneg
  have hinf : 0 < sInf (Set.range (fun y : M =>
      (K.flow.connection t).scalarCurvature y ^ (-1 / 2 : ℝ))) :=
    pos_of_mul_pos_right (hdiam.trans_lt N.diameter_upper) N.constant_pos.le
  refine { N with
    constant_pos := hC'
    uniform_sectional_lower := ?_
    diameter_lower := ?_
    diameter_upper := ?_ }
  · obtain ⟨B, hB, hsectional⟩ := N.uniform_sectional_lower
    exact ⟨B, hinv.trans_lt hB, hsectional⟩
  · by_cases hsup : 0 ≤ sSup (Set.range (fun y : M =>
        (K.flow.connection t).scalarCurvature y ^ (-1 / 2 : ℝ)))
    · exact (mul_le_mul_of_nonneg_right hinv hsup).trans_lt N.diameter_lower
    · exact (mul_neg_of_pos_of_neg (inv_pos.mpr hC')
        (lt_of_not_ge hsup)).trans_le hdiam
  · exact N.diameter_upper.trans_le (mul_le_mul_of_nonneg_right hCC' hinf.le)

theorem M27StrongCanonicalNeighborhood.mono_constant
    (h : M27StrongCanonicalNeighborhood K t x epsilon C) (hCC' : C ≤ C') :
    M27StrongCanonicalNeighborhood K t x epsilon C' := by
  cases h with
  | neck N hcenter => exact .neck N hcenter
  | cap N => exact .cap (N.mono_constant hCC')
  | component N => exact .component (N.mono_constant hCC')
  | round N => exact .round N

theorem M27ScalarDerivativeBounds.mono_constant
    (h : M27ScalarDerivativeBounds K C) (hCC' : C ≤ C') :
    M27ScalarDerivativeBounds K C' := by
  obtain ⟨B, hB, hBC, hbounds⟩ := h
  exact ⟨B, hB, hBC.trans_le hCC', hbounds⟩

end PoincareConjecture
