import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.Curvature










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture



theorem nonround_uniform_curvature_scale_separation_of_services
    (P : NoncompactKappaServices.{u}) {A : ℝ} (hA : 0 ≤ A) :
    ∃ L : ℝ, 0 < L ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p q : M),
        ¬ IsRoundAncientKappaSolution K →
        (K.flow.connection 0).scalarCurvature p = 1 →
        L < ((K.flow.metric 0).edist q p).toReal →
        A < Real.sqrt ((K.flow.connection 0).scalarCurvature q) *
          ((K.flow.metric 0).edist q p).toReal := by
  have hApos : 0 < A + 1 := by linarith
  obtain ⟨C, hC, hbound⟩ := nonround_uniform_core_scalar_upper_of_services P hApos
  have hCpos : 0 < C := zero_lt_one.trans hC
  refine ⟨(A + 1) * Real.sqrt C, by positivity, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p q hnonround hnormalized hd
  obtain ⟨N⟩ := P.normalization M K q 0 le_rfl
  have hR : 0 < (K.flow.connection 0).scalarCurvature q := N.scale_eq ▸ N.scale_pos
  have hsqrt : 0 < Real.sqrt ((K.flow.connection 0).scalarCurvature q) :=
    Real.sqrt_pos.mpr hR
  by_contra hn
  push_neg at hn
  have hp : p ∈ (K.flow.metric 0).ball q
      ((A + 1) * (K.flow.connection 0).scalarCurvature q ^ (-1 / 2 : ℝ)) := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt
      ((K.flow.metric 0).edist_ne_top q p)).mpr
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg hR.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
    apply (lt_div_iff₀ hsqrt).mpr
    nlinarith
  have hscalar := hbound K q hnonround p hp
  rw [hnormalized] at hscalar
  have hroot := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num) hscalar
  rw [Real.sqrt_one, Real.sqrt_mul hCpos.le] at hroot
  have hcontr : A < A := by
    calc
      A < A + 1 := by linarith
      _ < (A + 1) * (Real.sqrt C *
          Real.sqrt ((K.flow.connection 0).scalarCurvature q)) := by nlinarith
      _ = ((A + 1) * Real.sqrt C) *
          Real.sqrt ((K.flow.connection 0).scalarCurvature q) := by ring
      _ < ((K.flow.metric 0).edist q p).toReal *
          Real.sqrt ((K.flow.connection 0).scalarCurvature q) :=
        mul_lt_mul_of_pos_right hd hsqrt
      _ ≤ A := by nlinarith
  exact (lt_irrefl A) hcontr

theorem nonround_uniform_curvature_scale_separation
    (P : M26CanonicalNeighborhoodPredecessors.{u}) {A : ℝ} (hA : 0 ≤ A) :
    ∃ L : ℝ, 0 < L ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p q : M),
        ¬ IsRoundAncientKappaSolution K →
        (K.flow.connection 0).scalarCurvature p = 1 →
        L < ((K.flow.metric 0).edist q p).toReal →
        A < Real.sqrt ((K.flow.connection 0).scalarCurvature q) *
          ((K.flow.metric 0).edist q p).toReal := by
  exact nonround_uniform_curvature_scale_separation_of_services P.noncompactServices hA

end PoincareConjecture
