import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactBounds.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.DoubleCapped
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Constants
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.Round













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture



theorem compact_nonround_positive_geometry_of_scaled_diameter
    (P : M27KappaAlternativePredecessors.{u}) {D : ℝ} (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M),
        ¬ IsRoundAncientKappaSolution K → IsCompact (univ : Set M) →
        (∀ x : M, metricDiameter (K.flow.metric 0) univ <
          D * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ)) →
        Nonempty (M27CompactPositiveGeometry K C) := by
  obtain ⟨C, hC, hgeometry⟩ := compact_positive_geometry_of_scaled_diameter P hD
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hnonround hcompact hdiam
  exact hgeometry K hnonround hcompact
    (P.compact_nonround_sphere_or_projective K hcompact hnonround) hdiam




theorem compact_positive_geometry_or_strongDoubleCapped
    (P : M27KappaAlternativePredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
            [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
            [SecondCountableTopology M] [ConnectedSpace M]
            (K : AncientKappaSolution 3 M),
            ¬ IsRoundAncientKappaSolution K → IsCompact (univ : Set M) →
            Nonempty (M27CompactPositiveGeometry K C) ∨
              Nonempty (M26StrongDoubleCappedTube K 0 epsilon C) := by
  obtain ⟨epsilon₀, hε₀, halternatives⟩ := P.compact_alternatives
  refine ⟨epsilon₀, hε₀, ?_⟩
  intro epsilon hepsilon hε
  obtain ⟨C₀, hC₀, hcases⟩ := halternatives epsilon hepsilon hε
  let D : ℝ := max C₀ 11
  have hD : 0 < D := hC₀.trans_le (le_max_left _ _)
  have h10 : 10 < D := (by norm_num : (10 : ℝ) < 11).trans_le (le_max_right _ _)
  obtain ⟨Cg, hCg, hgeometry⟩ :=
    compact_nonround_positive_geometry_of_scaled_diameter P hD
  refine ⟨max Cg C₀, hCg.trans_le (le_max_left _ _), ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hnonround hcompact
  have hscalar (x : M) : 0 < (K.flow.connection 0).scalarCurvature x := by
    obtain ⟨A⟩ := P.normalization M K x 0 le_rfl
    exact A.scale_eq ▸ A.scale_pos
  have hsmall (hdiam : ∀ x : M, metricDiameter (K.flow.metric 0) univ <
      D * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ)) :
      Nonempty (M27CompactPositiveGeometry K (max Cg C₀)) := by
    obtain ⟨G⟩ := hgeometry K hnonround hcompact hdiam
    exact ⟨G.mono_constant hCg (le_max_left _ _) hscalar⟩
  obtain ⟨H⟩ := hcases K hcompact
  obtain ⟨H⟩ := H.compact_alternatives
  cases H with
  | compactSmall S =>
      apply Or.inl
      apply hsmall
      intro x
      exact (S.diameter_bound x).trans_le
        (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (hscalar x).le _))
  | round hr _ =>
      apply Or.inl
      apply hsmall
      intro x
      have hs : 0 < Real.sqrt ((K.flow.connection 0).scalarCurvature x) :=
        Real.sqrt_pos.mpr (hscalar x)
      have hpower : (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ) =
          (Real.sqrt ((K.flow.connection 0).scalarCurvature x))⁻¹ := by
        rw [neg_div, Real.rpow_neg (hscalar x).le, ← Real.sqrt_eq_rpow]
      calc
        metricDiameter (K.flow.metric 0) univ ≤
            10 / Real.sqrt ((K.flow.connection 0).scalarCurvature x) :=
          (le_div_iff₀ hs).mpr (round_metricDiameter_mul_sqrt_scalar_le
            (K.flow.metric 0) (K.flow.connection 0) (K.complete 0 le_rfl) hr x)
        _ < D * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ) := by
          rw [hpower, div_eq_mul_inv]
          exact mul_lt_mul_of_pos_right h10 (inv_pos.mpr hs)
  | doubleCapped T => exact Or.inr ⟨T.mono_constant (le_max_right _ _)⟩

end PoincareConjecture
