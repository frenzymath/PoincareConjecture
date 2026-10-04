import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.LocalBounds
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.LocalEstimates
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Contractions
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Small
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Round

/-!
# Uniform scalar jets at normalized basepoints

For a fixed positive noncollapsing constant, the uniform local scalar estimate
and Shi's estimates bound the first two curvature derivatives at the basepoint.
Their contractions bound the scalar gradient and scalar evolution. Universal
noncollapse for nonround solutions and the direct round estimates give one
constant for every scalar-normalized ancient solution.

Reference: Morgan--Tian, Corollary 9.71 and equations (9.31)-(9.32),
pp. 229-230; Theorem 9.93, pp. 242-243.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.ScalarDerivatives

attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space RicciFlow.smallMeasurableSpace
  RicciFlow.smallBorelSpace

theorem uniform_normalized_curvatureDerivative_bound
    (S : ScalarDerivativeServices.{u}) {kappa : ℝ} (hkappa : 0 < kappa)
    (k : ℕ) :
    ∃ D : ℝ, 0 < D ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M],
        ∀ (K : AncientKappaSolution 3 M) (p : M),
          AncientKappaNoncollapsed K.flow kappa →
          (K.flow.connection 0).scalarCurvature p = 1 →
          (K.flow.connection 0).curvatureDerivativeNorm k p ≤ D := by
  obtain ⟨L, hL, hlocal⟩ := uniform_based_local_scalar_bound S hkappa 1 (by norm_num)
  obtain ⟨D, hD, hderiv⟩ := uniform_terminal_curvatureDerivative_bound S L hL k
  refine ⟨D, hD, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnc hR
  apply hderiv K p
  intro x hx
  have hb := hlocal (smallBasedKappaSolution K p kappa hkappa hnc hR) (equivShrink M x)
    ((smallBasedKappaSolution_mem_ball K p kappa hkappa hnc hR 0 1 x).mpr hx)
  change (K.flow.shrink.connection 0).scalarCurvature (equivShrink M x) ≤ L at hb
  simpa only [K.flow.shrink_scalarCurvature, Equiv.symm_apply_apply] using hb

theorem uniform_fixed_kappa_scalar_jets
    (S : ScalarDerivativeServices.{u}) {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ B : ℝ, 0 < B ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M],
        ∀ (K : AncientKappaSolution 3 M) (p : M),
          AncientKappaNoncollapsed K.flow kappa →
          (K.flow.connection 0).scalarCurvature p = 1 →
          scalarGradientNorm (K.flow.metric 0) (K.flow.connection 0) p ≤ B ∧
          |(K.flow.connection 0).laplacian (K.flow.connection 0).scalarCurvature p +
            2 * (K.flow.connection 0).ricciNormSq p| ≤ B := by
  obtain ⟨D₁, hD₁, hb₁⟩ := uniform_normalized_curvatureDerivative_bound S hkappa 1
  obtain ⟨D₂, hD₂, hb₂⟩ := uniform_normalized_curvatureDerivative_bound S hkappa 2
  refine ⟨9 * D₁ + 27 * D₂ + 2, by positivity, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnc hR
  have hcalc := S.tensor_calculus 3 M (K.flow.metric 0) (K.flow.connection 0)
  have h₁ := hb₁ K p hnc hR
  have h₂ := hb₂ K p hnc hR
  constructor
  · have hg := scalarGradientNorm_le_curvatureDerivativeNorm
      (K.flow.metric 0) (K.flow.connection 0) hcalc p
    linarith
  · have hlap := (K.flow.connection 0).abs_laplacian_scalar_le_curvatureDerivativeNorm hcalc p
    have hRic : ∀ v : TangentSpace (𝓡 3) p, 0 ≤ (K.flow.connection 0).ricci p v v :=
      fun v => ((K.flow.connection 0).ricci_bounds_of_nonnegative_curvatureOperator
        hcalc p (K.nonnegative_curvature_operator 0 le_rfl p) v).1
    have hRicSq := (K.flow.connection 0).ricciNormSq_le_scalarCurvature_sq_of_ricci_nonneg
      hcalc p hRic
    rw [hR, one_pow] at hRicSq
    have hRicSq0 : 0 ≤ (K.flow.connection 0).ricciNormSq p :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have ht := abs_add_le ((K.flow.connection 0).laplacian
      (K.flow.connection 0).scalarCurvature p) (2 * (K.flow.connection 0).ricciNormSq p)
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hRicSq0)] at ht
    norm_num only [Nat.cast_ofNat, pow_succ, pow_zero, mul_one] at hlap
    linarith

/-- One normalized scalar-jet bound works for both the round and nonround families. -/
theorem uniform_normalized_scalar_jets
    (S : ScalarDerivativeServices.{u}) :
    ∃ B : ℝ, 0 < B ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M],
        ∀ (K : AncientKappaSolution 3 M) (p : M),
          (K.flow.connection 0).scalarCurvature p = 1 →
          scalarGradientNorm (K.flow.metric 0) (K.flow.connection 0) p ≤ B ∧
          |(K.flow.connection 0).laplacian (K.flow.connection 0).scalarCurvature p +
            2 * (K.flow.connection 0).ricciNormSq p| ≤ B := by
  classical
  obtain ⟨kappa, hkappa, hnc⟩ := S.universal_noncollapsing
  obtain ⟨B, hB, hbound⟩ := uniform_fixed_kappa_scalar_jets S hkappa
  refine ⟨B + 2, by linarith, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hR
  by_cases hround : IsRoundAncientKappaSolution K
  · constructor
    · rw [round_scalarGradientNorm_eq_zero (K.flow.connection 0) (hround 0 le_rfl) p]
      linarith
    · have h := round_scalarEvolution_bound (K.flow.connection 0)
        (S.tensor_calculus 3 M _ _) (hround 0 le_rfl) p
      rw [hR, one_pow, mul_one] at h
      linarith
  · obtain ⟨hg, ht⟩ := hbound K p (hnc K hround) hR
    constructor <;> linarith

end PoincareMT.ScalarDerivatives
