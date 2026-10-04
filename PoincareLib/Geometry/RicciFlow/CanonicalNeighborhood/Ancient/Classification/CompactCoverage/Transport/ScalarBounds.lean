import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Main
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Scalar.Lift

/-!
# M27 scalar derivative constants on terminal cap carriers

The uniform normalized scalar jets bound the gradient and the actual
Laplacian-plus-Ricci expression. Positive parabolic normalization transports
these inequalities to the scalar powers in the cap certificate. Scalar
evolution is differentiated within the ancient interval, including time zero.

Reference: Morgan--Tian, Definition 9.72(8), pp. 230--231, and
Corollary 9.71, equations (9.31)--(9.32), pp. 229--230.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- A constant chosen before the carrier and ancient solution gives strict
slack in both actual derivative fields of every cap, at every ancient time. -/
theorem uniformKappaCapDerivativeBounds_of_m27
    (P : M27KappaAlternativePredecessors.{u}) :
    ∃ D : ℝ, 0 < D ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
        ∀ K : AncientKappaSolution 3 M,
          ∃ B : ℝ, 0 ≤ B ∧ B < D ∧ ∀ t : ℝ, t ≤ 0 → ∀ x : M,
            scalarGradientNorm (K.flow.metric t) (K.flow.connection t) x ≤
              B * (K.flow.connection t).scalarCurvature x ^ (3 / 2 : ℝ) ∧
            |(K.flow.connection t).laplacian (K.flow.connection t).scalarCurvature x +
                2 * (K.flow.connection t).ricciNormSq x| ≤
              B * (K.flow.connection t).scalarCurvature x ^ 2 := by
  obtain ⟨B, hB, hbound⟩ :=
    ScalarDerivatives.uniform_normalized_scalar_jets P.scalarDerivativeServices
  refine ⟨B + 1, by linarith, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K
  refine ⟨B, hB.le, by linarith, ?_⟩
  intro t ht x
  obtain ⟨N⟩ := P.normalization M K x t ht
  obtain ⟨hgradient, hevolution⟩ := hbound N.target x N.normalized_scalar
  exact ⟨N.scalarGradientNorm_le hB.le hgradient,
    N.scalarEvolution_bound P.scalarDerivativeServices ht hevolution⟩

attribute [local instance] AncientKappaSolution.uliftSecondCountable
  AncientKappaSolution.uliftConnectedSpace

/-- The supplied predecessor universe controls every actual ancient solution
on a small carrier, with the same constant and strict slack as its lift. -/
theorem uniformKappaCapDerivativeBounds_small_of_m27
    (P : M27KappaAlternativePredecessors.{u}) :
    ∃ D : ℝ, 0 < D ∧
      ∀ {M : Type} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
        ∀ K : AncientKappaSolution 3 M,
          ∃ B : ℝ, 0 ≤ B ∧ B < D ∧ ∀ t : ℝ, t ≤ 0 → ∀ x : M,
            scalarGradientNorm (K.flow.metric t) (K.flow.connection t) x ≤
              B * (K.flow.connection t).scalarCurvature x ^ (3 / 2 : ℝ) ∧
            |(K.flow.connection t).laplacian (K.flow.connection t).scalarCurvature x +
                2 * (K.flow.connection t).ricciNormSq x| ≤
              B * (K.flow.connection t).scalarCurvature x ^ 2 := by
  obtain ⟨D, hD, hbound⟩ := uniformKappaCapDerivativeBounds_of_m27 P
  refine ⟨D, hD, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} M) :=
    Poincare.Manifold.uliftChartedSpace _ M
  let : IsManifold (𝓡 3) ∞ (ULift.{u} M) :=
    Poincare.Manifold.uliftIsManifold (𝓡 3) M
  let L : AncientKappaSolution 3 (ULift.{u} M) := K.ulift
  obtain ⟨B, hB, hBD, hderivatives⟩ := hbound L
  refine ⟨B, hB, hBD, ?_⟩
  intro t ht x
  simpa only [L, AncientKappaSolution.ulift_flow, RicciFlow.ulift_scalarGradientNorm,
    RicciFlow.ulift_scalarEvolution, RicciFlow.ulift_scalarCurvature] using
    hderivatives t ht (ULift.up.{u} x)

/-- Restriction to a source cap gives both strict derivative fields on a
small carrier, directly from predecessors in the supplied universe. -/
theorem uniformKappaCapDerivativeFields_small_of_m27
    (P : M27KappaAlternativePredecessors.{u}) :
    ∃ D : ℝ, 0 < D ∧
      ∀ {M : Type} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
        ∀ (K : AncientKappaSolution 3 M) (t C : ℝ) (U : Set M),
          t ≤ 0 → D ≤ C →
          (∃ B : ℝ, B < C ∧ ∀ x ∈ U,
            scalarGradientNorm (K.flow.metric t) (K.flow.connection t) x ≤
              B * (K.flow.connection t).scalarCurvature x ^ (3 / 2 : ℝ)) ∧
          (∃ B : ℝ, B < C ∧ ∀ x ∈ U,
            |(K.flow.connection t).laplacian (K.flow.connection t).scalarCurvature x +
                2 * (K.flow.connection t).ricciNormSq x| ≤
              B * (K.flow.connection t).scalarCurvature x ^ 2) := by
  obtain ⟨D, hD, hbound⟩ := uniformKappaCapDerivativeBounds_small_of_m27 P
  refine ⟨D, hD, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K t C U ht hDC
  obtain ⟨B, _, hBD, hB⟩ := hbound K
  exact ⟨⟨B, hBD.trans_le hDC, fun x _ => (hB t ht x).1⟩,
    ⟨B, hBD.trans_le hDC, fun x _ => (hB t ht x).2⟩⟩

end PoincareMT
