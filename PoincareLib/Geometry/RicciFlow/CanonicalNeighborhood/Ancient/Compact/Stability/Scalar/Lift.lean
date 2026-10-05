import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Scalar.DerivativeBounds
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.CarrierLift
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Canonical.StaticMetric
import PoincareLib.Geometry.Riemannian.Homothety.Assembly

/-!
# Scalar derivative estimates on smaller carriers

Universe lifting pulls back the actual flow by the smooth map `ULift.down`.
The unit metric homothety preserves the scalar gradient and the full scalar
evolution expression. Consequently the uniform derivative constant supplied
in the predecessor universe also controls each solution on a small carrier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareMT

namespace RicciFlow

variable {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {J : Set ℝ}

local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} M) :=
  Poincare.Manifold.uliftChartedSpace _ M

local instance : IsManifold (𝓡 3) ∞ (ULift.{u} M) :=
  Poincare.Manifold.uliftIsManifold (𝓡 3) M

/-- The actual lifted flow has the same scalar gradient norm. -/
@[simp] theorem ulift_scalarGradientNorm (F : RicciFlow 3 M J)
    (t : ℝ) (x : ULift.{u} M) :
    scalarGradientNorm (F.ulift.metric t) (F.ulift.connection t) x =
      scalarGradientNorm (F.metric t) (F.connection t) x.down := by
  let e := Poincare.Manifold.uliftDiffeomorph (𝓡 3) M
  have he : MetricHomothety (F.ulift.metric t) (F.metric t) e 1 := by
    intro y a b
    rw [one_mul]
    rfl
  let H := Homothety.metricHomothetyCalculus (F.ulift.metric t) (F.metric t) e 1
    zero_lt_one he
  exact H.m48_scalarGradient_eq he (F.ulift.connection t) (F.connection t) x

/-- Universe lifting preserves the entire scalar evolution numerator, before
the absolute value in the cap derivative certificate is taken. -/
@[simp] theorem ulift_scalarEvolution (F : RicciFlow 3 M J)
    (t : ℝ) (x : ULift.{u} M) :
    (F.ulift.connection t).laplacian (F.ulift.connection t).scalarCurvature x +
        2 * (F.ulift.connection t).ricciNormSq x =
      (F.connection t).laplacian (F.connection t).scalarCurvature x.down +
        2 * (F.connection t).ricciNormSq x.down := by
  let e := Poincare.Manifold.uliftDiffeomorph (𝓡 3) M
  have he : MetricHomothety (F.ulift.metric t) (F.metric t) e 1 := by
    intro y a b
    rw [one_mul]
    rfl
  let H := Homothety.metricHomothetyCalculus (F.ulift.metric t) (F.metric t) e 1
    zero_lt_one he
  exact H.m48_scalarEvolution_eq he (F.ulift.connection t) (F.connection t) x

end RicciFlow

attribute [local instance] AncientKappaSolution.uliftSecondCountable
  AncientKappaSolution.uliftConnectedSpace

/-- The supplied predecessor universe controls every actual ancient solution
on a small carrier, with the same constant and strict slack as its lift. -/
theorem uniformKappaCapDerivativeBounds_small
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
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
  obtain ⟨D, hD, hbound⟩ := uniformKappaCapDerivativeBounds P
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
theorem uniformKappaCapDerivativeFields_small
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
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
  obtain ⟨D, hD, hbound⟩ := uniformKappaCapDerivativeBounds_small P
  refine ⟨D, hD, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K t C U ht hDC
  obtain ⟨B, _, hBD, hB⟩ := hbound K
  exact ⟨⟨B, hBD.trans_le hDC, fun x _ => (hB t ht x).1⟩,
    ⟨B, hBD.trans_le hDC, fun x _ => (hB t ht x).2⟩⟩

end PoincareMT
