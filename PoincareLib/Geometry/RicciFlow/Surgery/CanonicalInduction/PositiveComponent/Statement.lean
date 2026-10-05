import PoincareLib.Geometry.RicciFlow.Basic
import PoincareLib.Geometry.RicciFlow.Pinching.Definitions

/-!
# M47 positive-component terminal blow-up

Natural-language theorem: a Ricci flow on a compact connected smooth
three-manifold, initially strictly positively curved and with unbounded
curvature arbitrarily near a finite terminal time, has scalar curvature
tending uniformly to positive infinity at that time. ConnectedSpace includes
nonemptiness. The curvature and positivity refer to the actual flow metric.

Source: the strictly positive branch of Morgan--Tian Theorem 4.23,
printed pp. 74-75. Compactness makes terminal blow-up incompatible with a
smooth extension. Hamilton's pinching ratio then gives uniform divergence.
The printed nonnegative-Ricci dichotomy is not asserted. See
reviews/contracts/2026-09-20-m47-complete-contract.md.
This supporting conclusion belongs to M47's existing single admission.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- Terminal full-curvature blow-up is uniform in scalar curvature on an
initially strictly positive compact connected ordinary component. -/
def M47PositiveComponentBlowupStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M],
    ∀ T : ℝ, 0 < T → ∀ F : RicciFlow 3 M (Set.Ico 0 T),
      (∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
        LeviCivitaData.IsOrthonormalPair (F.metric 0) x v w →
          0 < (F.connection 0).sectionalCurvature x v w) →
      (∀ L s : ℝ, s < T → ∃ t ∈ Set.Ioo (max 0 s) T, ∃ x : M,
        L < (F.connection t).curvatureTensorNorm x) →
      ∀ L : ℝ, ∃ s : ℝ, 0 ≤ s ∧ s < T ∧
        ∀ t ∈ Set.Ioo s T, ∀ x : M, L ≤ (F.connection t).scalarCurvature x

end PoincareMT
