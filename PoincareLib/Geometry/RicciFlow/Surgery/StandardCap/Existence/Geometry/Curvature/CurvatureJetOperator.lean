import PoincareLib.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.BootstrapAdapter
import PoincareLib.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Curvature.Recurrence

/-!
# Universal finite-jet operators for covariant curvature components

Spatial prolongation differentiates the preceding component operator.
Subtracting one Christoffel correction for every existing tensor slot
gives the next covariant derivative. The operators are smooth on the
invertible-metric jet domain. This is the interpolation estimate for
Morgan-Tian Theorem 12.5, pp. 296-297; see restart-curvature-jet-bounds.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Finite metric jets are dependent products of multilinear-map spaces.
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareMT.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap

/-- Formal metric jets with invertible zeroth coefficient at each
covariant curvature order (Theorem 12.5, pp. 296-297). -/
def curvatureJetDomain (n m : ℕ) :
    Set (Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) (2 + m)) :=
  (baseProjection 2 m) ⁻¹' jetRicciFlowDomain n

/-- The finite-jet curvature domain is open (Theorem 12.5, pp. 296-297). -/
theorem isOpen_curvatureJetDomain (n m : ℕ) : IsOpen (curvatureJetDomain n m) :=
  (isOpen_jetRicciFlowDomain n).preimage (baseProjection 2 m).continuous

/-- Components of the order-m covariant curvature derivative as a
universal function of the metric jet through order m+2. New derivative
slots occur first (Theorem 12.5, pp. 296-297). -/
noncomputable def curvatureJetComponents (n : ℕ) : (m : ℕ) →
    Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) (2 + m) →
      (Fin (4 + m) → Fin n) → ℝ
  | 0 => fun J I => jetCurvature (twoJetProjection n J)
      (EuclideanSpace.basisFun (Fin n) ℝ (I 0)) (EuclideanSpace.basisFun (Fin n) ℝ (I 1))
      (EuclideanSpace.basisFun (Fin n) ℝ (I 2)) (EuclideanSpace.basisFun (Fin n) ℝ (I 3))
  | m + 1 => by
      classical
      exact fun J I =>
        (prolong (2 + m) (curvatureJetComponents n m) J
          (EuclideanSpace.basisFun (Fin n) ℝ (I 0))) (Fin.tail I) -
        ∑ i : Fin (4 + m), ∑ a : Fin n,
          EuclideanSpace.proj a (jetChristoffel
            (twoJetProjection n (baseProjection 2 (m + 1) J))
            (EuclideanSpace.basisFun (Fin n) ℝ (I 0))
            (EuclideanSpace.basisFun (Fin n) ℝ (Fin.tail I i))) *
          curvatureJetComponents n m (truncate (2 + m) J) (Function.update (Fin.tail I) i a)

set_option synthInstance.maxHeartbeats 100000 in
-- Prolongation and truncation retain the dependent finite-jet order.
/-- All covariant curvature component operators are smooth on their
actual invertible-metric domain (Theorem 12.5, pp. 296-297). -/
theorem contDiffOn_curvatureJetComponents (n m : ℕ) :
    ContDiffOn ℝ ∞ (curvatureJetComponents n m) (curvatureJetDomain n m) := by
  classical
  induction m with
  | zero =>
      apply contDiffOn_pi.mpr
      intro I J hJ
      change ((twoJetProjection n J).1).IsInvertible at hJ
      exact ((contDiffAt_jetCurvature hJ _ _ _ _).comp J
        (twoJetProjection n).contDiff.contDiffAt).contDiffWithinAt
  | succ m ih =>
      have hp := contDiffOn_prolong (isOpen_curvatureJetDomain n m) ih
      have hbase : ContDiffOn ℝ ∞
          (fun J => curvatureJetComponents n m (truncate (2 + m) J))
          (curvatureJetDomain n (m + 1)) :=
        ih.comp (truncate (E := EuclideanSpace ℝ (Fin n)) (V := MetricCoefficient n)
          (2 + m)).contDiff.contDiffOn (fun _ h => h)
      apply contDiffOn_pi.mpr
      intro I
      apply (contDiffOn_pi.mp (hp.clm_apply contDiffOn_const) (Fin.tail I)).sub
      apply ContDiffOn.sum
      intro i _
      apply ContDiffOn.sum
      intro a _
      apply ContDiffOn.mul _ (contDiffOn_pi.mp hbase (Function.update (Fin.tail I) i a))
      intro J hJ
      have hΓ : ContDiffAt ℝ ∞ (fun K => jetChristoffel
          (twoJetProjection n (baseProjection 2 (m + 1) K))
          (EuclideanSpace.basisFun (Fin n) ℝ (I 0))
          (EuclideanSpace.basisFun (Fin n) ℝ (Fin.tail I i))) J := by
        have hproj : ContDiffAt ℝ ∞
            (fun K => twoJetProjection n (baseProjection 2 (m + 1) K)) J :=
          ((twoJetProjection n).comp (baseProjection 2 (m + 1))).contDiff.contDiffAt
        have h := (contDiffAt_jetChristoffel hJ
          (u := fun _ => EuclideanSpace.basisFun (Fin n) ℝ (I 0))
          (v := fun _ => EuclideanSpace.basisFun (Fin n) ℝ (Fin.tail I i))
          contDiffAt_const contDiffAt_const).comp J hproj
        convert! h using 1
      exact ((EuclideanSpace.proj a).contDiff.contDiffAt.comp J hΓ).contDiffWithinAt

end PoincareMT.M34
