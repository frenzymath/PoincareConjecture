import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.ExistenceData
import PoincareLib.Geometry.RicciFlow.Positivity.PointwiseFlatness
import PoincareLib.Geometry.Riemannian.MetricComparison
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Metric contraction on the actual standard flow

Morgan-Tian Proposition 12.31, pp. 325-326, uses decreasing distances to
keep a fixed regular region in one fixed-radius ball. Nonnegative
sectional curvature and the actual Ricci-flow equation make every metric
quadratic form decrease. The resulting norm and ball comparisons require
no terminal metric or geodesic-existence assumption.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.RepairedStandardCapExistenceData

/-- Proposition 12.31, pp. 325-326: the selected standard metric decreases
as a quadratic form along the actual flow. -/
theorem metric_inner_antitone {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (x : StandardCapSpace)
    (v : TangentSpace (𝓡 3) x) :
    AntitoneOn (fun t => (E.flow.metric t).inner x v v) (Ico 0 E.flow.base.lifetime) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico 0 E.flow.base.lifetime)
    (fun t ht => (E.flow.base.flow.equation t ht x v v).continuousWithinAt)
    (fun t ht => (E.flow.base.flow.equation t (interior_subset ht) x v v).mono interior_subset)
  intro t ht
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
    (M04.nonneg_ricci_of_nonnegativeSectionalAt (E.flow.connection t) x
      (E.nonnegative_sectional t (interior_subset ht) x) v)

/-- Proposition 12.31, pp. 325-326: every fixed tangent norm decreases
between two times of the selected standard flow. -/
theorem tangentNorm_le_of_time_le {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {s t : ℝ}
    (hs : s ∈ Ico 0 E.flow.base.lifetime) (ht : t ∈ Ico 0 E.flow.base.lifetime)
    (hst : s ≤ t) (x : StandardCapSpace) (v : TangentSpace (𝓡 3) x) :
    (E.flow.metric t).tangentNorm x v ≤ (E.flow.metric s).tangentNorm x v :=
  Real.sqrt_le_sqrt (E.metric_inner_antitone x v hs ht hst)

/-- Proposition 12.31, pp. 325-326: an earlier fixed ball remains inside
the later ball of the same radius because the actual metric contracts. -/
theorem ball_subset_of_time_le {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {s t : ℝ}
    (hs : s ∈ Ico 0 E.flow.base.lifetime) (ht : t ∈ Ico 0 E.flow.base.lifetime)
    (hst : s ≤ t) (x : StandardCapSpace) (r : ℝ) :
    (E.flow.metric s).ball x r ⊆ (E.flow.metric t).ball x r := by
  simpa only [one_mul] using
    (E.flow.metric s).ball_subset_ball_of_tangentNorm_le (E.flow.metric t) x r 1
      zero_lt_one (fun y _ v => by simpa only [one_mul] using
        E.tangentNorm_le_of_time_le hs ht hst y v)

end PoincareMT.RepairedStandardCapExistenceData
