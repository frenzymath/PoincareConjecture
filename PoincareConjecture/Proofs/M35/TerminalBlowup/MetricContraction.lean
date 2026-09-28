import PoincareConjecture.Definitions.M34StandardCapExistence
import PoincareConjecture.Proofs.M04.PointwiseFlatness
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison
import Mathlib.Analysis.Calculus.Deriv.MeanValue











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RepairedStandardCapExistenceData



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



theorem tangentNorm_le_of_time_le {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {s t : ℝ}
    (hs : s ∈ Ico 0 E.flow.base.lifetime) (ht : t ∈ Ico 0 E.flow.base.lifetime)
    (hst : s ≤ t) (x : StandardCapSpace) (v : TangentSpace (𝓡 3) x) :
    (E.flow.metric t).tangentNorm x v ≤ (E.flow.metric s).tangentNorm x v :=
  Real.sqrt_le_sqrt (E.metric_inner_antitone x v hs ht hst)



theorem ball_subset_of_time_le {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {s t : ℝ}
    (hs : s ∈ Ico 0 E.flow.base.lifetime) (ht : t ∈ Ico 0 E.flow.base.lifetime)
    (hst : s ≤ t) (x : StandardCapSpace) (r : ℝ) :
    (E.flow.metric s).ball x r ⊆ (E.flow.metric t).ball x r := by
  simpa only [one_mul] using
    (E.flow.metric s).ball_subset_ball_of_tangentNorm_le (E.flow.metric t) x r 1
      zero_lt_one (fun y _ v => by simpa only [one_mul] using
        E.tangentNorm_le_of_time_le hs ht hst y v)

end PoincareConjecture.RepairedStandardCapExistenceData
