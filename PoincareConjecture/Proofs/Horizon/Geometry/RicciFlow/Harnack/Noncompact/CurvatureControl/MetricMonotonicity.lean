import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.MetricComparison
import Mathlib.Analysis.Calculus.Deriv.MeanValue









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}



theorem antitoneOn_metric_inner_self_of_ricci_nonneg
    (F : RicciFlow n M J) {a b : ℝ} (hJ : Icc a b ⊆ interior J)
    (x : M) (v : TangentSpace (𝓡 n) x)
    (hRic : ∀ t ∈ Icc a b, 0 ≤ (F.connection t).ricci x v v) :
    AntitoneOn (fun t => (F.metric t).inner x v v) (Icc a b) := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s => (F.metric s).inner x v v)
        (-2 * (F.connection t).ricci x v v) t :=
    (F.equation t (interior_subset (hJ ht)) x v v).hasDerivAt
      (mem_interior_iff_mem_nhds.mp (hJ ht))
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hd t (interior_subset ht)).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hRic t (interior_subset ht))


theorem tangentNorm_le_of_ricci_nonneg
    (F : RicciFlow n M J) {a b : ℝ} (hJ : Icc a b ⊆ interior J)
    (x : M) (v : TangentSpace (𝓡 n) x)
    (hRic : ∀ τ ∈ Icc a b, 0 ≤ (F.connection τ).ricci x v v)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    (F.metric t).tangentNorm x v ≤ (F.metric s).tangentNorm x v :=
  Real.sqrt_le_sqrt (F.antitoneOn_metric_inner_self_of_ricci_nonneg hJ x v hRic hs ht hst)



theorem ball_subset_ball_of_ricci_nonneg
    (F : RicciFlow n M J) {a b : ℝ} (hJ : Icc a b ⊆ interior J)
    (p : M) (r : ℝ) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hRic : ∀ τ ∈ Icc a b, ∀ x ∈ (F.metric s).ball p r,
      ∀ v : TangentSpace (𝓡 n) x, 0 ≤ (F.connection τ).ricci x v v) :
    (F.metric s).ball p r ⊆ (F.metric t).ball p r := by
  simpa only [one_mul] using
    RiemannianMetric.ball_subset_ball_of_tangentNorm_le
      (F.metric s) (F.metric t) p r 1 zero_lt_one (by
        intro x hx v
        simpa only [one_mul] using F.tangentNorm_le_of_ricci_nonneg hJ x v
          (fun τ hτ => hRic τ hτ x hx v) hs ht hst)

end PoincareConjecture.RicciFlow
