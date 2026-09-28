import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Basic
import Mathlib.Analysis.Calculus.MeanValue








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)

theorem inner_antitone_of_nonnegative_ricci (hJ : Convex ℝ J)
    (hRic : ∀ t ∈ J, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).ricci x v v)
    {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) (hst : s ≤ t)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    (F.metric t).inner x v v ≤ (F.metric s).inner x v v := by
  have hm : AntitoneOn (fun t ↦ (F.metric t).inner x v v) J := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos hJ
      (fun t ht ↦ (F.equation t ht x v v).continuousWithinAt)
      (f' := fun t ↦ -2 * (F.connection t).ricci x v v)
    · intro t ht
      exact (F.equation t (interior_subset ht) x v v).mono interior_subset
    · intro t ht
      exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hRic t (interior_subset ht) x v)
  exact hm hs ht hst

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

theorem volumeMeasure_antitone_of_nonnegative_ricci (hJ : Convex ℝ J)
    (hRic : ∀ t ∈ J, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).ricci x v v)
    {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) (hst : s ≤ t)
    {A : Set M} (hA : MeasurableSet A) :
    (F.metric t).volumeMeasure A ≤ (F.metric s).volumeMeasure A :=
  (F.metric s).volumeMeasure_le_of_inner_le (F.metric t)
    (F.inner_antitone_of_nonnegative_ricci hJ hRic hs ht hst) hA

end PoincareConjecture.RicciFlow
