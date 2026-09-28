import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RicciFlow



theorem inner_self_antitoneOn_of_nonnegative_ricci
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J I : Set ℝ} (F : RicciFlow n M J) (hI : Convex ℝ I) (hIJ : I ⊆ J)
    (x : M) (v : TangentSpace (𝓡 n) x)
    (hRic : ∀ t ∈ I, 0 ≤ (F.connection t).ricci x v v) :
    AntitoneOn (fun t => (F.metric t).inner x v v) I := by
  have hd (t : ℝ) (ht : t ∈ I) := (F.equation t (hIJ ht) x v v).mono hIJ
  apply antitoneOn_of_hasDerivWithinAt_nonpos hI
    (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).mono interior_subset)
  intro t ht
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hRic t (interior_subset ht))

end PoincareConjecture.RicciFlow
