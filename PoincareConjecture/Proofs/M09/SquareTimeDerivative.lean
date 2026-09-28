import PoincareConjecture.Proofs.M09.SquareTimeFields
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem squareTime_metric_hasDerivAt {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun r ↦ (F.metric (T - r ^ 2)).inner x u v)
      (4 * s * (F.connection (T - s ^ 2)).ricci x u v) s := by
  have hclock : HasDerivAt (fun r : ℝ ↦ T - r ^ 2) (-2 * s) s := by
    simpa only [id_eq, Nat.reduceSub, Nat.cast_ofNat, pow_one, mul_one, neg_mul] using
      (hasDerivAt_pow 2 s).const_sub T
  have hnear : ∀ᶠ r in 𝓝 s, T - r ^ 2 ∈ J := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    exact hwindow (squareTime_mem_window T hb hr)
  have h := (F.equation (T - s ^ 2)
    (hwindow (squareTime_mem_window T hb hs)) x u v).comp_hasDerivAt s hclock hnear
  convert! h using 1 <;> first | rfl | ring

end PoincareConjecture.Proofs.M09
