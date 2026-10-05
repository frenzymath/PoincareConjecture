import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Basic.GeneralizedCylinderReverseBall
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Limits.GeneralizedCompactMetricComparison
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Calculus.RiemannianProper
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Calculus.RiemannianProper

/-!
# Actual reverse ball localization along generalized blow-up convergence

Completeness makes one larger limit ball precompact. The actual frozen
order-zero metric convergence on its closure and source-ball coverage
then give uniform reverse localization before any source point is chosen.
Source: Morgan-Tian Theorem 12.29 and Claim 12.30, pp. 324-325;
reverse-ball-localization.md.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.GeneralizedBlowupConvergence

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (C : GeneralizedBlowupConvergence S J)

local instance : TopologicalSpace C.limit.carrier.carrier := C.limit.carrier.topologicalSpace
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.limit.carrier.carrier :=
  C.limit.carrier.chartedSpace
local instance : IsManifold (𝓡 3) ∞ C.limit.carrier.carrier := C.limit.carrier.isManifold

/-- For each fixed positive normalized radius, all points in the actual
source ball eventually have actual preimages in the limit ball of twice
that radius. The index precedes every point of the ball
(Theorem 12.29 and Claim 12.30, pp. 324-325). -/
theorem eventually_source_ball_localization_zero (a : ℝ) (ha : 0 < a) :
    ∀ᶠ k : ℕ in atTop, ∀ x ∈ S.baseBall (C.subsequence k) a,
      ∃ y ∈ (C.limit.flow.metric 0).ball C.limit.base (2 * a) ∩ C.exhaustion.space k,
        ∃ h0, (C.embedding k).pointMap 0 h0 y =
          (⟨(S.base (C.subsequence k)).1, x⟩ : (S.flow (C.subsequence k)).point) := by
  let : T3Space C.limit.carrier.carrier := C.limit.carrier.t3Space
  let : ConnectedSpace C.limit.carrier.carrier := C.limit.connectedSpace
  let g := C.limit.flow.metric 0
  let K := closure (g.ball C.limit.base (2 * a + 1))
  have hK : IsCompact K := Proofs.M09.isCompact_closure_metric_ball g
    (C.limit.complete 0 C.limit.zero_mem) C.limit.base (2 * a + 1)
  have hsub : {x | g.edist C.limit.base x ≤ ENNReal.ofReal (2 * a)} ⊆ K := by
    intro x hx
    apply subset_closure
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
  let h0 : ∀ k, 0 ∈ Icc (-C.exhaustion.time k) 0 :=
    fun k => ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
  filter_upwards [C.eventually_pullback_inner_comparison_zero hK,
    C.source_balls_in_image a ha] with k hk hcover
  have hlocal := (C.embedding k).reverse_ball_zero_of_pullback_inner_lower
    (C.exhaustion.space_open k) (h0 k) (S.base_scalar_pos (C.subsequence k)) g
    (C.exhaustion.base_mem k) (C.base_preserving k (h0 k)) (a := a)
    (fun x hx => by
      obtain ⟨y, hy, hy0, he⟩ := hcover x hx
      exact ⟨y, hy, he⟩)
    (fun x _ hd v => (hk.2 x (hsub hd) v).1)
  intro x hx
  obtain ⟨y, hy, he⟩ := hlocal x hx
  exact ⟨y, hy, h0 k, he⟩

end PoincareMT.GeneralizedBlowupConvergence
