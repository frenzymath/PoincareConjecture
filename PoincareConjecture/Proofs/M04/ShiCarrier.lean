import PoincareConjecture.Proofs.M04.LocalMetricComparison










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Set

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem initial_half_ball_closure_isCompact [T2Space M]
    (g : RiemannianMetric n M) (p : M) {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (closure (g.ball p r))) :
    IsCompact (closure (g.ball p (r / 2))) := by
  apply hcompact.of_isClosed_subset isClosed_closure
  exact (initial_half_ball_closure_subset_initial_ball g p hr).trans
    subset_closure

theorem initial_ball_isOpen [T2Space M]
    (g : RiemannianMetric n M) (p : M) (r : ℝ) :
    IsOpen (g.ball p r) := by
  letI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  letI : PseudoEMetricSpace M := .ofRiemannianMetric (𝓡 n) M
  have hcont : Continuous (fun y => g.edist p y) :=
    continuous_const.edist continuous_id
  change IsOpen {y | g.edist p y < ENNReal.ofReal r}
  exact isOpen_lt hcont continuous_const

end PoincareConjecture.M04
