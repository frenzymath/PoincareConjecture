import PoincareConjecture.Proofs.M47.TerminalGermsOpenCharts










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

variable {n : ℕ} {M P N : Type*}
  [TopologicalSpace M] [TopologicalSpace P] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ P] [IsManifold (𝓡 n) ∞ N]

omit [IsManifold (𝓡 n) ∞ N] in


theorem terminalGerms_open_metric_compatibility
    (q : M → N) (r : P → N)
    (hq : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ q)
    (hr : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ r)
    (g : RiemannianMetric n M) (h : RiemannianMetric n P)
    (hmetric : ∀ x y, q x = r y → ∀ a b c d,
      mfderiv (𝓡 n) (𝓡 n) q x a = mfderiv (𝓡 n) (𝓡 n) r y c →
      mfderiv (𝓡 n) (𝓡 n) q x b = mfderiv (𝓡 n) (𝓡 n) r y d →
      g.inner x a b = h.inner y c d)
    (V : Opens N)
    (x : terminalGermsOpenChartSource q hq V)
    (y : terminalGermsOpenChartSource r hr V)
    (hxy : terminalGermsOpenChartMap q hq V x = terminalGermsOpenChartMap r hr V y)
    (a b : TangentSpace (𝓡 n) x) (c d : TangentSpace (𝓡 n) y)
    (ha : mfderiv (𝓡 n) (𝓡 n) (terminalGermsOpenChartMap q hq V) x a =
      mfderiv (𝓡 n) (𝓡 n) (terminalGermsOpenChartMap r hr V) y c)
    (hb : mfderiv (𝓡 n) (𝓡 n) (terminalGermsOpenChartMap q hq V) x b =
      mfderiv (𝓡 n) (𝓡 n) (terminalGermsOpenChartMap r hr V) y d) :
    (g.pullbackOfLocalDiffeomorph Subtype.val
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n)
        (terminalGermsOpenChartSource q hq V))).inner x a b =
    (h.pullbackOfLocalDiffeomorph Subtype.val
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n)
        (terminalGermsOpenChartSource r hr V))).inner y c d := by
  have hqx := terminalGerms_openChartMap_differential q hq V x
  have hry := terminalGerms_openChartMap_differential r hr V y
  apply hmetric x.val y.val (congrArg Subtype.val hxy) _ _ _ _
  · calc
      _ = mfderiv (𝓡 n) (𝓡 n) (Subtype.val : V → N)
          (terminalGermsOpenChartMap q hq V x)
          (mfderiv (𝓡 n) (𝓡 n) (terminalGermsOpenChartMap q hq V) x a) :=
        (congrArg (fun A => A a) hqx).symm
      _ = mfderiv (𝓡 n) (𝓡 n) (Subtype.val : V → N)
          (terminalGermsOpenChartMap r hr V y)
          (mfderiv (𝓡 n) (𝓡 n) (terminalGermsOpenChartMap r hr V) y c) :=
        congrArg₂ (fun (z : V) (v : EuclideanSpace ℝ (Fin n)) =>
          mfderiv (𝓡 n) (𝓡 n) (Subtype.val : V → N) z v) hxy ha
      _ = _ := congrArg (fun A => A c) hry
  · calc
      _ = mfderiv (𝓡 n) (𝓡 n) (Subtype.val : V → N)
          (terminalGermsOpenChartMap q hq V x)
          (mfderiv (𝓡 n) (𝓡 n) (terminalGermsOpenChartMap q hq V) x b) :=
        (congrArg (fun A => A b) hqx).symm
      _ = mfderiv (𝓡 n) (𝓡 n) (Subtype.val : V → N)
          (terminalGermsOpenChartMap r hr V y)
          (mfderiv (𝓡 n) (𝓡 n) (terminalGermsOpenChartMap r hr V) y d) :=
        congrArg₂ (fun (z : V) (v : EuclideanSpace ℝ (Fin n)) =>
          mfderiv (𝓡 n) (𝓡 n) (Subtype.val : V → N) z v) hxy hb
      _ = _ := congrArg (fun A => A d) hry

omit [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin n)) P]
  [IsManifold (𝓡 n) ∞ P] in


theorem terminalGerms_open_terminal_metric
    (q : M → N) (hq : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ q)
    (g : RiemannianMetric n M) (g0 : RiemannianMetric n N)
    (hterminal : ∀ x a b, g.inner x a b = g0.inner (q x)
      (mfderiv (𝓡 n) (𝓡 n) q x a) (mfderiv (𝓡 n) (𝓡 n) q x b))
    (V : Opens N) (x : terminalGermsOpenChartSource q hq V)
    (a b : TangentSpace (𝓡 n) x) :
    (g.pullbackOfLocalDiffeomorph Subtype.val
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n)
        (terminalGermsOpenChartSource q hq V))).inner x a b =
    (g0.pullbackOfLocalDiffeomorph Subtype.val
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) V)).inner
      (terminalGermsOpenChartMap q hq V x)
      (mfderiv (𝓡 n) (𝓡 n) (terminalGermsOpenChartMap q hq V) x a)
      (mfderiv (𝓡 n) (𝓡 n) (terminalGermsOpenChartMap q hq V) x b) := by
  have hq' := terminalGerms_openChartMap_differential q hq V x
  change g.inner x.val _ _ = g0.inner (q x.val) _ _
  rw [hterminal]
  exact congrArg₂ (fun v w : EuclideanSpace ℝ (Fin n) => g0.inner (q x.val) v w)
    (congrArg (fun A => A a) hq').symm (congrArg (fun A => A b) hq').symm

end PoincareConjecture.M47
