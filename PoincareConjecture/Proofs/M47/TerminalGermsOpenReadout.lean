import PoincareConjecture.Proofs.M47.TerminalGermsOpenCharts
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenInclusion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareConjecture.M47

variable {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]

theorem terminalGerms_openChartMap_mfderiv
    (q : M → N) (hq : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ q)
    (V : Opens N) (x : terminalGermsOpenChartSource q hq V) :
    mfderiv (𝓡 n) (𝓡 n) (terminalGermsOpenChartMap q hq V) x =
      mfderiv (𝓡 n) (𝓡 n) q x.val := by
  have h := terminalGerms_openChartMap_differential q hq V x
  rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal
      (I := 𝓡 n) V (terminalGermsOpenChartMap q hq V x),
    Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal
      (I := 𝓡 n) (terminalGermsOpenChartSource q hq V) x] at h
  ext v
  exact congrArg (fun A => A v) h

variable [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]

theorem terminalGerms_open_metric_readout
    (q : M → N) (hq : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ q)
    (V : Opens N) (g : RiemannianMetric n M) (gV : RiemannianMetric n V)
    (hread : ∀ (x : terminalGermsOpenChartSource q hq V)
      (a b : TangentSpace (𝓡 n) x),
      g.inner x.val
        (mfderiv (𝓡 n) (𝓡 n)
          (Subtype.val : terminalGermsOpenChartSource q hq V → M) x a)
        (mfderiv (𝓡 n) (𝓡 n)
          (Subtype.val : terminalGermsOpenChartSource q hq V → M) x b) =
      gV.inner (terminalGermsOpenChartMap q hq V x)
        (mfderiv (𝓡 n) (𝓡 n) (terminalGermsOpenChartMap q hq V) x a)
        (mfderiv (𝓡 n) (𝓡 n) (terminalGermsOpenChartMap q hq V) x b))
    (x : M) (hx : q x ∈ V) (a b : TangentSpace (𝓡 n) x) :
    g.inner x a b = gV.inner ⟨q x, hx⟩
      (mfderiv (𝓡 n) (𝓡 n) q x a) (mfderiv (𝓡 n) (𝓡 n) q x b) := by
  have h := hread ⟨x, hx⟩ a b
  have hs := Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal
    (I := 𝓡 n) (terminalGermsOpenChartSource q hq V) ⟨x, hx⟩
  rw [hs, terminalGerms_openChartMap_mfderiv] at h
  exact h

end PoincareConjecture.M47
