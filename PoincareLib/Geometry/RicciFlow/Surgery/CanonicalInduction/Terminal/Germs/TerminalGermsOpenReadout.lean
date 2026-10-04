import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Terminal.Germs.TerminalGermsOpenCharts
import PoincareLib.Geometry.Manifold.RegularLevel.OpenInclusion

/-!
# Original tangent readouts on an open target

The inherited open-submanifold charts make the actual inclusion
differential the identity. The literal restriction square consequently
retains the original chart differential and metric readout.
Source: MT Proposition 5.14, pp. 90-91;
derivations/terminal-germs-overlap.md, Stage A5j3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareMT.M47

variable {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]

/-- The differential of the actual restricted chart map is the
original differential in the inherited tangent coordinates. -/
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

/-- An actual restricted-chart metric identity reads the same original
metric and original differential at every source point over the target. -/
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

end PoincareMT.M47
