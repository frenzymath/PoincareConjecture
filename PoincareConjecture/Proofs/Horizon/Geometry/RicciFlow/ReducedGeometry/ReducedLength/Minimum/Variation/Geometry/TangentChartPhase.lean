import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.ChartFrame
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

noncomputable def tangentChartPhase (p : M) (q : TangentBundle (𝓡 n) M) : V × V :=
  ((chartAt V p) q.proj, (mfderiv (𝓡 n) (𝓡 n) (chartAt V p) q.proj) q.2)

theorem tangentChartPhase_continuousOn (p : M) :
    ContinuousOn (tangentChartPhase (n := n) p)
      {q : TangentBundle (𝓡 n) M | q.proj ∈ (chartAt V p).source} := by
  have hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (chartAt V p) (chartAt V p).source :=
    contMDiffOn_chart
  have ht := hc.continuousOn_tangentMapWithin (by simp)
    (chartAt V p).open_source.uniqueMDiffOn
  have h := (tangentBundleModelSpaceHomeomorph (𝓡 n)).continuous.comp_continuousOn ht
  apply h.congr
  intro q hq
  change ((chartAt V p) q.proj, (mfderiv (𝓡 n) (𝓡 n) (chartAt V p) q.proj) q.2) =
    ((chartAt V p) q.proj,
      (mfderivWithin (𝓡 n) (𝓡 n) (chartAt V p) (chartAt V p).source q.proj) q.2)
  rw [mfderivWithin_of_isOpen (chartAt V p).open_source hq]

theorem tangentChartPhase_inverse (p : M) (q : TangentBundle (𝓡 n) M)
    (hq : q.proj ∈ (chartAt V p).source) :
    (⟨(chartAt V p).symm (tangentChartPhase p q).1,
      (mfderiv (𝓡 n) (𝓡 n) (chartAt V p).symm (tangentChartPhase p q).1)
        (tangentChartPhase p q).2⟩ : TangentBundle (𝓡 n) M) = q := by
  rcases q with ⟨x, v⟩
  apply Bundle.TotalSpace.ext ((chartAt V p).left_inv hq)
  apply heq_of_eq
  exact congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x ↦ L v)
    ((mdifferentiable_chart (I := 𝓡 n) p).symm_comp_deriv hq)

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
