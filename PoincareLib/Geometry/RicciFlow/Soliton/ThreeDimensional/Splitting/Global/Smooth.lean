import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Orientation
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.SmoothCover

/-!
# Smooth metric data on the rank-one cover

`SmoothCover` constructs the atlas and pullback metric from an actual
covering-map input.  This wrapper packages the resulting local diffeomorphism,
metric, smooth deck diffeomorphism, and deck isometry alongside the intrinsic
cover certificate.  No global product coordinate is introduced here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.RicciFlow.Splitting

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

/-- Smooth geometric data canonically induced on the unit-kernel cover. -/
theorem nullOrientationCover_smooth_data
    {D : LeviCivitaData g} (C : NullOrientationCover D) :
    letI := unitRicciKernelChartedSpace D C.covering
    letI := unitRicciKernelIsManifold D C.covering
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
        (unitRicciKernelProjection D) ∧
      Nonempty (RiemannianMetric 3 (UnitRicciKernel D)) ∧
      ∃ e : Diffeomorph (𝓡 3) (𝓡 3)
          (UnitRicciKernel D) (UnitRicciKernel D) ∞,
        ∀ (p : UnitRicciKernel D)
          (v w : TangentSpace (𝓡 3) p),
          (unitRicciKernelMetric D C.covering).inner (e p)
              (mfderiv (𝓡 3) (𝓡 3) e p v)
              (mfderiv (𝓡 3) (𝓡 3) e p w) =
            (unitRicciKernelMetric D C.covering).inner p v w := by
  let := unitRicciKernelChartedSpace D C.covering
  let := unitRicciKernelIsManifold D C.covering
  refine ⟨unitRicciKernelProjection_isLocalDiffeomorph D C.covering,
    ⟨unitRicciKernelMetric D C.covering⟩, ?_⟩
  refine ⟨unitRicciKernelDeckDiffeomorph D C.covering, ?_⟩
  exact unitRicciKernelReverse_preserves_metric D C.covering

end PoincareMT.RicciFlow.Splitting
