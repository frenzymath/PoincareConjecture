import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Transport
import Mathlib.Topology.Homeomorph.Lemmas



open scoped Manifold ContDiff

universe v u

namespace Poincare.Manifold


@[instance_reducible]
def uliftChartedSpace (H : Type*) [TopologicalSpace H]
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M] :
    ChartedSpace H (ULift.{v} M) :=
  HomeomorphTransport.chartedSpace (H := H) Homeomorph.ulift.symm

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


theorem uliftIsManifold :
    letI : ChartedSpace H (ULift.{v} M) := uliftChartedSpace H M
    IsManifold I ∞ (ULift.{v} M) := by
  let : ChartedSpace H (ULift.{v} M) := uliftChartedSpace H M
  exact HomeomorphTransport.isManifold Homeomorph.ulift.symm I ∞


def uliftDiffeomorph :
    letI : ChartedSpace H (ULift.{v} M) := uliftChartedSpace H M
    Diffeomorph I I (ULift.{v} M) M ∞ := by
  letI : ChartedSpace H (ULift.{v} M) := uliftChartedSpace H M
  exact (HomeomorphTransport.diffeomorph Homeomorph.ulift.symm I ∞).symm

@[simp] theorem uliftDiffeomorph_apply (x : ULift.{v} M) :
    letI : ChartedSpace H (ULift.{v} M) := uliftChartedSpace H M
    uliftDiffeomorph I M x = x.down := rfl

@[simp] theorem uliftDiffeomorph_symm_apply (x : M) :
    letI : ChartedSpace H (ULift.{v} M) := uliftChartedSpace H M
    (uliftDiffeomorph I M).symm x = ULift.up.{v} x := rfl

theorem uliftDiffeomorph_toEquiv :
    letI : ChartedSpace H (ULift.{v} M) := uliftChartedSpace H M
    (uliftDiffeomorph I M).toEquiv = Equiv.ulift.{v, u} := rfl

end Poincare.Manifold
