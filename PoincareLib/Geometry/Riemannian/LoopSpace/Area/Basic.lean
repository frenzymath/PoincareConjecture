import PoincareLib.Topology.Homotopy.LoopSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Lipschitz spanning disks and Riemannian filling area

Adapted from Mapher commit f927d9e1f0810042766d3b5f64d3f4da02ee93cc.
Source: Morgan--Tian, Definition 18.17 and Lemma 18.27, pp. 430, 434-435.
-/

set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology ENNReal unitInterval
universe u
namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- The circle is the boundary of the chosen disk. -/
def loopBoundary : Set LoopPlane := {z | ‖z‖ = 1}

/-- The metric Jacobian density of a parametrized two-dimensional map. -/
noncomputable def parametrizedAreaDensity (g : RiemannianMetric 3 M)
    (f : LoopPlane → M) (z : LoopPlane) : ℝ :=
  let d := mfderiv (𝓡 2) (𝓡 3) f z
  let e : Fin 2 → TangentSpace (𝓡 3) (f z) :=
    fun i => d (EuclideanSpace.basisFun (Fin 2) ℝ i)
  Real.sqrt (max 0 (Matrix.det (fun i j => g.inner (f z) (e i) (e j))))

/-- Parametrized Riemannian area, integrated over the unit disk. -/
noncomputable def parametrizedRiemannianArea (g : RiemannianMetric 3 M)
    (f : LoopPlane → M) : ℝ :=
  ∫ z in loopDiskSet, parametrizedAreaDensity g f z ∂MeasureTheory.volume

/-- A Lipschitz spanning disk for a C¹ loop.  Boundary equality is allowed up
to the explicit circle homeomorphism carried by `reparameterization`. -/
structure LipschitzSpanningDisk (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) where
  map : LoopPlane → M
  continuous_on_disk : ContinuousOn map loopDiskSet
  /-- The metric Jacobian is evaluated at the a.e. differentiability locus of
  the Lipschitz parametrization. -/
  ae_manifold_differentiable : ∀ᵐ z ∂MeasureTheory.volume,
    z ∈ loopDiskSet → MDifferentiableAt (𝓡 2) (𝓡 3) map z
  reparameterization : CircleReparameterization
  boundary_eq : ∀ z : LoopCircle,
    map z = γ (reparameterization.map z)
  lipschitz_constant : ℝ
  lipschitz_nonnegative : 0 ≤ lipschitz_constant
  lipschitz_on_disk : ∀ x y : LoopDisk,
    g.edist (map x) (map y) ≤
      ENNReal.ofReal lipschitz_constant * ENNReal.ofReal ‖(x : LoopPlane) - y‖
  area_integrable : MeasureTheory.IntegrableOn
    (parametrizedAreaDensity g map) loopDiskSet MeasureTheory.volume
  area_nonnegative : 0 ≤ parametrizedRiemannianArea g map

namespace LipschitzSpanningDisk

noncomputable def area {g : RiemannianMetric 3 M}
    {γ : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g γ) : ℝ :=
  parametrizedRiemannianArea g D.map

end LipschitzSpanningDisk

/-- The nonempty admissible filling class and its finite-area witness. -/
structure FillingAreaData (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) where
  nonempty : Nonempty (LipschitzSpanningDisk g γ)
  finite_witness : ∃ D : LipschitzSpanningDisk g γ, ∃ C : ℝ, D.area ≤ C
  bounded_below : BddBelow (Set.range (fun D : LipschitzSpanningDisk g γ => D.area))

/-- Infimum of the areas of all admissible Lipschitz spanning disks. -/
noncomputable def fillingArea (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) : ℝ :=
  sInf (Set.range (fun D : LipschitzSpanningDisk g γ => D.area))


end PoincareMT
