import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.ModelGeometry.Homogeneity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Transport.Canonical
import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

local instance : ChartedSpace RoundCylinderCoordinates RoundCylinderSpace :=
  prodChartedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere ℝ ℝ
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) RoundCylinderSpace :=
  RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
local instance : IsManifold (𝓡 3) ∞ RoundCylinderSpace :=
  RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)

namespace SphereLineProductData

variable {P : Type u} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) P] [IsManifold (𝓡 3) ∞ P]
  (B : SphereLineProductData (P := P))

local instance : TopologicalSpace B.surface := B.surface_topology
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 2)) B.surface := B.surface_charted
local instance : IsManifold (𝓡 2) ∞ B.surface := B.surface_manifold
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (B.surface × ℝ) := B.product_charted
local instance : IsManifold (𝓡 3) ∞ (B.surface × ℝ) := B.product_manifold

def normalizedCylinderDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3) RoundCylinderSpace (B.surface × ℝ) ∞ :=
  roundCylinderModelDiffeomorph.symm.trans B.canonicalProductDiffeomorph

theorem normalizedCylinderDiffeomorph_inner (z : RoundCylinderSpace)
    (v w : TangentSpace (𝓡 3) z) :
    (B.product_metric (-1)).inner (B.normalizedCylinderDiffeomorph z)
      (mfderiv (𝓡 3) (𝓡 3) B.normalizedCylinderDiffeomorph z v)
      (mfderiv (𝓡 3) (𝓡 3) B.normalizedCylinderDiffeomorph z w) =
      roundCylinderMetric.inner z v w := by
  let c := roundCylinderModelDiffeomorph
  let e := B.normalizedCylinderDiffeomorph
  let d := B.canonicalProductDiffeomorph
  obtain ⟨z, rfl⟩ := c.surjective z
  have hsurj : Function.Surjective
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) c z) :=
    (c.mfderivToContinuousLinearEquiv (by simp) z).surjective
  obtain ⟨v, rfl⟩ := hsurj v
  obtain ⟨w, rfl⟩ := hsurj w
  have heq : e ∘ c = d := by
    funext q
    exact congrArg d (c.symm_apply_apply q)
  have hd (u : RoundCylinderTangent z) :
      mfderiv (𝓡 3) (𝓡 3) e (c z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) c z u) =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) d z u := by
    have h := mfderiv_comp z (e.contMDiff.mdifferentiable (by simp) _)
      (c.contMDiff.mdifferentiable (by simp) _)
    rw [heq] at h
    exact (congrArg (fun f => f u) h).symm
  change (B.product_metric (-1)).inner (e (c z))
    (mfderiv (𝓡 3) (𝓡 3) e (c z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) c z v))
    (mfderiv (𝓡 3) (𝓡 3) e (c z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) c z w)) = _
  erw [hd v, hd w]
  rw [show e (c z) = d z from congrFun heq z]
  rw [B.canonicalProductDiffeomorph_inner (-1) (by norm_num)]
  convert (roundCylinderMetric_inner z v w).symm using 1 <;>
    norm_num [EvolvingRoundCylinderMetric] <;> rfl

variable [MeasurableSpace (B.surface × ℝ)] [BorelSpace (B.surface × ℝ)]
  [T3Space (B.surface × ℝ)]

theorem normalized_ball_volume (p : B.surface × ℝ) :
    (B.product_metric (-1)).volumeMeasure ((B.product_metric (-1)).ball p (1 / 4)) =
      ENNReal.ofReal universalNoncollapseModelVolume := by
  let e := B.normalizedCylinderDiffeomorph
  have hv := RiemannianMetric.volumeMeasure_ball_diffeomorph roundCylinderMetric
    (B.product_metric (-1)) e
    (fun z v w => (B.normalizedCylinderDiffeomorph_inner z v w).symm) (e.symm p) (1 / 4)
  rw [e.apply_symm_apply] at hv
  rw [← hv, roundCylinder_ball_volume_eq (e.symm p) universalNoncollapseModelPoint]
  exact (ENNReal.ofReal_toReal
    (roundCylinderMetric.volumeMeasure_ball_lt_top roundCylinderMetric_complete
      universalNoncollapseModelPoint (1 / 4)).ne).symm

end SphereLineProductData
end PoincareConjecture
