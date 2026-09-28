import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.Differential
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.Proofs.M15

theorem compatibleCylinder_horizontalDerivative_lift
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    {time : X → ℝ} {I K : SpacetimeInterval}
    {F : GeneralizedFlowSpacetime n X time I}
    {D : SmoothSpacetimeInterval K}
    {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C]
    (e : CompatibleSpacetimeCylinder F D C)
    (g : SpacetimeCylinderMetric e)
    {J : Set ℝ} {s : ℝ} (L : ℝ → D.Point × C)
    (hL : MDifferentiableWithinAt 𝓘(ℝ) (spacetimeModel n) L J s)
    (hJ : UniqueDiffWithinAt ℝ J s) :
    g.spatialTangentEquiv (L s).1 (L s).2
      (mfderivWithin 𝓘(ℝ) (𝓡 n) (fun r => (L r).2) J s 1) =
      F.horizontalProjection (e.toSpacetime (L s))
        (mfderivWithin 𝓘(ℝ) (spacetimeModel n) (e.toSpacetime ∘ L) J s 1) := by
  let w := mfderivWithin 𝓘(ℝ) (spacetimeModel n) L J s 1
  let a : ℝ := D.inclusionDerivative (L s).1 w.1
  have htime : w.1 = a • D.positiveTangent (L s).1 := by
    calc
      w.1 = (D.inclusionDerivative (L s).1).symm a :=
        ((D.inclusionDerivative (L s).1).symm_apply_apply w.1).symm
      _ = a • D.positiveTangent (L s).1 := by
        change (D.inclusionDerivative (L s).1).symm a =
          a • (D.inclusionDerivative (L s).1).symm 1
        simpa only [smul_eq_mul, mul_one] using
          (D.inclusionDerivative (L s).1).symm.map_smul a (1 : ℝ)
  have hspatial : mfderivWithin 𝓘(ℝ) (𝓡 n) (fun r => (L r).2) J s 1 = w.2 := by
    have h := mfderiv_comp_mfderivWithin s
      (mdifferentiableAt_snd (I := 𝓡∂ 1) (I' := 𝓡 n)) hL hJ.uniqueMDiffWithinAt
    have hh := congrArg (fun A => A (1 : ℝ)) h
    rw [mfderiv_snd] at hh
    exact hh
  have hcomp : mfderivWithin 𝓘(ℝ) (spacetimeModel n) (e.toSpacetime ∘ L) J s 1 =
      mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (L s) w := by
    exact congrArg (fun A => A (1 : ℝ))
      (mfderiv_comp_mfderivWithin s
        (e.smooth.mdifferentiableAt (by simp)) hL hJ.uniqueMDiffWithinAt)
  have hw : w = (a • D.positiveTangent (L s).1, w.2) := Prod.ext htime rfl
  rw [hspatial, hcomp, hw]
  have h := movingGauge_projection_eq e.toMovingSpacetimeGauge
    g.toMovingSpacetimeGaugeGeometry (L s).1 (L s).2 a w.2
  rw [compatibleMovingGaugeDrift_zero, smul_zero, sub_zero] at h
  exact h.symm

end PoincareConjecture.Proofs.M15
