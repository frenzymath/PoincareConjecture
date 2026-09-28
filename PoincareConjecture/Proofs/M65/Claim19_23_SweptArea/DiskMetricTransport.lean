import PoincareConjecture.Proofs.M65.Mathlib.AreaDensityMeasurable
import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.DistanceTransport

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)} {K0 K1 K2 : ℝ}

theorem m65Disk_newMetric_integrable
    (bounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    {gamma : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk (F.metric s) gamma) :
    IntegrableOn (parametrizedAreaDensity (F.metric t) D.map) loopDiskSet volume := by
  have hmeas := m65AreaDensity_aestronglyMeasurable (F.metric t)
    (isCompact_closedBall (0 : LoopPlane) 1) D.continuous_on_disk D.ae_manifold_differentiable
  exact (D.area_integrable.const_mul (Real.exp ((2 * K2) * |t - s|))).mono_nonneg hmeas
    (Eventually.of_forall (fun _ => Real.sqrt_nonneg _))
    (Eventually.of_forall (m65FlowAreaDensity_scaling F bounds hs ht D.map))

noncomputable def m65TransportSpanningDisk
    (bounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    {gamma : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk (F.metric s) gamma) :
    LipschitzSpanningDisk (F.metric t) gamma where
  map := D.map
  continuous_on_disk := D.continuous_on_disk
  ae_manifold_differentiable := D.ae_manifold_differentiable
  reparameterization := D.reparameterization
  boundary_eq := D.boundary_eq
  lipschitz_constant := Real.exp (K2 * |t - s|) * D.lipschitz_constant
  lipschitz_nonnegative := mul_nonneg (Real.exp_nonneg _) D.lipschitz_nonnegative
  lipschitz_on_disk := by
    intro x y
    have hdist := m65FlowEdist_comparison F bounds hs ht (D.map x) (D.map y)
    calc
      _ ≤ ENNReal.ofReal (Real.exp (K2 * |t - s|)) *
          (ENNReal.ofReal D.lipschitz_constant * ENNReal.ofReal ‖(x : LoopPlane) - y‖) :=
        hdist.trans (mul_le_mul_right (D.lipschitz_on_disk x y) _)
      _ = _ := by rw [ENNReal.ofReal_mul (Real.exp_nonneg _), mul_assoc]
  area_integrable := m65Disk_newMetric_integrable bounds hs ht D
  area_nonnegative := integral_nonneg (fun _ => Real.sqrt_nonneg _)

theorem m65TransportSpanningDisk_area_le
    (bounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    {gamma : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk (F.metric s) gamma) :
    (m65TransportSpanningDisk bounds hs ht D).area ≤
      Real.exp ((2 * K2) * |t - s|) * D.area :=
  m65FlowArea_scaling F bounds hs ht D.map loopDiskSet D.area_integrable
    (m65Disk_newMetric_integrable bounds hs ht D)

end PoincareConjecture
