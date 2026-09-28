import PoincareConjecture.Proofs.M60.Mathlib.ChartwiseRademacher
import PoincareConjecture.Definitions.M60Area

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]

theorem m60_ae_mdifferentiable_of_metric_lipschitzOn (g : RiemannianMetric n M)
    {f : LoopPlane → M} {S : Set LoopPlane} (hS : IsOpen S)
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x ∈ S, ∀ y ∈ S,
      g.edist (f x) (f y) ≤ ENNReal.ofReal L * ENNReal.ofReal ‖x - y‖) :
    ∀ᵐ x ∂volume, x ∈ S → MDifferentiableAt (𝓡 2) (𝓡 n) f x := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : IsRiemannianManifold (𝓡 n) M := ⟨fun _ _ => rfl⟩
  have hLip : LipschitzOnWith (NNReal.mk L hL) f S := by
    intro x hx y hy
    change g.edist (f x) (f y) ≤ _
    simpa only [edist_dist, dist_eq_norm, ENNReal.ofReal_eq_coe_nnreal hL] using hf x hx y hy
  exact M60.ae_mdifferentiableAt_of_lipschitzOn volume hS hLip

theorem m60_ae_mdifferentiable_of_disk_lipschitz (g : RiemannianMetric n M)
    {f : LoopPlane → M} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y : LoopDisk,
      g.edist (f x) (f y) ≤ ENNReal.ofReal L * ENNReal.ofReal ‖(x : LoopPlane) - y‖) :
    ∀ᵐ x ∂volume, x ∈ loopDiskSet → MDifferentiableAt (𝓡 2) (𝓡 n) f x := by
  have hinner : ∀ᵐ x ∂volume, x ∈ Metric.ball (0 : LoopPlane) 1 →
      MDifferentiableAt (𝓡 2) (𝓡 n) f x :=
    m60_ae_mdifferentiable_of_metric_lipschitzOn g Metric.isOpen_ball hL
      (fun x hx y hy => hf ⟨x, Metric.ball_subset_closedBall hx⟩
        ⟨y, Metric.ball_subset_closedBall hy⟩)
  filter_upwards [hinner,
    compl_mem_ae_iff.mpr (Measure.addHaar_sphere volume (0 : LoopPlane) 1)] with x hx hcircle hxd
  apply hx
  have hle : ‖x‖ ≤ 1 := by
    simpa only [loopDiskSet, Metric.mem_closedBall, dist_zero_right] using hxd
  have hne : ‖x‖ ≠ 1 := by
    simpa only [mem_compl_iff, Metric.mem_sphere, dist_zero_right] using hcircle
  simpa only [Metric.mem_ball, dist_zero_right] using lt_of_le_of_ne hle hne

end PoincareConjecture
