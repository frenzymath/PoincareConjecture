import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Event.Area
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.LipschitzDiskArea
import PoincareConjecture.Definitions.M59LoopIdentification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

variable {M N : Type u}
  [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace N] [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]

noncomputable def m67PostcomposeDisk [T2Space M] [T2Space N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (f : ContinuousMap M N) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (post : M59LoopPostcomposition f)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ x y, h.edist (f x) (f y) ≤ ENNReal.ofReal L * g.edist x y)
    {gamma : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g gamma) :
    LipschitzSpanningDisk h (post.map gamma) := by
  have hLip : ∀ x y : LoopDisk,
      h.edist ((f ∘ D.map) x) ((f ∘ D.map) y) ≤
        ENNReal.ofReal (L * D.lipschitz_constant) *
          ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
    intro x y
    calc
      _ ≤ ENNReal.ofReal L * g.edist (D.map x) (D.map y) := hbound _ _
      _ ≤ ENNReal.ofReal L *
          (ENNReal.ofReal D.lipschitz_constant * ENNReal.ofReal ‖(x : LoopPlane) - y‖) :=
        mul_le_mul_right (D.lipschitz_on_disk x y) _
      _ = _ := by rw [ENNReal.ofReal_mul hL, mul_assoc]
  exact {
    map := f ∘ D.map
    continuous_on_disk := f.continuous.comp_continuousOn D.continuous_on_disk
    ae_manifold_differentiable := by
      filter_upwards [D.ae_manifold_differentiable] with z hz
      intro hzd
      exact (hf.mdifferentiable (by simp) (D.map z)).comp z (hz hzd)
    reparameterization := D.reparameterization
    boundary_eq := by
      intro z
      change f (D.map z) = (post.map gamma) (D.reparameterization.map z)
      rw [D.boundary_eq, ← (post.map gamma).boundary, post.extension_agreement,
        gamma.boundary]
    lipschitz_constant := L * D.lipschitz_constant
    lipschitz_nonnegative := mul_nonneg hL D.lipschitz_nonnegative
    lipschitz_on_disk := hLip
    area_integrable := m60AreaDensity_integrableOn_of_disk_lipschitz h
      (mul_nonneg hL D.lipschitz_nonnegative) hLip
    area_nonnegative := integral_nonneg (fun _ => Real.sqrt_nonneg _) }

theorem m67PostcomposeDisk_area_le [T2Space M] [T2Space N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (f : ContinuousMap M N) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (post : M59LoopPostcomposition f)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ x y, h.edist (f x) (f y) ≤ ENNReal.ofReal L * g.edist x y)
    {gamma : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g gamma) :
    (m67PostcomposeDisk g h f hf post hL hbound D).area ≤ L ^ 2 * D.area := by
  change (∫ z in loopDiskSet, parametrizedAreaDensity h (f ∘ D.map) z) ≤
    L ^ 2 * ∫ z in loopDiskSet, parametrizedAreaDensity g D.map z
  rw [← integral_const_mul]
  apply integral_mono_ae (m67PostcomposeDisk g h f hf post hL hbound D).area_integrable
    (D.area_integrable.const_mul (L ^ 2))
  filter_upwards [ae_restrict_of_ae D.ae_manifold_differentiable,
    ae_restrict_mem (show MeasurableSet loopDiskSet from Metric.isClosed_closedBall.measurableSet)] with z hz hzd
  exact m67_area_density_comp_le g h (hf.mdifferentiable (by simp)) hL hbound (hz hzd)

theorem m67_filling_transport_of_lipschitz [T2Space M] [T2Space N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (f : ContinuousMap M N) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (post : M59LoopPostcomposition f)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ x y, h.edist (f x) (f y) ≤ ENNReal.ofReal L * g.edist x y)
    (gamma : C1FreeLoopSpace (M := M)) (D : LipschitzSpanningDisk g gamma) :
    ∃ E : LipschitzSpanningDisk h (post.map gamma), E.area ≤ L ^ 2 * D.area :=
  ⟨m67PostcomposeDisk g h f hf post hL hbound D,
    m67PostcomposeDisk_area_le g h f hf post hL hbound D⟩

theorem m67_filling_transport_of_distance_bound [T2Space M] [T2Space N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (f : ContinuousMap M N) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (post : M59LoopPostcomposition f)
    {eta : ℝ} (heta : 0 < eta)
    (hbound : ∀ x y, h.edist (f x) (f y) ≤
      ENNReal.ofReal (1 + eta) * g.edist x y)
    (gamma : C1FreeLoopSpace (M := M)) (D : LipschitzSpanningDisk g gamma) :
    ∃ E : LipschitzSpanningDisk h (post.map gamma), E.area ≤ (1 + eta) ^ 2 * D.area := by
  have hL : 0 ≤ 1 + eta := by linarith
  exact ⟨m67PostcomposeDisk g h f hf post hL hbound D,
    m67PostcomposeDisk_area_le g h f hf post hL hbound D⟩

theorem m67_null_transport_of_postcomposition
    (f : ContinuousMap M N) (post : M59LoopPostcomposition f)
    (gamma : C1FreeLoopSpace (M := M)) (hgamma : IsNullHomotopicLoop gamma) :
    IsNullHomotopicLoop (post.map gamma) := by
  obtain ⟨d, hd, hboundary⟩ := hgamma
  refine ⟨f ∘ d, f.continuous.comp hd, ?_⟩
  intro z
  change f (d z) = (post.map gamma) z
  rw [hboundary, ← (post.map gamma).boundary, post.extension_agreement, gamma.boundary]

end PoincareConjecture
