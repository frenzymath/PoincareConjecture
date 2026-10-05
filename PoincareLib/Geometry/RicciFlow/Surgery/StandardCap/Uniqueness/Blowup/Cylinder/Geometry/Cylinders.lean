import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.OrdinaryRealization.GeneralizedFlow
import PoincareLib.Geometry.Spacetime.Rescaling.Time
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Exact normalized cylinders in the ordinary realization

Morgan-Tian, Theorem 12.28, printed pp. 323-324, through Chapter 11's
controlled limits. The affine source clock remains inside the actual
ordinary time interval; no value outside that interval extends a worldline.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M35.OrdinaryRealization

/-- The inverse parabolic clock embeds any retained normalized time domain.
Used in Theorem 12.28, pp. 323-324. -/
theorem clock_embedding {J I : Set ℝ} {a Q : ℝ} (hQ : 0 < Q)
    (htime : ∀ s ∈ I, a + s / Q ∈ J) :
    Topology.IsEmbedding (fun s : I => (⟨a + s.val / Q, htime s.val s.property⟩ : J)) := by
  apply Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
  exact (parabolicTimeOrderIso Q hQ a).symm.toHomeomorph.isEmbedding.comp
    Topology.IsEmbedding.subtypeVal

/-- The exact Chapter 11 cylinder over a retained spatial set and normalized time domain.
Used in Theorem 12.28, pp. 323-324. -/
noncomputable def cylinder {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    (a Q : ℝ) (hQ : 0 < Q) (I : Set ℝ) (U : Set StandardCapSpace)
    (htime : ∀ s ∈ I, a + s / Q ∈ J) :
    GeneralizedFlowCylinder (generalizedFlow F) capCarrier a Q I U where
  scale_pos := hQ
  forward s hs := (sliceDiffeomorph (htime s hs)).symm
  inverse s hs := sliceDiffeomorph (htime s hs)
  forward_smooth s hs := (sliceDiffeomorph (htime s hs)).symm.contMDiff.contMDiffOn
  inverse_smooth s hs := (sliceDiffeomorph (htime s hs)).contMDiff.contMDiffOn
  left_inverse s hs _ _ := (sliceDiffeomorph (htime s hs)).apply_symm_apply _
  right_inverse s hs _ _ := (sliceDiffeomorph (htime s hs)).symm_apply_apply _
  embedding := by
    let : TopologicalSpace (Σ t : ℝ, (slice J t).carrier) := spacetimeTopology J
    exact (spacetimeHomeomorph J).symm.isEmbedding.comp
      ((clock_embedding hQ htime).prodMap Topology.IsEmbedding.subtypeVal)
  vertical_compatibility _ _ x _ := by
    refine ⟨(), x, 1, zero_lt_one, ?_⟩
    intro s hs _
    exact ⟨htime s hs, rfl⟩

/-- The normalized cylinder metric is Q times the actual ordinary metric at a+s/Q.
Used in Theorem 12.28, pp. 323-324. -/
theorem cylinder_pullbackInner {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    (a Q : ℝ) (hQ : 0 < Q) (I : Set ℝ) (U : Set StandardCapSpace)
    (htime : ∀ s ∈ I, a + s / Q ∈ J) (s : ℝ) (hs : s ∈ I)
    (x : StandardCapSpace) (v w : TangentSpace (𝓡 3) x) :
    (cylinder F a Q hQ I U htime).pullbackInner s hs x v w =
      Q * (F.metric (a + s / Q)).inner x v w := by
  exact congrArg (fun r : ℝ => Q * r) (metric_pullback F (htime s hs) x v w)

end PoincareMT.M35.OrdinaryRealization
