import PoincareConjecture.Proofs.M47.BlowupControlsCapScalarUpper
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CylinderCurvature
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_PinchingBound
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_SmallHeight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

theorem cap_normalized_curvature_bound
    (P : M44CapPersistencePredecessors.{u})
    {F : SurgeryFlowData.{u}} (hpinch : SurgeryFlowPinched F)
    {t : ℝ} {J : Set ℝ} {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
    (hU : IsOpen U)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) StandardCapSpace (F.slice t).carrier ∞)
    (hmap : f.target ⊆ U) (G : M44.CylinderRicciFlow e f)
    (hsmall : (F.parameters.h t) ^ 2 ≤ 1) {K : ℝ}
    (hscalar : ∀ s (hs : s ∈ J) x, x ∈ U →
      (F.parameters.h t) ^ 2 *
        (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
          (e.forward s hs x) ≤ K) :
    ∀ s ∈ J, ∀ y, (G.flow.connection s).curvatureTensorNorm y ≤
      13 * max K (Real.exp 4) := by
  intro s hs y
  have htime : t + s / ((F.parameters.h t)⁻¹ ^ 2) ∈ F.time_domain :=
    e.time_subset (mem_image_of_mem _ hs)
  have hbound := hpinch.cap_curvature_norm_le P htime hsmall
    (M44.cylinderTargetTransport e f s hs y) (hscalar s hs y.1 (hmap y.2))
  rw [G.curvatureTensorNorm_eq hU hmap s hs y]
  simpa only [inv_pow, div_inv_eq_mul, mul_comm] using hbound

end PoincareConjecture.M47
