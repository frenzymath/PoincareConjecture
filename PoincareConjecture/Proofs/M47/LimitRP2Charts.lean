import PoincareConjecture.Definitions.M33BranchContinuation
import PoincareConjecture.Proofs.M44.Mathlib.SmoothImageInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

variable {G : GeneralizedRicciFlowData.{u}} {F : SurgeryFlowData.{u}}
  {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ}
  {I : Set ℝ} {U : Set C.carrier}

noncomputable def limitRP2CylinderSliceChart
    (e : GeneralizedFlowCylinder G C origin scale I U) (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ I) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier
      (G.slice (origin + s / scale)).carrier ∞ where
  toFun := e.forward s hs
  invFun := e.inverse s hs
  source := U
  target := e.forward s hs '' U
  map_source' _ hx := mem_image_of_mem _ hx
  map_target' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [e.left_inverse s hs hx]
    exact hx
  left_inv' _ hx := e.left_inverse s hs hx
  right_inv' _ hx := e.right_inverse s hs hx
  open_source := hU
  open_target := Poincare.isOpen_image_of_smooth_leftInvOn hU
    (e.forward_smooth s hs) (e.inverse_smooth s hs) (e.left_inverse s hs)
  contMDiffOn_toFun := e.forward_smooth s hs
  contMDiffOn_invFun := e.inverse_smooth s hs

noncomputable def limitRP2HistorySliceChart (R : M33RegularHistoryRealization G F)
    (t : ℝ) (ht : t ∈ G.interval) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) (G.slice t).carrier (F.slice t).carrier ∞ where
  toFun := R.forward t ht
  invFun := R.inverse t ht
  source := univ
  target := range (R.forward t ht)
  map_source' x _ := mem_range_self x
  map_target' _ _ := mem_univ _
  left_inv' x _ := R.left_inverse t ht x
  right_inv' _ hx := R.right_inverse t ht hx
  open_source := isOpen_univ
  open_target := (R.forward_openEmbedding t ht).isOpen_range
  contMDiffOn_toFun := (R.forward_smooth t ht).contMDiffOn
  contMDiffOn_invFun := R.inverse_smooth t ht

noncomputable def limitRP2PhysicalMap (e : GeneralizedFlowCylinder G C origin scale I U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval) :
    C.carrier → (F.slice (origin + s / scale)).carrier :=
  R.forward (origin + s / scale) ht ∘ e.forward s hs

theorem limitRP2PhysicalMap_isOpenEmbedding
    (e : GeneralizedFlowCylinder G C origin scale I U) (hU : IsOpen U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval) :
    Topology.IsOpenEmbedding (fun x : U => limitRP2PhysicalMap e R s hs ht x) := by
  exact (R.forward_openEmbedding (origin + s / scale) ht).comp
    (limitRP2CylinderSliceChart e hU s hs).toOpenPartialHomeomorph.isOpenEmbedding_restrict

theorem limitRP2PhysicalMap_injOn
    (e : GeneralizedFlowCylinder G C origin scale I U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval) :
    InjOn (limitRP2PhysicalMap e R s hs ht) U := by
  intro x hx y hy hxy
  exact (e.left_inverse s hs).injOn hx hy
    ((R.left_inverse (origin + s / scale) ht).injective hxy)

theorem limitRP2PhysicalMap_isLocalDiffeomorphAt
    (e : GeneralizedFlowCylinder G C origin scale I U) (hU : IsOpen U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval) {x : C.carrier} (hx : x ∈ U) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (limitRP2PhysicalMap e R s hs ht) x := by
  exact ((limitRP2CylinderSliceChart e hU s hs).isLocalDiffeomorphAt
    (𝓡 3) (𝓡 3) ∞ hx).comp (K := 𝓡 3) (P := _)
    ((limitRP2HistorySliceChart R (origin + s / scale) ht).isLocalDiffeomorphAt
      (𝓡 3) (𝓡 3) ∞ (mem_univ _))

end PoincareConjecture.M47
