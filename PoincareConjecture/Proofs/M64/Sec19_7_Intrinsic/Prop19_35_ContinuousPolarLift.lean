import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PolarInverse











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem m64Intrinsic_contDiffOn_boundary_lift
    {e : AnnulusCoordinates → AnnulusCoordinates} {U : Set AnnulusCoordinates}
    (hU : IsOpen U) (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U)
    {u : ℝ → AnnulusCoordinates} {J : Set ℝ} {radius : ℝ}
    (hu : ContinuousOn u J) (humap : MapsTo u J U)
    (hboundary : ∀ s ∈ J, e (u s) = intrinsicAnnulusBoundary radius s)
    (hi : ∀ s ∈ J, Function.Injective (mfderiv (𝓡 2) (𝓡 2) e (u s))) :
    ContDiffOn ℝ ∞ u J := by
  intro s hs
  obtain ⟨F, hsF, _, hF, _, hFi⟩ :=
    m64Intrinsic_exists_smooth_polar_inverse hU he (humap hs) (hi s hs)
  have htarget : intrinsicAnnulusBoundary radius s ∈ F.target := by
    rw [← hboundary s hs, ← hF]
    exact F.map_source hsF
  have hlocal : ContDiffAt ℝ ∞ (F.symm ∘ intrinsicAnnulusBoundary radius) s :=
    (hFi.contDiffAt (F.open_target.mem_nhds htarget)).comp s
      (m64Intrinsic_contDiff_boundary radius).contDiffAt
  have hsource : ∀ᶠ t in 𝓝[J] s, u t ∈ F.source :=
    (hu s hs).preimage_mem_nhdsWithin (F.open_source.mem_nhds hsF)
  have heq : u =ᶠ[𝓝[J] s] F.symm ∘ intrinsicAnnulusBoundary radius := by
    filter_upwards [hsource, self_mem_nhdsWithin] with t ht htJ
    change u t = F.symm (intrinsicAnnulusBoundary radius t)
    rw [← hboundary t htJ, ← hF, F.left_inv ht]
  apply hlocal.contDiffWithinAt.congr_of_eventuallyEq heq
  change u s = F.symm (intrinsicAnnulusBoundary radius s)
  rw [← hboundary s hs, ← hF, F.left_inv hsF]

end PoincareConjecture
