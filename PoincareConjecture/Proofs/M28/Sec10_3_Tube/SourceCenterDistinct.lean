import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMinimizerSubsegments
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceEdgeCommonOrientation











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]



theorem intrinsicEDist_self_of_mem (g : RiemannianMetric 3 M)
    {U : Set M} {x : M} (hx : x ∈ U) : intrinsicEDist g U x x = 0 := by
  apply le_antisymm ?_ (show (0 : ℝ≥0∞) ≤ intrinsicEDist g U x x from zero_le)
  have h := intrinsicEDist_le_pathELength g
    (γ := fun _ : ℝ => x) (a := 0) (b := 0) le_rfl contMDiffOn_const
    (fun _ _ => hx)
  simpa only [RiemannianMetric.pathELength, Manifold.pathELength_self] using h




theorem SourceEdgeCommonOrientationPacket.center_ne_later_center
    {g : RiemannianMetric 3 M} {N raw Q P : EpsilonNeck g}
    {γ : ℝ → M} {a b tN tQ tP : ℝ}
    (H : SourceEdgeCommonOrientationPacket N raw Q (γ := γ) tN tQ)
    {U : Set M} (haN : a ≤ tN) (hNQ : tN < tQ) (hQP : tQ ≤ tP)
    (hPb : tP ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hfinite : g.pathELength γ a b ≠ ⊤)
    (hmin : g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b))
    (hcP : γ tP = P.center) : N.center ≠ P.center := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hNP : tN ≤ tP := hNQ.le.trans hQP
  have hfirst : ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      g.pathELength γ tN tQ := by
    apply H.center_distance.1.trans
    exact Manifold.riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc haN (hQP.trans hPb))) H.center_N H.center_Q hNQ.le
  have hcoefficient : 0 < (0.99 : ℝ) * N.scale * N.epsilon⁻¹ :=
    mul_pos (mul_pos (by norm_num) N.scale_pos) (inv_pos.mpr N.epsilon_pos)
  have hpositive : 0 < g.pathELength γ tN tP :=
    (ENNReal.ofReal_pos.mpr hcoefficient).trans_le
      (hfirst.trans (Manifold.pathELength_mono le_rfl hQP))
  intro hcenters
  have hxU : γ tN ∈ U := hγU ⟨haN, hNP.trans hPb⟩
  have hsame : γ tP = γ tN := hcP.trans (hcenters.symm.trans H.center_N.symm)
  have hsub := pathELength_eq_intrinsicEDist_subsegment g haN hNP hPb
    hγ hγU hfinite hmin
  rw [hsame, intrinsicEDist_self_of_mem g hxU] at hsub
  exact (ne_of_gt hpositive) hsub

end PoincareConjecture.M28
