import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightTubeTransport
import Mathlib.Geometry.Manifold.MFDeriv.Atlas












set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



theorem IsCollarEmbedding.postcompose_diffeomorph
    {psi : UnitTwoSphere × ℝ → E3} (hpsi : IsCollarEmbedding psi)
    (G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) :
    IsCollarEmbedding (fun p => G (psi p)) := by
  refine ⟨G.contMDiff.comp_contMDiffOn hpsi.1, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hpsi.2.1 hx hy (G.injective hxy)
  · intro p hp
    have hdpsi := (hpsi.1.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds hp)).mdifferentiableAt (by simp)
    have hdG := (G.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
      (x := psi p) (mem_univ _)
    change Function.Injective
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ((G : E3 → E3) ∘ psi) p)
    rw [mfderiv_comp p (G.mdifferentiable (by simp) (psi p)) hdpsi]
    exact hdG.comp (hpsi.2.2 p hp)

variable {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}




noncomputable def SurgeryCapTag.heightCompress
    (C : SurgeryCapTag psi u)
    (h : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    (G0 G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
    (k R o w : ℝ) (hk : 0 < k)
    (ho : 0 < o) (hoo : o ≤ C.overlapWidth)
    (hw : 0 < w) (hww : w ≤ C.collarWidth)
    (hG0 : ∀ y : E3, ⟪(u : E3), G0 y⟫_ℝ = h ⟪(u : E3), y⟫_ℝ)
    (haff : ∀ z : ℝ, |z - C.cutHeight| ≤ R →
      h z = h C.cutHeight + k * (z - C.cutHeight))
    (hcap : ∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 < o →
      |C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model q).2) -
        C.cutHeight| ≤ R)
    (hcol : ∀ s : ℝ, |s| < w →
      |C.cutHeight + C.sign * (C.removal - C.scale) + C.beta * s - C.cutHeight| ≤ R)
    (hag : EqOn G G0 (C.tube ''
      (closedBall (0 : E2) 1 ×ˢ closedBall C.cutHeight R))) :
    SurgeryCapTag (fun p => G (psi p)) u := by
  exact {
    profile := C.profile
    cutHeight := h C.cutHeight
    removal := k * C.removal
    scale := k * C.scale
    sign := C.sign
    removal_pos := mul_pos hk C.removal_pos
    scale_pos := mul_pos hk C.scale_pos
    sign_abs := C.sign_abs
    scale_small := by
      calc
        (k * C.scale) * C.profile.heightBound = k * (C.scale * C.profile.heightBound) :=
          mul_assoc _ _ _
        _ < k * (C.removal / 4) := mul_lt_mul_of_pos_left C.scale_small hk
        _ = (k * C.removal) / 4 := by ring
    tube := heightTransportTube C.tube h G0
    tube_source := heightTransportTube_closedDisc_source C.tube h G0 C.tube_source
    tube_smooth := heightTransportTube_contDiffOn C.tube h G0 C.tube_smooth
    tube_inverse := heightTransportTube_contDiffOn_symm C.tube h G0 C.tube_inverse
    tube_height := heightTransportTube_height C.tube h G0 u u C.tube_height hG0
    sourceChart := C.sourceChart
    source_smooth := C.source_smooth
    source_inverse := C.source_inverse
    overlapWidth := o
    overlap_pos := ho
    overlap_le := hoo.trans C.overlap_le
    source_band := fun q hq => C.source_band q (lt_of_lt_of_le hq hoo)
    central_eq := by
      intro q hq
      have hheight :
          h (C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model q).2)) =
            h C.cutHeight + C.sign * (k * C.removal + k * C.scale * (C.profile.model q).2) :=
        (haff _ (hcap q hq)).trans (by ring)
      change G (psi (C.sourceChart q, 0)) = heightTransportTube C.tube h G0
        ((C.profile.model q).1,
          h C.cutHeight + C.sign * (k * C.removal + k * C.scale * (C.profile.model q).2))
      rw [C.central_eq q (lt_of_lt_of_le hq hoo), SurgeryCapProfile.capMap_apply,
        ← hheight, heightTransportTube_apply, h.symm_apply_apply]
      apply hag
      refine ⟨_, ⟨?_, ?_⟩, rfl⟩
      · simpa only [mem_closedBall, dist_zero_right] using C.profile.model_fst_norm_le q
      · simpa only [mem_closedBall, Real.dist_eq] using hcap q hq
    flatChart := C.flatChart
    flat_source := C.flat_source
    flat_smooth := C.flat_smooth
    flat_inverse := C.flat_inverse
    flat_eq := C.flat_eq
    beta := k * C.beta
    beta_ne := mul_ne_zero hk.ne' C.beta_ne
    collarWidth := w
    collar_pos := hw
    collar_le := hww.trans C.collar_le
    collar_eq := by
      intro x hx s hs
      have hheight : h (C.cutHeight + C.sign * (C.removal - C.scale) + C.beta * s) =
          h C.cutHeight + C.sign * (k * C.removal - k * C.scale) + (k * C.beta) * s :=
        (haff _ (hcol s hs)).trans (by ring)
      change G (psi (C.flatChart x, s)) = heightTransportTube C.tube h G0
        (x, h C.cutHeight + C.sign * (k * C.removal - k * C.scale) + (k * C.beta) * s)
      rw [C.collar_eq x hx s (lt_of_lt_of_le hs hww), ← hheight,
        heightTransportTube_apply, h.symm_apply_apply]
      apply hag
      refine ⟨_, ⟨?_, ?_⟩, rfl⟩
      · simpa only [mem_closedBall, dist_zero_right] using
          (show ‖x‖ ≤ (1 : ℝ) by linarith)
      · simpa only [mem_closedBall, Real.dist_eq] using hcol s hs }

variable (C : SurgeryCapTag psi u)
variable (h : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
variable (G0 G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
variable (k R o w : ℝ) (hk : 0 < k)
variable (ho : 0 < o) (hoo : o ≤ C.overlapWidth)
variable (hw : 0 < w) (hww : w ≤ C.collarWidth)
variable (hG0 : ∀ y : E3, ⟪(u : E3), G0 y⟫_ℝ = h ⟪(u : E3), y⟫_ℝ)
variable (haff : ∀ z : ℝ, |z - C.cutHeight| ≤ R →
  h z = h C.cutHeight + k * (z - C.cutHeight))
variable (hcap : ∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 < o →
  |C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model q).2) -
    C.cutHeight| ≤ R)
variable (hcol : ∀ s : ℝ, |s| < w →
  |C.cutHeight + C.sign * (C.removal - C.scale) + C.beta * s - C.cutHeight| ≤ R)
variable (hag : EqOn G G0 (C.tube ''
  (closedBall (0 : E2) 1 ×ˢ closedBall C.cutHeight R)))



theorem SurgeryCapTag.heightCompress_sourceCap :
    (C.heightCompress h G0 G k R o w hk ho hoo hw hww hG0 haff hcap hcol hag).sourceCap =
      C.sourceCap := rfl



theorem SurgeryCapTag.heightCompress_sourceSeam :
    (C.heightCompress h G0 G k R o w hk ho hoo hw hww hG0 haff hcap hcol hag).sourceSeam =
      C.sourceSeam := rfl



theorem SurgeryCapTag.heightCompress_cap :
    (C.heightCompress h G0 G k R o w hk ho hoo hw hww hG0 haff hcap hcol hag).cap =
      G '' C.cap := by
  change (fun q : UnitTwoSphere => G (psi (q, 0))) '' C.sourceCap =
    G '' ((fun q : UnitTwoSphere => psi (q, 0)) '' C.sourceCap)
  rw [image_image]



theorem SurgeryCapTag.heightCompress_seam :
    (C.heightCompress h G0 G k R o w hk ho hoo hw hww hG0 haff hcap hcol hag).seam =
      G '' C.seam := by
  change (fun q : UnitTwoSphere => G (psi (q, 0))) '' C.sourceSeam =
    G '' ((fun q : UnitTwoSphere => psi (q, 0)) '' C.sourceSeam)
  rw [image_image]

end PoincareConjecture.M25.Topology3D
