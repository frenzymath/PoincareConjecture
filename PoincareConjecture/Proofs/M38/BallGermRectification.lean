import PoincareConjecture.Proofs.M38.LocalGermExtension
import PoincareConjecture.Proofs.M38.BallChartGerms
import PoincareConjecture.Proofs.M38.RecenteredBall










set_option autoImplicit false

open Set Topology Filter
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}}



theorem exists_centeredBallGermRectification (B C : SurgeryBallEmbedding A)
    (hcenter : B.map 0 = C.map 0) :
    ∃ r : ℝ, 0 < r ∧
      ∃ e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞,
        (∀ x : StandardCapSpace, ‖x‖ < r →
          e (B.map x) = C.map (surgeryBallTransitionLinear B C hcenter x)) ∧
        (∀ y : A.carrier, y ∉ C.map '' Metric.ball 0 2 → e y = y) := by
  let L := surgeryBallTransitionLinear B C hcenter
  let f := surgeryBallTransition B C
  let g := surgeryBallTransition C B
  let k : StandardCapSpace → StandardCapSpace := fun x => L (g x)
  have hk : ContDiffOn ℝ ∞ k (surgeryBallTransitionDomain C B) :=
    L.contDiff.comp_contDiffOn (surgeryBallTransition_smooth C B)
  have hk0 : k 0 = 0 := by
    change L (surgeryBallTransition C B 0) = 0
    rw [surgeryBallTransition_zero C B hcenter.symm, map_zero]
  have hk' : fderiv ℝ k 0 = ContinuousLinearMap.id ℝ StandardCapSpace :=
    surgeryBallNormalizedInverse_derivative B C hcenter
  obtain ⟨δ, hδ, hδR, E, _, hinner, houter⟩ :=
    exists_coordinateGermExtension k (surgeryBallTransitionDomain_open C B)
      (surgeryBallTransitionDomain_zero C B hcenter.symm) hk hk0 hk' (3 / 2) (by norm_num)
  have hEouter : ∀ z : StandardCapSpace, 3 / 2 ≤ ‖z‖ → E z = z :=
    fun z hz => houter z (hδR.le.trans hz)
  let e := surgeryBallPatchDiffeomorph E hEouter C
  have hf0 : f 0 = 0 := surgeryBallTransition_zero B C hcenter
  have hfn : surgeryBallTransitionDomain B C ∈ 𝓝 (0 : StandardCapSpace) :=
    (surgeryBallTransitionDomain_open B C).mem_nhds
      (surgeryBallTransitionDomain_zero B C hcenter)
  have hfc : ContinuousAt f 0 := ((surgeryBallTransition_smooth B C).contDiffAt hfn).continuousAt
  have hpre : f ⁻¹' Metric.ball 0 (δ / 2) ∈ 𝓝 (0 : StandardCapSpace) := by
    apply hfc
    rw [hf0]
    exact Metric.ball_mem_nhds 0 (by positivity)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hfn hpre)
  refine ⟨r, hr, e, ?_, ?_⟩
  · intro x hx
    have hx' := hball (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
    have hfx : ‖f x‖ ≤ δ / 2 := by
      exact le_of_lt (by simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using hx'.2)
    change surgeryBallPatch C E (B.map x) = C.map (L x)
    rw [surgeryBallPatch_of_mem C E hx'.1.2]
    change C.map (E (f x)) = C.map (L x)
    rw [hinner (f x) hfx]
    change C.map (L (surgeryBallTransition C B (surgeryBallTransition B C x))) = C.map (L x)
    rw [surgeryBallTransition_left_inverse B C hx'.1]
  · intro y hy
    change surgeryBallPatch C E y = y
    exact surgeryBallPatch_of_not_mem C E hy




theorem exists_surgeryBallGermRectification (B C : SurgeryBallEmbedding A)
    (hBC : B.map 0 ∈ C.map '' Metric.ball 0 2)
    {O : Set A.carrier} (hO : IsOpen O) (hpO : B.map 0 ∈ O) :
    ∃ L : StandardCapSpace ≃L[ℝ] StandardCapSpace,
      (L : StandardCapSpace →L[ℝ] StandardCapSpace) =
        fderiv ℝ (fun x => C.inverse (B.map x)) 0 ∧
      ∃ r : ℝ, 0 < r ∧
        ∃ e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞,
          (∀ x : StandardCapSpace, ‖x‖ < r →
            e (B.map x) = C.map (C.inverse (B.map 0) + L x)) ∧
          (∀ y : A.carrier, y ∉ O → e y = y) := by
  obtain ⟨t, ht, D, hDmap, hDinv, hD0, hDO⟩ :=
    exists_surgeryBallAffineSubchart C (B.map 0) hBC hO hpO
  let LD := surgeryBallTransitionLinear B D hD0.symm
  let S : StandardCapSpace ≃L[ℝ] StandardCapSpace :=
    (LinearEquiv.smulOfNeZero ℝ StandardCapSpace t ht.ne').toContinuousLinearEquiv
  let L : StandardCapSpace ≃L[ℝ] StandardCapSpace := LD.trans S
  have hL (x : StandardCapSpace) : L x = t • LD x := rfl
  have hLcoe : (L : StandardCapSpace →L[ℝ] StandardCapSpace) =
      t • fderiv ℝ (surgeryBallTransition B D) 0 := by
    ext x
    rfl
  have hfd := ((surgeryBallTransition_smooth B D).contDiffAt
    ((surgeryBallTransitionDomain_open B D).mem_nhds
      (surgeryBallTransitionDomain_zero B D hD0.symm))).differentiableAt (by simp)
  have haffine : (fun x => C.inverse (B.map x)) =
      (fun x => C.inverse (B.map 0) + t • surgeryBallTransition B D x) := by
    funext x
    change C.inverse (B.map x) = C.inverse (B.map 0) + t • D.inverse (B.map x)
    rw [hDinv, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    abel
  have hderivative : HasFDerivAt (fun x => C.inverse (B.map x))
      (t • fderiv ℝ (surgeryBallTransition B D) 0) 0 := by
    rw [haffine]
    exact (hfd.hasFDerivAt.const_smul t).const_add (C.inverse (B.map 0))
  obtain ⟨r, hr, e, he, heout⟩ := exists_centeredBallGermRectification B D hD0.symm
  refine ⟨L, hLcoe.trans hderivative.fderiv.symm, r, hr, e, ?_, ?_⟩
  · intro x hx
    rw [he x hx, hDmap, hL]
  · intro y hy
    exact heout y (fun hmem => hy (hDO hmem))

end PoincareConjecture.M38
