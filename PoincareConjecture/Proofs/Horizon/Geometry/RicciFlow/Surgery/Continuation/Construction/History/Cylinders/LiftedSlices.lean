import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.RegularSlices

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Surgery.RegularHistory.Cylinders

variable {F : SurgeryFlowData.{u}} (W : M33RegularHistoryWindow F)
  {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ} {J : Set ℝ} {U : Set C.carrier}
  (e : SurgeryFlowCylinder F C origin scale J U)
  (htime : ∀ s ∈ J, origin + s / scale ∈ W.interval)

def liftedForward (s : ℝ) (hs : s ∈ J) : C.carrier → (slice W (origin + s / scale)).carrier :=
  inverse W (origin + s / scale) (htime s hs) ∘ e.forward s hs

def liftedInverse (s : ℝ) (hs : s ∈ J) : (slice W (origin + s / scale)).carrier → C.carrier :=
  e.inverse s hs ∘ forward W (origin + s / scale)

variable (hguard : ∀ s hs, e.forward s hs '' U ⊆ m33RegularRegion F (origin + s / scale))

include hguard

theorem ambient_liftedForward (s : ℝ) (hs : s ∈ J) (x : C.carrier) (hx : x ∈ U) :
    forward W (origin + s / scale) (liftedForward W e htime s hs x) = e.forward s hs x := by
  apply right_inverse W (origin + s / scale) (htime s hs)
  rw [regular_range W _ (htime s hs)]
  exact hguard s hs ⟨x, hx, rfl⟩

theorem liftedForward_smooth (s : ℝ) (hs : s ∈ J) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (liftedForward W e htime s hs) U := by
  apply (inverse_smooth W (origin + s / scale) (htime s hs)).comp (e.forward_smooth s hs)
  intro x hx
  rw [regular_range W _ (htime s hs)]
  exact hguard s hs ⟨x, hx, rfl⟩

theorem liftedInverse_smooth (s : ℝ) (hs : s ∈ J) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (liftedInverse W e s hs)
      (liftedForward W e htime s hs '' U) := by
  apply (e.inverse_smooth s hs).comp (forward_smooth W (origin + s / scale)).contMDiffOn
  rintro _ ⟨x, hx, rfl⟩
  change forward W (origin + s / scale) (liftedForward W e htime s hs x) ∈ e.forward s hs '' U
  rw [ambient_liftedForward W e htime hguard s hs x hx]
  exact mem_image_of_mem _ hx

theorem lifted_left_inverse (s : ℝ) (hs : s ∈ J) :
    LeftInvOn (liftedInverse W e s hs) (liftedForward W e htime s hs) U := by
  intro x hx
  change e.inverse s hs (forward W _ (liftedForward W e htime s hs x)) = x
  rw [ambient_liftedForward W e htime hguard s hs x hx]
  exact e.left_inverse s hs hx

theorem lifted_right_inverse (s : ℝ) (hs : s ∈ J) :
    LeftInvOn (liftedForward W e htime s hs) (liftedInverse W e s hs)
      (liftedForward W e htime s hs '' U) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [lifted_left_inverse W e htime hguard s hs hx]

theorem liftedForward_isEmbedding (s : ℝ) (hs : s ∈ J) :
    IsEmbedding (fun x : U => liftedForward W e htime s hs x.val) := by
  have hinv (y : liftedForward W e htime s hs '' U) : liftedInverse W e s hs y.val ∈ U := by
    obtain ⟨x, hx, hxy⟩ := y.property
    rw [← hxy, lifted_left_inverse W e htime hguard s hs hx]
    exact hx
  let H : U ≃ₜ (liftedForward W e htime s hs '' U) :=
    { toFun := fun x => ⟨liftedForward W e htime s hs x.val, ⟨x.val, x.property, rfl⟩⟩
      invFun := fun y => ⟨liftedInverse W e s hs y.val, hinv y⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact lifted_left_inverse W e htime hguard s hs x.property
      right_inv := by
        intro y
        apply Subtype.ext
        exact lifted_right_inverse W e htime hguard s hs y.property
      continuous_toFun :=
        (liftedForward_smooth W e htime hguard s hs).continuousOn.domRestrict.subtype_mk
          (fun x => ⟨x.val, x.property, rfl⟩)
      continuous_invFun :=
        (liftedInverse_smooth W e htime hguard s hs).continuousOn.domRestrict.subtype_mk hinv }
  exact IsEmbedding.subtypeVal.comp H.isEmbedding

theorem lifted_pullbackInner (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    (x : C.carrier) (hx : x ∈ U) (v w : TangentSpace (𝓡 3) x) :
    scale * (metric W (origin + s / scale)).inner (liftedForward W e htime s hs x)
      (mfderiv (𝓡 3) (𝓡 3) (liftedForward W e htime s hs) x v)
      (mfderiv (𝓡 3) (𝓡 3) (liftedForward W e htime s hs) x w) =
        e.pullbackInner s hs x v w := by
  have hnear : (forward W (origin + s / scale) ∘ liftedForward W e htime s hs) =ᶠ[nhds x]
      e.forward s hs :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx)
      (ambient_liftedForward W e htime hguard s hs)
  have hder := hnear.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  have hf := ((liftedForward_smooth W e htime hguard s hs) x hx).contMDiffAt
    (hU.mem_nhds hx)
  have hg := (forward_smooth W (origin + s / scale)).mdifferentiable (by simp)
  change scale * _ = scale * _
  congr 1
  rw [← metric_pullback W (origin + s / scale)]
  rw [← mfderiv_comp_apply x (hg _) (hf.mdifferentiableAt (by simp)) v,
    ← mfderiv_comp_apply x (hg _) (hf.mdifferentiableAt (by simp)) w,
    hder, ambient_liftedForward W e htime hguard s hs x hx]
  rfl

end PoincareConjecture.Surgery.RegularHistory.Cylinders
