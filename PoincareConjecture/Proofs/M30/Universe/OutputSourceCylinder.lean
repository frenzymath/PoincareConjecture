import PoincareConjecture.Proofs.M30.Universe.OutputSourceLiftJets
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding
import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction.SmoothInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30

noncomputable def liftCylinderOfOrdinaryEmbedding
    {J : Set ℝ} (L : BlowupLimitFlow.{0} J)
    {F : GeneralizedRicciFlowData.{u}} {Dsrc : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} (W : TopologicalSpace.Opens Dsrc.carrier)
    (Esrc : GeneralizedFlowCylinder F Dsrc origin scale I W)
    (V : Set L.sliceCarrier.carrier) (hV : IsOpen V)
    (a0 : L.sliceCarrier.carrier → W)
    (hemb : Topology.IsOpenEmbedding (fun x : V => a0 x.val))
    (ha0 : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ a0 V) :
    GeneralizedFlowCylinder F (liftBlowupLimit.{u} L).sliceCarrier origin scale I
      ((ULift.down : ULift.{u} L.sliceCarrier.carrier → L.sliceCarrier.carrier) ⁻¹' V) := by
  classical
  let : Nonempty L.sliceCarrier.carrier := ⟨L.base⟩
  let a : L.sliceCarrier.carrier → Dsrc.carrier := fun x => (a0 x).val
  have ha : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ a V := by
    intro x
    exact (ha0 x).comp (𝓡 3) Dsrc.carrier
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) W (a0 x.val))
  have hinj : InjOn a V := by
    intro x hx y hy hxy
    have hxy' : a0 x = a0 y := Subtype.ext hxy
    exact congrArg Subtype.val (hemb.injective
      (show (fun z : V => a0 z.val) ⟨x, hx⟩ =
        (fun z : V => a0 z.val) ⟨y, hy⟩ from hxy'))
  let b : Dsrc.carrier → L.sliceCarrier.carrier :=
    fun y => if y ∈ a '' V then Function.invFunOn a V y else L.base
  have hb_left : LeftInvOn b a V := by
    intro x hx
    dsimp only [b]
    rw [if_pos (mem_image_of_mem a hx)]
    exact hinj.leftInvOn_invFunOn hx
  have hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b (a '' V) := by
    rintro _ ⟨x, hx, rfl⟩
    have hlocal : ∀ᶠ z in 𝓝 x, b (a z) = z := by
      filter_upwards [hV.mem_nhds hx] with z hz
      exact hb_left hz
    exact (Poincare.contMDiffAt_of_local_left_inverse (ha ⟨x, hx⟩).contMDiffAt
      ((ha ⟨x, hx⟩).mfderivToContinuousLinearEquiv (by simp)).bijective
      hlocal).contMDiffWithinAt
  let f := fun s (hs : s ∈ I) (x : L.sliceCarrier.carrier) => Esrc.forward s hs (a x)
  let g := fun s (hs : s ∈ I) (y : (F.slice (origin + s / scale)).carrier) =>
    b (Esrc.inverse s hs y)
  have hf (s : ℝ) (hs : s ∈ I) : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) V :=
    (Esrc.forward_smooth s hs).comp ha.contMDiffOn (fun x _ => (a0 x).property)
  have hleft (s : ℝ) (hs : s ∈ I) : LeftInvOn (g s hs) (f s hs) V := by
    intro x hx
    change b (Esrc.inverse s hs (Esrc.forward s hs (a x))) = x
    rw [Esrc.left_inverse s hs (a0 x).property]
    exact hb_left hx
  have hg (s : ℝ) (hs : s ∈ I) :
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (g s hs) (f s hs '' V) := by
    have hsub : f s hs '' V ⊆ Esrc.forward s hs '' (W : Set Dsrc.carrier) := by
      rintro _ ⟨x, _, rfl⟩
      exact ⟨a x, (a0 x).property, rfl⟩
    apply hb.comp ((Esrc.inverse_smooth s hs).mono hsub)
    rintro _ ⟨x, hx, rfl⟩
    change Esrc.inverse s hs (Esrc.forward s hs (a x)) ∈ a '' V
    rw [Esrc.left_inverse s hs (a0 x).property]
    exact mem_image_of_mem a hx
  refine liftCylinderFromMaps L F origin scale I V Esrc.scale_pos f g hf hg hleft ?_ ?_ ?_
  · intro s hs
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg (f s hs) (hleft s hs hx)
  · exact Esrc.embedding.comp (Topology.IsEmbedding.id.prodMap hemb.isEmbedding)
  · intro s hs x _
    exact Esrc.vertical_compatibility s hs (a x) (a0 x).property

end PoincareConjecture.M30
