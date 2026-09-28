import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Cylinders.BoxWorldlines
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Cylinders.LiftedSlices

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Surgery.RegularHistory.Cylinders

variable {F : SurgeryFlowData.{u}} (W : M33RegularHistoryWindow F)
  (L : ∀ t, t ∈ F.surgery_times → t ∈ W.interval →
    RicciFlowLocalTheory 3 (F.slice t).carrier)
  {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ} {J : Set ℝ} {U : Set C.carrier}
  (e : SurgeryFlowCylinder F C origin scale J U)
  (htime : ∀ s ∈ J, origin + s / scale ∈ W.interval)
  (hguard : ∀ s hs, e.forward s hs '' U ⊆ m33RegularRegion F (origin + s / scale))

include hguard

theorem exists_lifted_box (s : ℝ) (hs : s ∈ J) :
    ∃ b : BoxIndex W, ∃ _hb : origin + s / scale ∈ (atlasBox W L b).interval,
      ∃ y : U → (atlasBox W L b).carrier.carrier, IsEmbedding y ∧
      ∀ t ht (htb : origin + t / scale ∈ (atlasBox W L b).interval) (x : U),
        liftedForward W e htime t ht x.val = (atlasBox W L b).forward _ htb (y x) := by
  obtain ⟨b, hb, hsurj, htracks⟩ := exists_tracking_box e L htime s hs
  let B := atlasBox W L b
  let y : U → B.carrier.carrier := fun x =>
    B.inverse _ hb (liftedForward W e htime s hs x.val)
  have hy (x : U) : B.forward _ hb (y x) = liftedForward W e htime s hs x.val :=
    B.right_inverse _ hb (Set.range_eq_univ.mpr hsurj ▸ mem_univ _)
  refine ⟨b, hb, y, ?_, ?_⟩
  · apply (B.forward_openEmbedding _ hb).isEmbedding.of_comp_iff.mp
    have heq : (B.forward _ hb) ∘ y = fun x : U => liftedForward W e htime s hs x.val :=
      funext hy
    rw [heq]
    exact liftedForward_isEmbedding W e htime hguard s hs
  · intro t ht htb x
    apply (forward_openEmbedding W _).injective
    rw [ambient_liftedForward W e htime hguard t ht x.val x.property]
    exact (htracks t ht htb x.val x.property (y x) (by
      rw [hy x, ambient_liftedForward W e htime hguard s hs x.val x.property])).symm

theorem lifted_vertical_compatibility (s : ℝ) (hs : s ∈ J) (x : C.carrier) (hx : x ∈ U) :
    ∃ b : (generalized W L).box_index, ∃ y : ((generalized W L).box b).carrier.carrier,
      ∃ δ : ℝ, 0 < δ ∧ ∀ t ht, |t - s| < δ →
        ∃ hb : origin + t / scale ∈ ((generalized W L).box b).interval,
          liftedForward W e htime t ht x = ((generalized W L).box b).forward _ hb y := by
  obtain ⟨b, hb, y, _, htracks⟩ := exists_lifted_box W L e htime hguard s hs
  obtain ⟨V, hV, hBV⟩ := (atlasBox W L b).relatively_open
  have hopen : IsOpen ((fun t : ℝ => origin + t / scale) ⁻¹' V) :=
    hV.preimage (by fun_prop)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen s ((hBV ▸ hb).2)
  refine ⟨b, y ⟨x, hx⟩, δ, hδ, ?_⟩
  intro t ht hts
  have htb : origin + t / scale ∈ (atlasBox W L b).interval := by
    rw [hBV]
    exact ⟨htime t ht, hball (by simpa only [Metric.mem_ball, Real.dist_eq] using hts)⟩
  exact ⟨htb, htracks t ht htb ⟨x, hx⟩⟩

end PoincareConjecture.Surgery.RegularHistory.Cylinders
