import PoincareConjecture.Proofs.M47.GeneralizedBridgeCylinder
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

theorem limitFinite_preserved_history_interior
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {C : GeneralizedSliceCarrier.{u}}
    {base Q b c tau : ℝ} {U : Set C.carrier}
    (hbase : base ∈ H.generalized.interval) (htau : 0 < tau)
    (hb : b < -tau) (hU : IsOpen U)
    (E : SurgeryFlowCylinder F C base Q (Icc b 0) U)
    (e0 : GeneralizedFlowCylinder H.generalized C base Q (Icc c 0) U)
    (hfuture : ∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc b 0), ∀ x ∈ U,
      E.forward s hs' x = H.history.forward (base + s / Q)
        ((H.generalized.slice_nonempty_iff _).mp ⟨e0.forward s hs x⟩)
        (e0.forward s hs x)) :
    ∃ htime : ∀ s ∈ Icc (-tau) 0, base + s / Q ∈ H.generalized.interval,
      ∃ e : GeneralizedFlowCylinder H.generalized C base Q (Icc (-tau) 0) U,
        (∀ s hs x, x ∈ U → H.history.forward (base + s / Q) (htime s hs)
          (e.forward s hs x) = E.forward s ⟨hb.le.trans hs.1, hs.2⟩ x) ∧
        (∀ s hs x, x ∈ U → ∀ v w : TangentSpace (𝓡 3) x,
          e.pullbackInner s hs x v w =
            E.pullbackInner s ⟨hb.le.trans hs.1, hs.2⟩ x v w) ∧
        (∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc (-tau) 0), ∀ x ∈ U,
          e.forward s hs' x = e0.forward s hs x) ∧
        (∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc (-tau) 0), ∀ x ∈ U,
          ∀ v w : TangentSpace (𝓡 3) x,
            e.pullbackInner s hs' x v w = e0.pullbackInner s hs x v w) := by
  have hsub : Icc (-tau) 0 ⊆ Icc b 0 := Icc_subset_Icc hb.le le_rfl
  let small := E.restrict hsub ordConnected_Icc (Subset.refl U)
  have htime (s : ℝ) (hs : s ∈ Icc (-tau) 0) :
      base + s / Q ∈ H.generalized.interval := by
    rw [H.interval_eq]
    apply W.interval_connected.out W.zero_mem (H.interval_eq ▸ hbase)
    exact ⟨F.time_domain_nonnegative (E.time_subset (mem_image_of_mem _ (hsub hs))),
      add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs.2 E.scale_pos.le)⟩
  have hregular (s : ℝ) (hs : s ∈ Icc (-tau) 0) :
      small.forward s hs '' U ⊆ m33RegularRegion F (base + s / Q) := by
    exact E.regular_image_of_earlier (hsub hs)
      ⟨b, ⟨le_rfl, (hb.trans (neg_neg_of_pos htau)).le⟩, hb.trans_le hs.1⟩
  obtain ⟨e, hmap, hmetric⟩ := H.cylinders_from_surgery C base Q
    (Icc (-tau) 0) U hU htime small hregular
  have hagree (s : ℝ) (hs : s ∈ Icc c 0) (hs' : s ∈ Icc (-tau) 0)
      (x : C.carrier) (hx : x ∈ U) : e.forward s hs' x = e0.forward s hs x := by
    apply (H.history.forward_openEmbedding (base + s / Q) (htime s hs')).injective
    exact (hmap s hs' x hx).trans (hfuture s hs (hsub hs') x hx)
  refine ⟨htime, e, hmap, hmetric, hagree, ?_⟩
  intro s hs hs' x hx v w
  have heq : e.forward s hs' =ᶠ[𝓝 x] e0.forward s hs := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hagree s hs hs' y hy
  unfold GeneralizedFlowCylinder.pullbackInner
  rw [heq.self_of_nhds, heq.mfderiv_eq]

end PoincareConjecture.M47
