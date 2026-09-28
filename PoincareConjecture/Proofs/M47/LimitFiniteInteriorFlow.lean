import PoincareConjecture.Proofs.M47.LimitFiniteRetainedInterior
import PoincareConjecture.Proofs.M47.TerminalSourceRealizationHistory









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47



theorem limitFinite_preserved_interior_flow
    (P : M47Predecessors.{u})
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {C : GeneralizedSliceCarrier.{u}}
    {base Q b c tau K : ℝ} (U : TopologicalSpace.Opens C.carrier)
    (hne : (U : Set C.carrier).Nonempty)
    (hbase : base ∈ H.generalized.interval) (htau : 0 < tau) (hb : b < -tau)
    (E : SurgeryFlowCylinder F C base Q (Icc b 0) U)
    (e0 : GeneralizedFlowCylinder H.generalized C base Q (Icc c 0) U)
    (hfuture : ∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc b 0), ∀ x ∈ U,
      E.forward s hs' x = H.history.forward (base + s / Q)
        ((H.generalized.slice_nonempty_iff _).mp ⟨e0.forward s hs x⟩)
        (e0.forward s hs x))
    (hcurv : ∀ s (hs : s ∈ Icc b 0), ∀ x ∈ U,
      |(F.connection (base + s / Q)).curvatureTensorNorm (E.forward s hs x)| ≤ K * Q) :
    ∃ G : RicciFlow 3 U (Icc (-tau) 0),
      (∀ s (hs : s ∈ Icc (-tau) 0) (x : U),
        (∀ v w : TangentSpace (𝓡 3) x,
          (G.metric s).inner x v w = E.pullbackInner s ⟨hb.le.trans hs.1, hs.2⟩ x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w)) ∧
        (G.connection s).scalarCurvature x =
          (F.connection (base + s / Q)).scalarCurvature
            (E.forward s ⟨hb.le.trans hs.1, hs.2⟩ x.val) / Q ∧
        (G.connection s).curvatureTensorNorm x =
          (F.connection (base + s / Q)).curvatureTensorNorm
            (E.forward s ⟨hb.le.trans hs.1, hs.2⟩ x.val) / Q) ∧
      (∀ s ∈ Icc (-tau) 0, ∀ x : U, |(G.connection s).curvatureTensorNorm x| ≤ K) ∧
      (∀ s (hs : s ∈ Icc c 0) (_hs' : s ∈ Icc (-tau) 0) (x : U),
        ∀ v w : TangentSpace (𝓡 3) x,
          (G.metric s).inner x v w = e0.pullbackInner s hs x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w)) := by
  obtain ⟨htime, e, hmap, hmetric, _hfuture, hfutureMetric⟩ :=
    limitFinite_preserved_history_interior H hbase htau hb U.isOpen E e0 hfuture
  obtain ⟨G, hG⟩ := terminalSourceRealization_generalized P htau U hne e
  have hread (s : ℝ) (hs : s ∈ Icc (-tau) 0) (x : U) :
      (∀ v w : TangentSpace (𝓡 3) x,
        (G.metric s).inner x v w = E.pullbackInner s ⟨hb.le.trans hs.1, hs.2⟩ x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w)) ∧
      (G.connection s).scalarCurvature x =
        (F.connection (base + s / Q)).scalarCurvature
          (E.forward s ⟨hb.le.trans hs.1, hs.2⟩ x.val) / Q ∧
      (G.connection s).curvatureTensorNorm x =
        (F.connection (base + s / Q)).curvatureTensorNorm
          (E.forward s ⟨hb.le.trans hs.1, hs.2⟩ x.val) / Q := by
    refine ⟨?_, ?_, ?_⟩
    · intro v w
      exact ((hG s hs x).1 v w).trans (hmetric s hs x.val x.property _ _)
    · rw [(hG s hs x).2.1, ← H.scalar_pullback _ (htime s hs), hmap s hs x.val x.property]
    · rw [(hG s hs x).2.2, ← H.curvature_norm_pullback _ (htime s hs),
        hmap s hs x.val x.property]
  refine ⟨G, hread, ?_, ?_⟩
  · intro s hs x
    rw [(hread s hs x).2.2, abs_div, abs_of_pos E.scale_pos]
    exact (div_le_iff₀ E.scale_pos).mpr (hcurv s _ x.val x.property)
  · intro s hs hs' x v w
    exact ((hG s hs' x).1 v w).trans (hfutureMetric s hs hs' x.val x.property _ _)

end PoincareConjecture.M47
