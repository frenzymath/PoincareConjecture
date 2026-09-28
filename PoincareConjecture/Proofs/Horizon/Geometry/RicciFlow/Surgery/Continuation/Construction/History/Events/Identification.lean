import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.RegularSlices
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.OpenFlow












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Surgery.RegularHistory.EventIdentify

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F} {T : ℝ}
    (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]


abbrev carrier : GeneralizedSliceCarrier.{u} :=
  (F.slice (F.event T hT).tMinus).openSubset
    (SurgeryRegionEquivalence.sourceInterior (U := (F.event T hT).retained_pre))


def pre (t : Ico (F.event T hT).tMinus T) (htW : t.val ∈ W.interval)
    (htS : t.val ∉ F.surgery_times) : (carrier hT).carrier → (slice W t.val).carrier :=
  fun x => ⟨(F.event T hT).pre_identify t x.val, htW, by
    rw [m33RegularRegion_of_regular F t.val htS]
    exact mem_univ _⟩

@[simp] theorem forward_pre (t : Ico (F.event T hT).tMinus T)
    (htW : t.val ∈ W.interval) (htS : t.val ∉ F.surgery_times)
    (x : (carrier hT).carrier) :
    forward W t.val (pre hT t htW htS x) = (F.event T hT).pre_identify t x.val := rfl

theorem pre_smooth (t : Ico (F.event T hT).tMinus T)
    (htW : t.val ∈ W.interval) (htS : t.val ∉ F.surgery_times) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (pre hT t htW htS) :=
  (ContMDiff.subtypeVal_comp_iff (regionOpens W t.val) _).mp
    (((F.event T hT).pre_identify t).contMDiff.comp contMDiff_subtype_val)

theorem pre_openEmbedding (t : Ico (F.event T hT).tMinus T)
    (htW : t.val ∈ W.interval) (htS : t.val ∉ F.surgery_times) :
    Topology.IsOpenEmbedding (pre hT t htW htS) := by
  apply Topology.IsOpenEmbedding.of_comp _ (forward_openEmbedding W t.val)
  exact ((F.event T hT).pre_identify t).toHomeomorph.isOpenEmbedding.comp
    isOpen_interior.isOpenEmbedding_subtypeVal

theorem pre_metric (t : Ico (F.event T hT).tMinus T)
    (htW : t.val ∈ W.interval) (htS : t.val ∉ F.surgery_times)
    (x : (carrier hT).carrier) (v w : TangentSpace (𝓡 3) x) :
    (metric W t.val).inner (pre hT t htW htS x)
      (mfderiv (𝓡 3) (𝓡 3) (pre hT t htW htS) x v)
      (mfderiv (𝓡 3) (𝓡 3) (pre hT t htW htS) x w) =
        ((F.event T hT).continuingPreFlow.metric t.val).inner x v w := by
  have hderiv (z : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) (forward W t.val) (pre hT t htW htS x)
        (mfderiv (𝓡 3) (𝓡 3) (pre hT t htW htS) x z) =
      mfderiv (𝓡 3) (𝓡 3) ((F.event T hT).pre_identify t) x.val
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val x z) := by
    have h := (mfderiv_comp_apply x
      ((forward_smooth W t.val).mdifferentiable (by simp) _)
      ((pre_smooth hT t htW htS).mdifferentiable (by simp) x) z).symm
    exact h.trans (mfderiv_comp_apply x
      (((F.event T hT).pre_identify t).contMDiff.mdifferentiable (by simp) x.val)
      ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) x) z)
  rw [← metric_pullback W t.val, hderiv v, hderiv w]
  exact (F.event T hT).pre_metric t x.val _ _


def post {b : ℝ} (A : SurgeryRegularSlab F.slice F.metric T b)
    (t : Icc T b) (htW : t.val ∈ W.interval)
    (htS : t.val ∈ F.surgery_times → t.val = T) :
    (carrier hT).carrier → (slice W t.val).carrier :=
  fun x => ⟨A.identify t ((F.event T hT).retention.map x.val), htW, by
    by_cases hs : t.val ∈ F.surgery_times
    · have heq := htS hs
      rcases t with ⟨t, ht⟩
      dsimp only at heq
      subst t
      rw [m33RegularRegion_of_surgery F T hT, A.initial_identify]
      exact (F.event T hT).retention.mapsTo_interior x.property
    · rw [m33RegularRegion_of_regular F t.val hs]
      exact mem_univ _⟩

@[simp] theorem forward_post {b : ℝ} (A : SurgeryRegularSlab F.slice F.metric T b)
    (t : Icc T b) (htW : t.val ∈ W.interval)
    (htS : t.val ∈ F.surgery_times → t.val = T) (x : (carrier hT).carrier) :
    forward W t.val (post hT A t htW htS x) =
      A.identify t ((F.event T hT).retention.map x.val) := rfl

theorem post_smooth {b : ℝ} (A : SurgeryRegularSlab F.slice F.metric T b)
    (t : Icc T b) (htW : t.val ∈ W.interval)
    (htS : t.val ∈ F.surgery_times → t.val = T) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (post hT A t htW htS) :=
  (ContMDiff.subtypeVal_comp_iff (regionOpens W t.val) _).mp
    ((A.identify t).contMDiff.comp
      (F.event T hT).retention.interiorMap_isLocalDiffeomorph.contMDiff)

theorem post_openEmbedding {b : ℝ} (A : SurgeryRegularSlab F.slice F.metric T b)
    (t : Icc T b) (htW : t.val ∈ W.interval)
    (htS : t.val ∈ F.surgery_times → t.val = T) :
    Topology.IsOpenEmbedding (post hT A t htW htS) := by
  apply Topology.IsOpenEmbedding.of_comp _ (forward_openEmbedding W t.val)
  exact (A.identify t).toHomeomorph.isOpenEmbedding.comp
    (isOpen_interior.isOpenEmbedding_subtypeVal.comp
      (F.event T hT).retention.interiorDiffeomorph.toHomeomorph.isOpenEmbedding)

theorem post_metric {b : ℝ} (A : SurgeryRegularSlab F.slice F.metric T b)
    (t : Icc T b) (htW : t.val ∈ W.interval)
    (htS : t.val ∈ F.surgery_times → t.val = T)
    (x : (carrier hT).carrier) (v w : TangentSpace (𝓡 3) x) :
    (metric W t.val).inner (post hT A t htW htS x)
      (mfderiv (𝓡 3) (𝓡 3) (post hT A t htW htS) x v)
      (mfderiv (𝓡 3) (𝓡 3) (post hT A t htW htS) x w) =
        (((F.event T hT).continuingPostFlow A.flow).metric t.val).inner x v w := by
  have hderiv (z : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) (forward W t.val) (post hT A t htW htS x)
        (mfderiv (𝓡 3) (𝓡 3) (post hT A t htW htS) x z) =
      mfderiv (𝓡 3) (𝓡 3) (A.identify t) ((F.event T hT).retention.map x.val)
        (mfderiv (𝓡 3) (𝓡 3) (F.event T hT).retention.interiorMap x z) := by
    have h := (mfderiv_comp_apply x
      ((forward_smooth W t.val).mdifferentiable (by simp) _)
      ((post_smooth hT A t htW htS).mdifferentiable (by simp) x) z).symm
    exact h.trans (mfderiv_comp_apply x
      ((A.identify t).contMDiff.mdifferentiable (by simp) _)
      ((F.event T hT).retention.interiorMap_isLocalDiffeomorph.contMDiff.mdifferentiable
        (by simp) x) z)
  rw [← metric_pullback W t.val, hderiv v, hderiv w]
  exact A.metric_pullback t ((F.event T hT).retention.map x.val) _ _


theorem post_event_range {b : ℝ} (A : SurgeryRegularSlab F.slice F.metric T b)
    (hTW : T ∈ W.interval) :
    range (forward W T ∘
      post hT A ⟨T, le_rfl, A.ordered.le⟩ hTW (fun _ => rfl)) =
        interior (F.event T hT).retained_post := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change A.identify ⟨T, le_rfl, A.ordered.le⟩
      ((F.event T hT).retention.map x.val) ∈ _
    rw [A.initial_identify]
    exact (F.event T hT).retention.mapsTo_interior x.property
  · intro hy
    obtain ⟨x, hx, hxy⟩ := (F.event T hT).retention.image_interior.symm ▸ hy
    refine ⟨⟨x, hx⟩, ?_⟩
    exact (A.initial_identify ((F.event T hT).retention.map x)).trans hxy

theorem post_event_surjective {b : ℝ} (A : SurgeryRegularSlab F.slice F.metric T b)
    (hTW : T ∈ W.interval) :
    Function.Surjective (post hT A ⟨T, le_rfl, A.ordered.le⟩ hTW (fun _ => rfl)) := by
  intro y
  have hy : y.val ∈ interior (F.event T hT).retained_post := by
    simpa only [m33RegularRegion_of_surgery F T hT] using y.property.2
  obtain ⟨x, hx⟩ := (post_event_range hT A hTW).symm ▸ hy
  exact ⟨x, Subtype.ext hx⟩

theorem pre_slab_compatibility (a b : ℝ) (hab : a < b)
    (hJ : Icc a b ⊆ F.time_domain) (hfree : Disjoint F.surgery_times (Ioc a b))
    (s t : Ico (F.event T hT).tMinus T) (hs : s.val ∈ Icc a b) (ht : t.val ∈ Icc a b)
    (hsW : s.val ∈ W.interval) (htW : t.val ∈ W.interval)
    (hsS : s.val ∉ F.surgery_times) (htS : t.val ∉ F.surgery_times)
    (x : (carrier hT).carrier) :
    (F.regular_slabs a b hab hJ hfree).transport ⟨s.val, hs⟩ ⟨t.val, ht⟩
      (forward W s.val (pre hT s hsW hsS x)) =
        forward W t.val (pre hT t htW htS x) :=
  F.event_slab_compatibility T hT a b hab hJ hfree
    s.val t.val hs ht s.property t.property x.val

theorem post_transport {b : ℝ} (A : SurgeryRegularSlab F.slice F.metric T b)
    (s t : Icc T b) (hsW : s.val ∈ W.interval) (htW : t.val ∈ W.interval)
    (hsS : s.val ∈ F.surgery_times → s.val = T)
    (htS : t.val ∈ F.surgery_times → t.val = T) (x : (carrier hT).carrier) :
    A.transport s t (forward W s.val (post hT A s hsW hsS x)) =
      forward W t.val (post hT A t htW htS x) := by
  simp only [forward_post, SurgeryRegularSlab.transport, Diffeomorph.symm_apply_apply]



theorem post_slab_compatibility {b : ℝ} (hTb : T < b)
    (hPost : Icc T b ⊆ F.time_domain) (hPostFree : Disjoint F.surgery_times (Ioc T b))
    (a c : ℝ) (hac : a < c) (hJ : Icc a c ⊆ F.time_domain)
    (hfree : Disjoint F.surgery_times (Ioc a c))
    (s t : Icc T b) (hs : s.val ∈ Icc a c) (ht : t.val ∈ Icc a c)
    (hsW : s.val ∈ W.interval) (htW : t.val ∈ W.interval)
    (hsS : s.val ∈ F.surgery_times → s.val = T)
    (htS : t.val ∈ F.surgery_times → t.val = T) (x : (carrier hT).carrier) :
    (F.regular_slabs a c hac hJ hfree).transport ⟨s.val, hs⟩ ⟨t.val, ht⟩
      (forward W s.val
        (post hT (F.regular_slabs T b hTb hPost hPostFree) s hsW hsS x)) =
      forward W t.val
        (post hT (F.regular_slabs T b hTb hPost hPostFree) t htW htS x) := by
  rw [F.slab_transport_coherent a c T b hac hJ hfree hTb hPost hPostFree
    s.val t.val hs ht s.property t.property]
  exact post_transport hT _ s t hsW htW hsS htS x

end PoincareConjecture.Surgery.RegularHistory.EventIdentify
