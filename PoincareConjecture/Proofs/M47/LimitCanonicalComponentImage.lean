import PoincareConjecture.Proofs.M47.LimitCanonicalPhysicalChart
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.LimitMetricJets
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

theorem limitCanonical_target_eq_connectedComponent
    {C : GeneralizedSliceCarrier.{u}} {D : GeneralizedSliceCarrier.{v}}
    [CompactSpace C.carrier] [ConnectedSpace C.carrier]
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier D.carrier ∞)
    (hsource : f.source = univ) (x : C.carrier) :
    f.target = connectedComponent (f x) := by
  have hcontinuous : Continuous f := continuousOn_univ.mp
    (hsource ▸ f.contMDiffOn_toFun.continuousOn)
  have himage : f '' univ = f.target := by
    simpa only [hsource] using f.toPartialEquiv.image_source_eq_target
  have hclosed : IsClosed f.target := by
    rw [← himage]
    exact (isCompact_univ.image hcontinuous).isClosed
  have hconnected : IsPreconnected f.target := by
    rw [← himage]
    exact isPreconnected_univ.image f hcontinuous.continuousOn
  have hx : f x ∈ f.target := f.map_source (hsource ▸ mem_univ x)
  exact (hconnected.subset_connectedComponent hx).antisymm
    ((show IsClopen f.target from ⟨hclosed, f.open_target⟩).connectedComponent_subset hx)

theorem limitCanonical_eventually_exhaustion_univ
    {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence V J)
    (hcompact : IsCompact (univ : Set G.limit.sliceCarrier.carrier)) :
    ∀ᶠ k in atTop, G.exhaustion.space k = univ := by
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  filter_upwards [eventually_ge_atTop j] with k hk
  exact eq_univ_of_univ_subset (hj.trans (G.exhaustion.space_increasing hk))

theorem limitCanonical_eventually_physical_component_image
    {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence V J)
    (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    (hcompact : IsCompact (univ : Set G.limit.sliceCarrier.carrier)) :
    ∀ᶠ k in atTop, G.exhaustion.space k = univ ∧
      ∀ (s : ℝ) (hs : s ∈ Icc (-G.exhaustion.time k) 0)
        (ht : (V.base (G.subsequence k)).1 + s / V.scale (G.subsequence k) ∈
          (V.flow (G.subsequence k)).interval),
        (limitCanonicalPhysicalChart (G.embedding k) (G.exhaustion.space_open k)
          (R (G.subsequence k)) s hs ht).target =
        connectedComponent (limitRP2PhysicalMap (G.embedding k)
          (R (G.subsequence k)) s hs ht G.limit.base) := by
  let : CompactSpace G.limit.sliceCarrier.carrier := isCompact_univ_iff.mp hcompact
  let : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
  filter_upwards [limitCanonical_eventually_exhaustion_univ G hcompact] with k hk
  refine ⟨hk, ?_⟩
  intro s hs ht
  exact limitCanonical_target_eq_connectedComponent
    (limitCanonicalPhysicalChart (G.embedding k) (G.exhaustion.space_open k)
      (R (G.subsequence k)) s hs ht)
    ((limitCanonicalPhysicalChart_source _ _ _ _ _ _).trans hk) G.limit.base

end PoincareConjecture.M47
