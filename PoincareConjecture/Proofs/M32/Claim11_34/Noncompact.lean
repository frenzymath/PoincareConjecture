import PoincareConjecture.Proofs.M32.Claim11_34.CylinderOpen
import PoincareConjecture.Proofs.M32.Thm11_31.Levels
import PoincareConjecture.Proofs.M32.Claim11_32.Sequence
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen


















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space



theorem blowup_exists_exhaustion_superset
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J)
    {K : Set G.limit.sliceCarrier.carrier} (hK : IsCompact K) :
    ∃ j, K ⊆ G.exhaustion.space j :=
  hK.elim_directed_cover G.exhaustion.space G.exhaustion.space_open
    (fun x _ => G.exhaustion.space_covers.symm ▸ mem_univ x)
    G.exhaustion.space_increasing.directed_le



theorem horn_isPreconnected_carrier
    {F : GeneralizedRicciFlowData.{u}} {T accuracy : ℝ}
    {E : GeneralizedFlowExtension F T} (horn : StrongHorn E accuracy) :
    IsPreconnected horn.carrier := by
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num))
  let : ConnectedSpace (Ico (0 : ℝ) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_Ico (by norm_num : (0 : ℝ) < 1))
  let : ConnectedSpace horn.carrier :=
    horn.coordinate.surjective.connectedSpace horn.coordinate.continuous
  simpa only [image_univ, Subtype.range_val] using
    (isPreconnected_univ : IsPreconnected (univ : Set horn.carrier)).image
      (Subtype.val : horn.carrier → (E.extended.slice T).carrier)
      continuous_subtype_val.continuousOn



theorem horn_carrier_not_subset_compact
    {F : GeneralizedRicciFlowData.{u}} {T accuracy : ℝ}
    {E : GeneralizedFlowExtension F T} (horn : StrongHorn E accuracy)
    (K : Set (E.extended.slice T).carrier) (hK : IsCompact K) :
    ¬ horn.carrier ⊆ K := by
  intro hsub
  apply horn_tail_not_subset_compact horn 0 (by norm_num) K hK
  rintro y ⟨⟨s, t⟩, ⟨_, ht0, ht1⟩, rfl⟩
  apply hsub
  have hmem := (horn.coordinate (s, ⟨t, ht0.le, ht1⟩)).property
  rwa [horn.coordinate_eq] at hmem




theorem blowupLimit_not_isCompact_of_source_regions
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J)
    (U : ∀ k, Set ((S.flow (G.subsequence k)).slice (S.base (G.subsequence k)).1).carrier)
    (hU : ∀ k, IsPreconnected (U k))
    (hescape : ∀ k K, IsCompact K → ¬ U k ⊆ K)
    (hbase : ∀ k, (S.base (G.subsequence k)).2 ∈ U k) :
    ¬ IsCompact (univ : Set G.limit.carrier.carrier) := by
  intro hcompact
  obtain ⟨j, hj⟩ := blowup_exists_exhaustion_superset G hcompact
  have hfull : G.exhaustion.space j = univ := eq_univ_of_univ_subset hj
  have hzero : (0 : ℝ) ∈ Icc (-G.exhaustion.time j) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos j).le, le_rfl⟩
  have hmap : ∃ f : G.limit.carrier.carrier →
      ((S.flow (G.subsequence j)).slice
        ((S.base (G.subsequence j)).1 + 0 / S.scale (G.subsequence j))).carrier,
      Continuous f ∧ IsOpen (f '' univ) ∧
        (⟨(S.base (G.subsequence j)).1 + 0 / S.scale (G.subsequence j),
          f G.limit.base⟩ : (S.flow (G.subsequence j)).point) =
          S.base (G.subsequence j) := by
    refine ⟨(G.embedding j).forward 0 hzero, ?_, ?_, G.base_preserving j hzero⟩
    · have hc := ((G.embedding j).forward_smooth 0 hzero).continuousOn
      exact continuousOn_univ.mp (hc.mono hj)
    · have ho := cylinder_isOpen_forward_image (G.embedding j)
        (G.exhaustion.space_open j) 0 hzero
      exact (congrArg IsOpen (congrArg
        (fun V : Set G.limit.carrier.carrier => (G.embedding j).forward 0 hzero '' V)
          hfull)).mp ho
  have hmap' : ∃ f : G.limit.carrier.carrier →
      ((S.flow (G.subsequence j)).slice (S.base (G.subsequence j)).1).carrier,
      Continuous f ∧ IsOpen (f '' univ) ∧
        (⟨(S.base (G.subsequence j)).1, f G.limit.base⟩ :
          (S.flow (G.subsequence j)).point) = S.base (G.subsequence j) := by
    let P : ℝ → Prop := fun t =>
      ∃ f : G.limit.carrier.carrier → ((S.flow (G.subsequence j)).slice t).carrier,
        Continuous f ∧ IsOpen (f '' univ) ∧
          (⟨t, f G.limit.base⟩ : (S.flow (G.subsequence j)).point) = S.base (G.subsequence j)
    have htime : (S.base (G.subsequence j)).1 + 0 / S.scale (G.subsequence j) =
        (S.base (G.subsequence j)).1 := by simp
    exact (congrArg P htime).mp hmap
  obtain ⟨f, hf, hfo, hfb⟩ := hmap'
  have hfbase : f G.limit.base = (S.base (G.subsequence j)).2 :=
    eq_of_heq (Sigma.mk.inj hfb).2
  have hK : IsCompact (f '' univ) := hcompact.image hf
  have hmeet : (U j ∩ f '' univ).Nonempty :=
    ⟨(S.base (G.subsequence j)).2, hbase j, G.limit.base, mem_univ _, hfbase⟩
  exact hescape j (f '' univ) hK ((hU j).subset_isClopen ⟨hK.isClosed, hfo⟩ hmeet)



theorem terminalBlowupSequence_limit_not_isCompact
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
    [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
    [∀ k, SecondCountableTopology (M k)]
    {F : ℕ → GeneralizedRicciFlowData.{u}} {T : ℕ → ℝ}
    (H : ∀ k, SingularTimeAssumptions (F k) (T k) (M k))
    (Q : ∀ k, SingularLimitConclusion (H k))
    (x : ∀ k, ((Q k).extension.extended.slice (T k)).carrier)
    (hpos : ∀ k, 0 < ((Q k).extension.extended.connection (T k)).scalarCurvature (x k))
    (hdiv : Tendsto (fun k =>
      ((Q k).extension.extended.connection (T k)).scalarCurvature (x k)) atTop atTop)
    {accuracy : ℕ → ℝ} (horn : ∀ k, StrongHorn (Q k).extension (accuracy k))
    (hx : ∀ k, x k ∈ (horn k).carrier) {J : Set ℝ}
    (G : GeneralizedBlowupConvergence (terminalBlowupSequence H Q x hpos hdiv) J) :
    ¬ IsCompact (univ : Set G.limit.carrier.carrier) := by
  exact blowupLimit_not_isCompact_of_source_regions G
    (fun k => (horn (G.subsequence k)).carrier)
    (fun k => horn_isPreconnected_carrier (horn (G.subsequence k)))
    (fun k => horn_carrier_not_subset_compact (horn (G.subsequence k)))
    (fun k => hx (G.subsequence k))

end PoincareConjecture.M32
