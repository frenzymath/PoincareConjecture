import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.LimitConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.Retention
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.RetainedDisappearing
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Caps.Height
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.EventRebuild.Transport

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RepairedContinuationLimitBridge

open Surgery.Terminal.Gluing SurgeryEventRebuild

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)

def assembleNonemptyEvent
    (σ : Ico H.reference.tMinus T) (hclose : T - (F.parameters.h T) ^ 2 < σ.1)
    {ι : Type u} [Fintype ι]
    (J : ι → MetricSurgeryInput F.local_constants (N.limit.extension.extended.metric T))
    (R : ∀ i, MetricSurgeryResult F.standard_initial (J i))
    (U : Opens (N.limit.extension.extended.slice T).carrier) (hU : Nonempty U)
    (hd : Pairwise (fun i j => Disjoint
      ((J i).negativeHalf : Set (N.limit.extension.extended.slice T).carrier) (J j).negativeHalf))
    (hc : ∀ i, Disjoint (U : Set (N.limit.extension.extended.slice T).carrier)
      (J i).neck.central_sphere)
    (hneck : Pairwise (fun i j => Disjoint (J i).neck.carrier (J j).neck.carrier))
    (hUn : ∀ i, (U : Set (N.limit.extension.extended.slice T).carrier) ∩
      (J i).neck.carrier = (J i).negativeHalf)
    (hfront : frontier (U : Set (N.limit.extension.extended.slice T).carrier) ⊆
      ⋃ i, (J i).neck.central_sphere)
    (hcompact : IsCompact (closure (U : Set (N.limit.extension.extended.slice T).carrier)))
    (hcore : {x | N.limit.terminal_scalar x ≤ I.rho⁻¹ ^ 2} ⊆ U)
    (htime : ∀ i, (J i).time = T)
    (hdelta : ∀ i, (J i).neck.epsilon = F.parameters.delta T)
    (hscale : ∀ i, (J i).neck.scale = F.parameters.h T)
    (future : ℝ → SliceMetric.{u})
    (hPast : ∀ t, t < T → (⟨F.slice t, F.metric t⟩ : SliceMetric.{u}) = future t)
    (hPost : (⟨cutCarrier J R U hU hd hc, cutMetric J R U hU hd hc⟩ : SliceMetric.{u}) =
      future T) :
    SurgeryEventData F.standard_initial F.local_constants F.parameters
      (fun t => (future t).1) (fun t => (future t).2) T := by
  letI : Nonempty (N.limit.extension.extended.slice T).carrier := hU.map Subtype.val
  let r := B.referenceRebaseTime σ
  let L₀ := B.referenceLimitIdentify N.limit σ
  let A := referenceRetained U L₀
  let P := retainedMap J R U hU hd hc '' closure (U : Set _)
  let ret := referenceRetention J R U hU hd hc hneck hUn hfront L₀
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let C : Fin (Fintype.card ι) → SurgeryCapChart F.standard_initial
      (cutCarrier J R U hU hd hc) (cutMetric J R U hU hd hc) (F.parameters.h T) :=
    fun i => (capChart J R U hU hd hc (e i)).atHeight (hscale (e i))
  let d := Classical.choose (B.exists_reference_disappearing_cover U hcore σ)
  have hdcover := Classical.choose_spec (B.exists_reference_disappearing_cover U hcore σ)
  have hm := hPast σ.1 σ.2.2
  have hT := hPost
  refine {
    tMinus := σ.1
    tMinus_nonnegative := F.time_domain_nonnegative (I.last_slab.time_subset r.2)
    tMinus_lt := σ.2.2
    preterminal_close := hclose
    pre_flow := flow hm (I.last_slab.rebaseFlow r)
    pre_identify := fun t => diffeomorph hm (hPast t.1 t.2.2) (I.last_slab.rebaseIdentify r t)
    pre_initial := by
      intro x
      obtain ⟨y, rfl⟩ := (identify _ _ hm).surjective x
      exact (diffeomorph_apply hm hm
        (I.last_slab.rebaseIdentify r ⟨σ.1, le_rfl, σ.2.2⟩) y).trans
          (congrArg (identify _ _ hm) (I.last_slab.rebaseIdentify_initial r y))
    pre_metric := fun t => diffeomorph_flow_metric_pullback hm (hPast t.1 t.2.2)
      (I.last_slab.rebaseFlow r) t.1 (I.last_slab.rebaseIdentify r t)
      (I.last_slab.rebase_metric r t)
    regular_limit := relabel (C := fun p => Set p.1.carrier) hm
      (B.reference_identify σ ⁻¹' H.reference.regularLimitSet)
    regular_limit_eq := ?_
    regular_limit_open := ?_
    terminal := N.limit.extension.extended.slice T
    limit_identify := regionSource hm (N.limit.extension.extended.slice T)
      (B.reference_identify σ ⁻¹' H.reference.regularLimitSet) univ L₀
    limit_metric := N.limit.extension.extended.metric T
    limit_connection := N.limit.extension.extended.connection T
    metric_converges := ?_
    retained_pre := relabel (C := fun p => Set p.1.carrier) hm A
    retained_pre_compact := ?_
    retained_pre_subset := ?_
    low_curvature_retained := ?_
    retained_post := relabel (C := fun p => Set p.1.carrier) hT P
    retained_post_compact := ?_
    retention := region hm hT A P ret
    retained_metric := ?_
    cap_count := Fintype.card ι
    caps := relabel (C := fun p => Fin (Fintype.card ι) →
      SurgeryCapChart F.standard_initial p.1 p.2 (F.parameters.h T)) hT C
    cap_disjoint := ?_
    post_cover := ?_
    cap_boundary := ?_
    necks := fun i => J (e i)
    neck_carrier_disjoint := fun i j hij => hneck (e.injective.ne hij)
    neck_time := fun i => htime (e i)
    neck_delta := fun i => hdelta (e i)
    neck_scale := fun i => hscale (e i)
    pre_boundary := ?_
    boundary_correspondence := ?_
    neck_negative_retained := ?_
    neck_positive_discarded := ?_
    local_result := fun i => R (e i)
    local_embed := relabel
      (C := fun p => ∀ i : Fin (Fintype.card ι), (R (e i)).output.carrier → p.1.carrier)
      hT (fun i => capInclusion J R U hU hd hc (e i))
    local_embed_smooth := ?_
    local_embed_injective := ?_
    local_metric := ?_
    local_tip := ?_
    local_cap_image := ?_
    local_retention := ?_
    disappearing_start := d
    disappearing_start_bounds := ⟨hdcover.1, hdcover.2.1⟩
    disappearing_curvature := ?_
    disappearing_cover := ?_ }
  all_goals
    try dsimp only [flow, diffeomorph, relabel, regionSource, region] at *
    generalize hval : future σ.1 = m at *
    clear hval
    subst m
    generalize hval : future T = b at *
    clear hval
    subst b
  · exact B.reference_regularLimit_eq σ
  · exact B.reference_regularLimit_open N.limit σ
  · have h := B.reference_surgeryMetricLimitOn N.limit σ
    rw [N.limit.terminal_metric_eq] at h
    exact h
  · exact referenceRetained_compact U L₀ hcompact
  · exact referenceRetained_subset U L₀
  · rw [referenceRetained_image]
    intro x hx
    apply subset_closure
    apply hcore
    rw [N.limit.terminal_scalar_eq]
    simpa only [I.rho_eq] using hx
  · exact retainedMap_image_compact J R U hU hd hc hneck hUn hfront hcompact
  · exact referenceRetention_metric J R U hU hd hc hneck hUn hfront L₀
      (B.reference_regularLimit_open N.limit σ)
  · intro i j hij
    exact capChart_disjoint J R U hU hd hc (e.injective.ne hij)
  · change P ∪ (⋃ i, (capChart J R U hU hd hc (e i)).carrier) = univ
    rw [e.surjective.iUnion_comp (fun i => (capChart J R U hU hd hc i).carrier)]
    dsimp only [P]
    rw [retainedMap_image_eq_retainedPost J R U hU hd hc hneck hUn hfront]
    exact retainedPost_cover J R U hU hd hc
  · intro i
    change P ∩ (capChart J R U hU hd hc (e i)).carrier =
      frontier (capChart J R U hU hd hc (e i)).carrier
    dsimp only [P]
    rw [retainedMap_image_eq_retainedPost J R U hU hd hc hneck hUn hfront]
    exact retainedPost_inter_cap J R U hU hd hc (e i)
  · change frontier A = ⋃ i, L₀.inverse '' (J (e i)).neck.central_sphere
    rw [e.surjective.iUnion_comp (fun i => L₀.inverse '' (J i).neck.central_sphere)]
    exact referenceRetained_frontier J R U hU hd hc hneck hUn hfront L₀ hcompact
  · intro i
    exact referenceRetention_boundary J R U hU hd hc hneck hUn hfront L₀ (e i)
  · intro i
    exact referenceRetained_negative J U hUn L₀ (e i)
  · intro i
    exact referenceRetained_positive J U hUn L₀ (e i)
  · intro i
    exact (capInclusion_localDiffeomorph J R U hU hd hc (e i)).contMDiff
  · intro i
    exact (capInclusion_openEmbedding J R U hU hd hc (e i)).injective
  · intro i
    exact capInclusion_metric J R U hU hd hc (e i)
  · intro i
    rfl
  · intro i
    rfl
  · intro i x hx
    exact referenceRetention_local J R U hU hd hc hneck hUn hfront L₀ (e i) x hx
  · intro a ha
    obtain ⟨s, hs, hsT, htail⟩ := B.reference_uniform_scalar_tail_off_open U hcore σ a
      (I.rho_eq ▸ ha)
    refine ⟨s, hs.le, hsT, fun t ht x hx => htail t ht x ?_⟩
    rwa [← referenceRetained_interior J R U hU hd hc hneck hUn hfront L₀]
  · intro t ht x hx
    apply hdcover.2.2 t ht x
    rwa [← referenceRetained_interior J R U hU hd hc hneck hUn hfront L₀]

end PoincareConjecture.RepairedContinuationLimitBridge
