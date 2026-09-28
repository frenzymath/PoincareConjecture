import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.Assembly


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RepairedContinuationLimitBridge

open Surgery.Terminal.Gluing SurgeryEventRebuild

private theorem regionSource_inverse_eq {s t : SliceMetric.{u}} (h : s = t)
    (Q : GeneralizedSliceCarrier.{u}) (V : Set s.1.carrier) (W : Set Q.carrier)
    (e : SurgeryRegionEquivalence s.1 Q V W) (x : Q.carrier) :
    (regionSource h Q V W e).inverse x = identify _ _ h (e.inverse x) := by
  subst t
  rfl

private theorem regionSource_image_eq {s t : SliceMetric.{u}} (h : s = t)
    (Q : GeneralizedSliceCarrier.{u}) (V : Set s.1.carrier) (W : Set Q.carrier)
    (e : SurgeryRegionEquivalence s.1 Q V W) (A : Set s.1.carrier) :
    (regionSource h Q V W e).map '' relabel (C := fun p => Set p.1.carrier) h A =
      e.map '' A := by
  subst t
  rfl

private theorem flow_identify_inner_eq {s t : SliceMetric.{u}} (h : s = t)
    {J : Set ℝ} (Q : RicciFlow 3 s.1.carrier J) (r : ℝ)
    (x : s.1.carrier) (v w : TangentSpace (𝓡 3) x) :
    ((flow h Q).metric r).inner (identify _ _ h x)
      (mfderiv (𝓡 3) (𝓡 3) (identify _ _ h) x v)
      (mfderiv (𝓡 3) (𝓡 3) (identify _ _ h) x w) = (Q.metric r).inner x v w := by
  subst t
  simp [flow, identify]

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)
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
    future T)

local notation "E" => B.assembleNonemptyEvent σ hclose J R U hU hd hc hneck hUn hfront
  hcompact hcore htime hdelta hscale future hPast hPost

def assembledEventSource : Diffeomorph (𝓡 3) (𝓡 3)
    (F.slice I.last_slab.start).carrier (future σ.1).1.carrier ∞ :=
  (I.last_slab.identify (B.referenceRebaseTime σ)).trans
    (identify _ _ (hPast σ.1 σ.2.2))

theorem assembleNonemptyEvent_tMinus : (E).tMinus = σ.1 := rfl

theorem assembleNonemptyEvent_terminal : (E).terminal = N.limit.extension.extended.slice T := rfl

theorem assembleNonemptyEvent_limit_metric : (E).limit_metric = N.limit.extension.extended.metric T := rfl

theorem assembleNonemptyEvent_cap_count : (E).cap_count = Fintype.card ι := rfl

theorem assembleNonemptyEvent_necks (i : Fin (Fintype.card ι)) :
    (E).necks i = J ((Fintype.equivFin ι).symm i) := rfl

theorem assembleNonemptyEvent_local_result (i : Fin (Fintype.card ι)) :
    (E).local_result i = R ((Fintype.equivFin ι).symm i) := rfl

theorem assembleNonemptyEvent_limit_map (x : (F.slice σ.1).carrier) :
    (E).limit_identify.map (identify _ _ (hPast σ.1 σ.2.2) x) =
      (letI : Nonempty (N.limit.extension.extended.slice T).carrier := hU.map Subtype.val
       (B.referenceLimitIdentify N.limit σ).map x) := by
  let : Nonempty (N.limit.extension.extended.slice T).carrier := hU.map Subtype.val
  exact regionSource_map (hPast σ.1 σ.2.2) _ _ _ (B.referenceLimitIdentify N.limit σ) x

theorem assembleNonemptyEvent_limit_inverse
    (x : (N.limit.extension.extended.slice T).carrier) :
    (E).limit_identify.inverse x = identify _ _ (hPast σ.1 σ.2.2)
      ((B.reference_identify σ).symm (N.limit.terminal_source x)) := by
  let : Nonempty (N.limit.extension.extended.slice T).carrier := hU.map Subtype.val
  exact regionSource_inverse_eq (hPast σ.1 σ.2.2) _ _ _
    (B.referenceLimitIdentify N.limit σ) x

theorem assembleNonemptyEvent_pre_identify (t : Ico σ.1 T) (x : (F.slice σ.1).carrier) :
    (E).pre_identify t (identify _ _ (hPast σ.1 σ.2.2) x) =
      identify _ _ (hPast t.1 t.2.2)
        (I.last_slab.rebaseIdentify (B.referenceRebaseTime σ) t x) :=
  diffeomorph_apply (hPast σ.1 σ.2.2) (hPast t.1 t.2.2)
    (I.last_slab.rebaseIdentify (B.referenceRebaseTime σ) t) x

theorem assembleNonemptyEvent_pre_identify_limit_inverse (t : Ico σ.1 T)
    (x : (N.limit.extension.extended.slice T).carrier) :
    (E).pre_identify t ((E).limit_identify.inverse x) =
      identify _ _ (hPast t.1 t.2.2)
        (I.last_slab.rebaseIdentify (B.referenceRebaseTime σ) t
          ((B.reference_identify σ).symm (N.limit.terminal_source x))) := by
  rw [assembleNonemptyEvent_limit_inverse, assembleNonemptyEvent_pre_identify]

theorem assembleNonemptyEvent_retained_image :
    (E).limit_identify.map '' (E).retained_pre =
      closure (U : Set (N.limit.extension.extended.slice T).carrier) := by
  let : Nonempty (N.limit.extension.extended.slice T).carrier := hU.map Subtype.val
  exact (regionSource_image_eq (hPast σ.1 σ.2.2) _ _ _
    (B.referenceLimitIdentify N.limit σ) _).trans
      (referenceRetained_image U (B.referenceLimitIdentify N.limit σ))

theorem assembleNonemptyEvent_source_identify (t : Ico σ.1 T)
    (x : (F.slice I.last_slab.start).carrier) :
    (E).pre_identify t (B.assembledEventSource σ future hPast x) =
      identify _ _ (hPast t.1 t.2.2)
        (I.last_slab.identify
          ⟨t.1, (B.referenceRebaseTime σ).2.1.trans t.2.1, t.2.2⟩ x) := by
  change (E).pre_identify t (identify _ _ (hPast σ.1 σ.2.2)
    (I.last_slab.identify (B.referenceRebaseTime σ) x)) = _
  rw [assembleNonemptyEvent_pre_identify, I.last_slab.rebaseIdentify_source]

theorem assembleNonemptyEvent_source_map (x : (F.slice I.last_slab.start).carrier) :
    (E).limit_identify.map (B.assembledEventSource σ future hPast x) =
      (letI : Nonempty (N.limit.extension.extended.slice T).carrier := hU.map Subtype.val
       N.limit.sourceInverse (B.core_map x)) := by
  let : Nonempty (N.limit.extension.extended.slice T).carrier := hU.map Subtype.val
  change (E).limit_identify.map (identify _ _ (hPast σ.1 σ.2.2)
    (I.last_slab.identify (B.referenceRebaseTime σ) x)) = _
  rw [assembleNonemptyEvent_limit_map]
  change N.limit.sourceInverse
    (B.reference_identify σ (I.last_slab.identify (B.referenceRebaseTime σ) x)) = _
  exact congrArg N.limit.sourceInverse (B.core_map_eq_reference_at σ x).symm

theorem assembleNonemptyEvent_source_metric (t : ℝ)
    (x : (F.slice I.last_slab.start).carrier) (v w : TangentSpace (𝓡 3) x) :
    ((E).pre_flow.metric t).inner (B.assembledEventSource σ future hPast x)
      (mfderiv (𝓡 3) (𝓡 3) (B.assembledEventSource σ future hPast) x v)
      (mfderiv (𝓡 3) (𝓡 3) (B.assembledEventSource σ future hPast) x w) =
        (I.last_slab.flow.metric t).inner x v w := by
  let e := I.last_slab.identify (B.referenceRebaseTime σ)
  let d := identify _ _ (hPast σ.1 σ.2.2)
  change ((flow (hPast σ.1 σ.2.2) (I.last_slab.rebaseFlow (B.referenceRebaseTime σ))).metric t).inner
    (d (e x)) (mfderiv (𝓡 3) (𝓡 3) (d ∘ e) x v)
    (mfderiv (𝓡 3) (𝓡 3) (d ∘ e) x w) = _
  rw [mfderiv_comp x (d.contMDiff.mdifferentiable (by simp) _)
    (e.contMDiff.mdifferentiable (by simp) _)]
  exact (flow_identify_inner_eq (hPast σ.1 σ.2.2)
    (I.last_slab.rebaseFlow (B.referenceRebaseTime σ)) t (e x)
    (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w)).trans
      (I.last_slab.rebaseFlow_source_metric (B.referenceRebaseTime σ) t x v w)

end PoincareConjecture.RepairedContinuationLimitBridge
