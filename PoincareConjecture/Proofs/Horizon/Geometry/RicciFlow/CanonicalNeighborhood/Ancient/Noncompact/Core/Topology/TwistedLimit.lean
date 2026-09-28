import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Topology.TwistedObstruction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Topology.ProjectiveProduct











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture

open CoreTopology

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}



theorem M27TwistedSphereLineFlowCertificate.not_compact_strip_transport
    (C : M27TwistedSphereLineFlowCertificate K)
    {N : Type v} [TopologicalSpace N] [T2Space N]
    [SimplyConnectedSpace N] [LocallyPathConnectedSpace N]
    (E : OpenPartialHomeomorph M N)
    (hstrip : ∀ p : UnitTwoSphere × ℝ, |p.2| ≤ 2 → C.cover p ∈ E.source) : False := by
  let j : TwistedStrip → UnitTwoSphere × ℝ := fun p => (p.1, p.2.val)
  have hj : Topology.IsOpenEmbedding j :=
    Topology.IsOpenEmbedding.id.prodMap
      (isOpen_Ioo (a := (-2 : ℝ)) (b := 2)).isOpenEmbedding_subtypeVal
  have hjdeck (p : TwistedStrip) : j (stripDeck p) = m27TwistedProductInvolution (j p) := rfl
  have hmem (p : TwistedStrip) : C.cover (j p) ∈ E.source :=
    hstrip (j p) (abs_le.mpr ⟨p.2.property.1.le, p.2.property.2.le⟩)
  let F : TwistedStrip → E.source := fun p => ⟨C.cover (j p), hmem p⟩
  have hFlocal : IsLocalHomeomorph F :=
    IsLocalHomeomorph.of_comp (g := (Subtype.val : E.source → M))
      (C.cover_local_diffeomorph.isLocalHomeomorph.comp hj.isLocalHomeomorph)
      E.open_source.isOpenEmbedding_subtypeVal.isLocalHomeomorph
      ((C.cover_local_diffeomorph.isLocalHomeomorph.continuous.comp
        hj.continuous).subtype_mk _)
  let f : TwistedStrip → N := E ∘ C.cover ∘ j
  have hf : IsLocalHomeomorph f :=
    E.isOpenEmbedding_restrict.isLocalHomeomorph.comp hFlocal
  apply no_twistedStrip_localHomeomorph f hf
  intro x y
  constructor
  · intro he
    have hc : C.cover (j x) = C.cover (j y) := E.injOn (hmem x) (hmem y) he
    rcases (C.cover_fibers (j x) (j y)).mp hc with h | h
    · exact Or.inl (hj.injective h)
    · exact Or.inr (hj.injective (h.trans (hjdeck x).symm))
  · rintro (rfl | rfl)
    · rfl
    · exact congrArg E ((C.cover_fibers (j x) (j (stripDeck x))).mpr
        (Or.inr (hjdeck x)))

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace




theorem M23TerminalExtension.not_twistedSphereLine_of_pointSouls
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (T : M23TerminalExtension G)
    (hsoul : ∀ k, Nonempty
      (RiemannianMetric.PointSoulData ((S.term k).flow.flow.metric 0))) :
    ¬ Nonempty (M27TwistedSphereLineFlowCertificate G.limit.flow) := by
  rintro ⟨C⟩
  have hcompact : IsCompact (C.cover '' (univ ×ˢ Icc (-2 : ℝ) 2)) :=
    (isCompact_univ.prod isCompact_Icc).image
      C.cover_local_diffeomorph.isLocalHomeomorph.continuous
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  obtain ⟨e, _, _, _⟩ := T.terminal_embedding
  let E := (e j).spatialHomeomorph (mem_Iic.mpr le_rfl) (G.exhaustion_open j)
  obtain ⟨P⟩ := hsoul (G.subsequence j)
  let : SimplyConnectedSpace (S.term (G.subsequence j)).carrier.carrier :=
    P.euclidean.symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  let : LocallyPathConnectedSpace (S.term (G.subsequence j)).carrier.carrier :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  apply C.not_compact_strip_transport E
  intro p hp
  exact hj (mem_image_of_mem C.cover ⟨mem_univ p.1, abs_le.mp hp⟩)

end PoincareConjecture
