import PoincareConjecture.Proofs.M25.AppA_21_Local.CappedCoreAlternative
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCommonSphereProducer
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCommonSphereComponent
import Mathlib.Topology.Connected.Clopen









set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



theorem ConnectedNeckCapCover.exists_repairedData_or_compact_capped_core_component :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : ConnectedNeckCapCover g), H.epsilon ≤ epsilon0 →
      ∀ (x : M), x ∈ H.X → (∃ C ∈ H.caps, x ∈ C.core) →
      Nonempty (RepairedNeckCapTopologyData g H) ∨
      (∃ C0 ∈ H.caps, x ∈ C0.core ∧
        (∀ C1 ∈ H.caps,
          ¬ (C0.carrier \ C0.end_neck.region (H.epsilon⁻¹ / 2) H.epsilon⁻¹ ⊆
            C1.core)) ∧
        ∃ (b : ℤ) (D : BalancedNeckChain g C0.epsilon),
          0 ≤ b ∧ D.shape = ChainShape.finite 0 b ∧
          D.source_necks = insert C0.end_neck H.necks ∧ D.neck 0 = C0.end_neck ∧
          (∀ i ∈ D.shape.active, (D.neck i).IsSeparating) ∧
          (∀ i ∈ D.shape.active, 0 < i →
            (D.neck i).center ∈ H.X \ C0.carrier) ∧
          (∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
            closure ((D.neck i).region (C0.epsilon⁻¹ / 2) C0.epsilon⁻¹) ⊆
                (D.neck (i + 1)).carrier ∧
              closure ((D.neck (i + 1)).region
                  (-C0.epsilon⁻¹) (-C0.epsilon⁻¹ / 2)) ⊆ (D.neck i).carrier) ∧
          (∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
            (D.neck (i + 1)).center ∈ closure ((D.neck i).region 0 C0.epsilon⁻¹) ∧
              (D.neck (i + 1)).center ∉ (D.neck i).carrier) ∧
          ∃ K : CappedTubeCertificate g,
            K.cap = C0 ∧ K.tube.epsilon = H.epsilon ∧ HEq K.tube.chain D ∧
            K.tube.carrier = (⋃ i ∈ D.shape.active, (D.neck i).carrier) ∧
            K.carrier = C0.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier) ∧
            ∃ C1 ∈ H.caps, ∃ y ∈ H.X,
              y ∈ C1.core ∧ y ∉ K.carrier ∧
              y ∈ closure ((D.neck b).region 0 C0.epsilon⁻¹) ∧
              (K.carrier ∩ C1.boundary_sphere).Nonempty ∧
              let W := K.carrier ∪ C1.carrier
              H.X ⊆ W ∧ IsCompact W ∧ IsClopen W ∧ IsConnected W ∧
                ∃ z : M, W = connectedComponent z) := by
  classical
  obtain ⟨epsilonA, hA, hAcap, hfrontier⟩ :=
    ConnectedNeckCapCover.exists_repairedData_or_finite_capped_core_frontier.{u}
  obtain ⟨epsilonG, hG, _, hgraph⟩ :=
    CapCertificate.exists_common_outward_graph_of_finite_core_frontier.{u}
  refine ⟨min epsilonA epsilonG, lt_min hA hG,
    (min_le_left _ _).trans hAcap, ?_⟩
  intro M _ _ _ _ _ _ g H hepsilon x hx hseed
  rcases hfrontier H (hepsilon.trans (min_le_left _ _)) x hx hseed with
    hdata | hfinite
  · exact Or.inl hdata
  obtain ⟨C0, hC0, hx0, hno, b, D, hb, hshape, hsource, hstart,
    hsep, hcenters, hquarters, hincidence, K, hKcap, hKe, hKchain,
    hKtube, hKcarrier, C1, hC1, y, hyX, hycore, hyout, hyfront, hboundary⟩ := hfinite
  have hCe : C0.epsilon = H.epsilon := H.cap_epsilon C0 hC0
  have hC1e : C1.epsilon = C0.epsilon := (H.cap_epsilon C1 hC1).trans hCe.symm
  have heG : C0.epsilon ≤ epsilonG := by
    rw [hCe]
    exact hepsilon.trans (min_le_right _ _)
  have hnoC1 : ¬ (C0.carrier \
      C0.end_neck.region (C0.epsilon⁻¹ / 2) C0.epsilon⁻¹ ⊆ C1.core) := by
    simpa only [hCe] using hno C1 hC1
  let V : TopologicalSpace.Opens M :=
    ⟨C0.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier),
      C0.carrier_open.union
        (isOpen_iUnion fun i => isOpen_iUnion fun _ => (D.neck i).carrier_open)⟩
  have hyVout : y ∉ (V : Set M) := by
    simpa only [hKcarrier, V, TopologicalSpace.Opens.coe_mk] using hyout
  have hmeet : ((V : Set M) ∩ C1.boundary_sphere).Nonempty := by
    simpa only [hKcarrier, V, TopologicalSpace.Opens.coe_mk] using hboundary
  obtain ⟨d, _, _, hyV, R, f, N, s, hR, _, _, _, hcore, _, hf, hfdom,
    hs, hlevel, hSV, _⟩ :=
    hgraph C0 C1 D heG hC1e hshape hstart hsep
      (fun i hi hi0 => (hcenters i hi hi0).2) hquarters hnoC1
      y hycore hyfront hyVout hmeet
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcompact, hclopen, hconnected,
    hcomponent⟩ :=
    C0.compact_union_component_of_common_outward_graph C1 V d.toHomeomorph
      R hR hcore f hf.continuous hfdom N s hs hlevel hSV y hycore hyV hyVout
  have hcompactW : IsCompact (K.carrier ∪ C1.carrier) := by
    simpa only [hKcarrier, V, TopologicalSpace.Opens.coe_mk] using hcompact
  have hclopenW : IsClopen (K.carrier ∪ C1.carrier) := by
    simpa only [hKcarrier, V, TopologicalSpace.Opens.coe_mk] using hclopen
  have hconnectedW : IsConnected (K.carrier ∪ C1.carrier) := by
    simpa only [hKcarrier, V, TopologicalSpace.Opens.coe_mk] using hconnected
  have hxK : x ∈ K.carrier := by
    rw [hKcarrier]
    exact Or.inl (C0.m25_core_subset_carrier hx0)
  have hXW : H.X ⊆ K.carrier ∪ C1.carrier :=
    H.connected_X.isPreconnected.subset_isClopen hclopenW ⟨x, hx, Or.inl hxK⟩
  refine Or.inr ⟨C0, hC0, hx0, hno, b, D, hb, hshape, hsource, hstart,
    hsep, hcenters, hquarters, hincidence, K, hKcap, hKe, hKchain,
    hKtube, hKcarrier, C1, hC1, y, hyX, hycore, hyout, hyfront, hboundary,
    hXW, hcompactW, hclopenW, hconnectedW,
    R.coordinate_map ((R.coordinate_inverse R.center).1, -C1.epsilon⁻¹ / 2), ?_⟩
  simpa only [hKcarrier, V, TopologicalSpace.Opens.coe_mk] using hcomponent

end PoincareConjecture
