import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Theory
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

def ConnectedNeckCapCover.neckOnlyCover_of_no_cap_core
    {g : RiemannianMetric 3 M} (H : ConnectedNeckCapCover g)
    (hno : ∀ C ∈ H.caps, Disjoint H.X C.core) : NeckOnlyCover g where
  epsilon := H.epsilon
  epsilon_pos := H.epsilon_pos
  epsilon_threshold := H.epsilon_threshold
  epsilon_threshold_pos := H.epsilon_threshold_pos
  epsilon_threshold_le_one_two_hundred := H.epsilon_threshold_le_one_two_hundred
  epsilon_le_threshold := H.epsilon_le_threshold
  X := H.X
  connected_X := H.connected_X
  necks := H.necks
  pointwise_center_cover := by
    intro x hx
    rcases H.pointwise_cover x hx with hneck | ⟨C, hC, hxC⟩
    · exact hneck
    · exact False.elim (Set.disjoint_left.mp (hno C hC) hx hxC)
  neck_epsilon := H.neck_epsilon

theorem ConnectedNeckCapCover.exists_maximal_cap_or_neck_cover_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ H : ConnectedNeckCapCover g, H.epsilon ≤ ε₀ →
          (∃ C ∈ H.caps, (H.X ∩ C.carrier).Nonempty ∧
            ∀ D ∈ H.caps, C.carrier ⊆ D.carrier →
              Disjoint (frontier C.carrier) D.closed_core) ∨
          (∀ x ∈ H.X, ∃ N ∈ H.necks, N.center = x) := by
  obtain ⟨ε₀, hε₀, hsmall, hmax⟩ := ConnectedNeckCapCover.exists_maximal_cap_growth_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g H hε
  by_cases hcap : ∃ C ∈ H.caps, (H.X ∩ C.core).Nonempty
  · obtain ⟨C₀, hC₀, x, hx, hxC₀⟩ := hcap
    obtain ⟨C, hC, hcontain, hmaxC⟩ := hmax H hε C₀ hC₀
    exact Or.inl ⟨C, hC, ⟨x, hx, hcontain (C₀.core_subset_carrier hxC₀)⟩, hmaxC⟩
  · right
    intro x hx
    rcases H.pointwise_cover x hx with hneck | ⟨C, hC, hxC⟩
    · exact hneck
    · exact False.elim (hcap ⟨C, hC, x, hx, hxC⟩)

omit [T2Space M] in

theorem ConnectedNeckCapCover.frontier_cover_of_maximal_cap
    {g : RiemannianMetric 3 M} (H : ConnectedNeckCapCover g) (C : CapCertificate g)
    (hmax : ∀ D ∈ H.caps, C.carrier ⊆ D.carrier →
      Disjoint (frontier C.carrier) D.closed_core)
    {x : M} (hx : x ∈ H.X) (hfront : x ∈ frontier C.carrier) :
    (∃ N ∈ H.necks, N.center = x) ∨
      (∃ D ∈ H.caps, x ∈ D.core ∧ ¬ C.carrier ⊆ D.carrier) := by
  rcases H.pointwise_cover x hx with hneck | ⟨D, hD, hxD⟩
  · exact Or.inl hneck
  · refine Or.inr ⟨D, hD, hxD, ?_⟩
    intro hCD
    exact Set.disjoint_left.mp (hmax D hD hCD) hfront (D.core_subset_closed_core hxD)

omit [T2Space M] in

theorem ConnectedNeckCapCover.boundary_meets_of_maximal_frontier_core_contact
    {g : RiemannianMetric 3 M} (H : ConnectedNeckCapCover g) (C D : CapCertificate g)
    (hmax : ∀ A ∈ H.caps, C.carrier ⊆ A.carrier →
      Disjoint (frontier C.carrier) A.closed_core)
    (hD : D ∈ H.caps) (hcontact : (frontier C.carrier ∩ D.core).Nonempty) :
    (D.boundary_sphere ∩ C.carrier).Nonempty := by
  by_contra h
  have hdis : Disjoint C.carrier D.boundary_sphere := by
    apply Disjoint.symm
    exact disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h)
  have hcore := D.subset_core_of_disjoint_boundary_of_frontier_core_contact
    C.isConnected_carrier.isPreconnected hdis hcontact
  obtain ⟨x, hx, hxD⟩ := hcontact
  exact Set.disjoint_left.mp (hmax D hD (hcore.trans D.core_subset_carrier)) hx
    (D.core_subset_closed_core hxD)

theorem ConnectedNeckCapCover.exists_maximal_cap_frontier_closing_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (H : ConnectedNeckCapCover g) (C D : CapCertificate g),
          H.epsilon ≤ ε₀ → C ∈ H.caps → D ∈ H.caps →
          (H.X ∩ C.carrier).Nonempty →
          (∀ A ∈ H.caps, C.carrier ⊆ A.carrier →
            Disjoint (frontier C.carrier) A.closed_core) →
          (frontier C.carrier ∩ D.core).Nonempty →
          H.X ⊆ C.carrier ∪ D.carrier ∧
            C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center ∧
              IsCompact (C.carrier ∪ D.carrier) := by
  obtain ⟨ε₀, hε₀, hsmall, hclose⟩ := CapCertificate.exists_frontier_contact_closing_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g H C D hε hC hD hmeet hmax hcontact
  have hnoncontain : ¬ C.carrier ⊆ D.carrier := by
    intro hCD
    obtain ⟨x, hx, hxD⟩ := hcontact
    exact Set.disjoint_left.mp (hmax D hD hCD) hx (D.core_subset_closed_core hxD)
  obtain ⟨heq, hc⟩ := hclose C D ((H.cap_epsilon C hC).trans_le hε)
    ((H.cap_epsilon D hD).trans (H.cap_epsilon C hC).symm) hcontact hnoncontain
  refine ⟨?_, heq, hc⟩
  rw [heq]
  obtain ⟨p, hpX, hpC⟩ := hmeet
  rw [connectedComponent_eq (C.carrier_subset_boundary_component hpC)]
  exact H.connected_X.isPreconnected.subset_connectedComponent hpX

theorem ConnectedNeckCapCover.exists_cap_frontier_or_neck_cover_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ H : ConnectedNeckCapCover g, H.epsilon ≤ ε₀ →
          (∃ C ∈ H.caps, (H.X ∩ C.carrier).Nonempty ∧
            (∀ D ∈ H.caps, C.carrier ⊆ D.carrier →
              Disjoint (frontier C.carrier) D.closed_core) ∧
            ((∃ D ∈ H.caps, H.X ⊆ C.carrier ∪ D.carrier ∧
              C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center ∧
                IsCompact (C.carrier ∪ D.carrier)) ∨
              ∀ x ∈ H.X ∩ frontier C.carrier, ∃ N ∈ H.necks, N.center = x)) ∨
          (∀ x ∈ H.X, ∃ N ∈ H.necks, N.center = x) := by
  obtain ⟨ε₁, hε₁, hsmall, hmax⟩ := exists_maximal_cap_or_neck_cover_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hclose⟩ := exists_maximal_cap_frontier_closing_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g H hε
  rcases hmax H (hε.trans (min_le_left _ _)) with ⟨C, hC, hmeet, hmaxC⟩ | hneck
  · left
    refine ⟨C, hC, hmeet, hmaxC, ?_⟩
    by_cases hcap : ∃ D ∈ H.caps, (frontier C.carrier ∩ D.core).Nonempty
    · obtain ⟨D, hD, hcontact⟩ := hcap
      exact Or.inl ⟨D, hD, hclose H C D (hε.trans (min_le_right _ _))
        hC hD hmeet hmaxC hcontact⟩
    · right
      rintro x ⟨hx, hxfront⟩
      rcases H.pointwise_cover x hx with hneck | ⟨D, hD, hxD⟩
      · exact hneck
      · exact False.elim (hcap ⟨D, hD, x, hxfront, hxD⟩)
  · exact Or.inr hneck

omit [T2Space M] in

theorem BalancedNeckChain.epsilon_eq_of_source_subset
    {g : RiemannianMetric 3 M} {ε : ℝ}
    (chain : BalancedNeckChain g ε) (H : ConnectedNeckCapCover g)
    (hsource : chain.source_necks ⊆ H.necks) :
    ε = H.epsilon := by
  obtain ⟨i, hi⟩ := chain.active_nonempty
  obtain ⟨N, hN, hsame⟩ := chain.selected i hi
  exact (chain.epsilon_eq i hi).symm.trans
    (hsame.1.trans (H.neck_epsilon N (hsource hN)))

omit [T2Space M] in

theorem EpsilonTubeCertificate.epsilon_eq_of_source_subset
    {g : RiemannianMetric 3 M} {X : Set M}
    (tube : EpsilonTubeCertificate g X) (H : ConnectedNeckCapCover g)
    (hsource : tube.chain.source_necks ⊆ H.necks) :
    tube.epsilon = H.epsilon :=
  tube.chain.epsilon_eq_of_source_subset H hsource

def RepairedNeckCapTopologyData.of_single_cap
    {g : RiemannianMetric 3 M} (H : ConnectedNeckCapCover g)
    (C : CapCertificate g) (hC : C ∈ H.caps)
    (hX : H.X ⊆ C.carrier) :
    RepairedNeckCapTopologyData g H := by
  refine
    { region := .singleCap C hX
      compatible := ?_ }
  exact ⟨H.cap_epsilon C hC, H.cap_constant_bound C hC⟩

omit [T2Space M] in

theorem CapCertificate.contains_of_disjoint_frontier
    {g : RiemannianMetric 3 M} (C : CapCertificate g) {X : Set M}
    (hX : IsConnected X) (hmeet : (X ∩ C.carrier).Nonempty)
    (hfront : Disjoint X (frontier C.carrier)) : X ⊆ C.carrier := by
  let : ConnectedSpace X := isConnected_iff_connectedSpace.mp hX
  have hopen := isClopen_preimage_val C.carrier_open hfront.symm
  obtain ⟨x, hx, hxC⟩ := hmeet
  have heq := hopen.eq_univ ⟨⟨x, hx⟩, hxC⟩
  intro y hy
  have hmem : (⟨y, hy⟩ : X) ∈ Subtype.val ⁻¹' C.carrier := by
    rw [heq]
    exact mem_univ _
  exact hmem

def RepairedNeckCapTopologyData.of_cap_frontier_disjoint
    {g : RiemannianMetric 3 M} (H : ConnectedNeckCapCover g)
    (C : CapCertificate g) (hC : C ∈ H.caps)
    (hmeet : (H.X ∩ C.carrier).Nonempty)
    (hfront : Disjoint H.X (frontier C.carrier)) :
    RepairedNeckCapTopologyData g H :=
  .of_single_cap H C hC
    (C.contains_of_disjoint_frontier H.connected_X hmeet hfront)

def RepairedNeckCapTopologyData.of_tube
    {g : RiemannianMetric 3 M} (H : ConnectedNeckCapCover g)
    (tube : EpsilonTubeCertificate g H.X)
    (hsource : tube.chain.source_necks ⊆ H.necks) :
    RepairedNeckCapTopologyData g H := by
  exact
    { region := .tube tube
      compatible := tube.epsilon_eq_of_source_subset H hsource }

def RepairedNeckCapTopologyData.of_capped_tube
    {g : RiemannianMetric 3 M} (H : ConnectedNeckCapCover g)
    (certificate : CappedTubeCertificate g)
    (hcap : certificate.cap ∈ H.caps)
    (hsource : certificate.tube.chain.source_necks ⊆ H.necks)
    (hX : H.X ⊆ certificate.carrier) :
    RepairedNeckCapTopologyData g H := by
  refine
    { region := .cappedTube certificate hX
      compatible := ?_ }
  exact
    ⟨H.cap_epsilon certificate.cap hcap,
      certificate.tube.epsilon_eq_of_source_subset H hsource,
      H.cap_constant_bound certificate.cap hcap,
      ⟨certificate.attachment⟩⟩

def RepairedNeckCapTopologyData.of_double_capped_tube
    {g : RiemannianMetric 3 M} (H : ConnectedNeckCapCover g)
    (certificate : DoubleCappedTubeCertificate g)
    (kind : ClosedComponentKind)
    (component : ClosedComponentCertificate kind certificate.carrier)
    (hcap₁ : certificate.cap₁ ∈ H.caps)
    (hcap₂ : certificate.cap₂ ∈ H.caps)
    (hsource : certificate.tube.chain.source_necks ⊆ H.necks)
    (hX : H.X ⊆ certificate.carrier) :
    RepairedNeckCapTopologyData g H := by
  refine
    { region := .doubleCappedTube certificate kind component hX
      compatible := ?_ }
  exact
    ⟨H.cap_epsilon certificate.cap₁ hcap₁,
      H.cap_epsilon certificate.cap₂ hcap₂,
      certificate.tube.epsilon_eq_of_source_subset H hsource,
      H.cap_constant_bound certificate.cap₁ hcap₁,
      H.cap_constant_bound certificate.cap₂ hcap₂⟩

def RepairedNeckCapTopologyData.of_two_caps
    {g : RiemannianMetric 3 M} (H : ConnectedNeckCapCover g)
    {Y : Set M} (kind : ClosedComponentKind)
    (C D : CapCertificate g)
    (component : ClosedComponentCertificate kind Y)
    (union_eq : Y = C.carrier ∪ D.carrier)
    (hC : C ∈ H.caps) (hD : D ∈ H.caps)
    (hX : H.X ⊆ Y) :
    RepairedNeckCapTopologyData g H := by
  refine
    { region := .twoCaps kind C D component union_eq hX
      compatible := ?_ }
  exact
    ⟨H.cap_epsilon C hC, H.cap_epsilon D hD,
      H.cap_constant_bound C hC, H.cap_constant_bound D hD⟩

end PoincareConjecture
