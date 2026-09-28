import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.M28.Mathlib.FrontierCrossing

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

omit [T2Space M] in
private theorem core_subset_closed_core (K : CapCertificate g) :
    K.core ⊆ K.closed_core := by
  rw [K.core_eq_interior_closed_core]
  exact interior_subset

omit [T2Space M] in
private theorem closed_core_subset_carrier (K : CapCertificate g) :
    K.closed_core ⊆ K.carrier := by
  intro x hx
  rw [K.closed_core_eq_complement_end] at hx
  exact hx.1

private theorem literal_side_cover (K : CapCertificate g) {T0 : Set M}
    (hT : IsPreconnected T0)
    (havoid : Disjoint T0 K.boundary_sphere) :
    T0 ⊆ K.core ∨ T0 ⊆ K.closed_coreᶜ := by
  have hopenCore : IsOpen K.core := by
    rw [K.core_eq_interior_closed_core]
    exact isOpen_interior
  have hclosed : IsClosed K.closed_core := K.closed_core_compact.isClosed
  have hdis : Disjoint K.core K.closed_coreᶜ :=
    disjoint_compl_right.mono_left (core_subset_closed_core K)
  have hcover : T0 ⊆ K.core ∪ K.closed_coreᶜ := by
    intro x hx
    by_cases hclosedx : x ∈ K.closed_core
    · by_cases hcorex : x ∈ K.core
      · exact Or.inl hcorex
      · have hfront : x ∈ frontier K.closed_core := by
          rw [frontier, hclosed.closure_eq]
          refine ⟨hclosedx, ?_⟩
          rw [← K.core_eq_interior_closed_core]
          exact hcorex
        have hboundary : x ∈ K.boundary_sphere := by
          rw [← K.core_frontier_eq_boundary]
          exact hfront
        exact False.elim (Set.disjoint_left.mp havoid hx hboundary)
    · exact Or.inr hclosedx
  exact hT.subset_or_subset hopenCore hclosed.isOpen_compl hdis hcover

theorem exists_literal_carrier_cap_boundary_contact
    {T0 : Set M} (K : CapCertificate g)
    (hT : IsPreconnected T0)
    {x p q : M}
    (hxT : x ∈ T0) (hxcore : x ∈ K.core)
    (hpT : p ∈ T0) (hpout : p ∉ K.carrier)
    (hqT : q ∈ T0) (hqout : q ∉ K.carrier) :
    (T0 ∩ K.boundary_sphere).Nonempty := by
  by_contra hnone
  have havoid : Disjoint T0 K.boundary_sphere := by
    apply disjoint_iff_inter_eq_empty.mpr
    exact Set.not_nonempty_iff_eq_empty.mp hnone
  have hend :
      (p ∈ T0 ∧ p ∉ K.carrier) ∧ (q ∈ T0 ∧ q ∉ K.carrier) :=
    ⟨⟨hpT, hpout⟩, ⟨hqT, hqout⟩⟩
  rcases literal_side_cover K hT havoid with hcore | hout
  · have hpcore := hcore hpT
    have hpcarrier := closed_core_subset_carrier K
      (core_subset_closed_core K hpcore)
    exact hend.1.2 hpcarrier
  · have hxout := hout hxT
    exact hxout (core_subset_closed_core K hxcore)

end PoincareConjecture.M28
