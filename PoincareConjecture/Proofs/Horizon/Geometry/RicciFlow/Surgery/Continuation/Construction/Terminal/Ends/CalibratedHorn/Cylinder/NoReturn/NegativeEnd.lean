import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.NoReturn.Prepend
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.RicciComparison.SphereTransport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.NoReturn.Tail
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Connected
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Finite.InitialEnd
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.SliceIsotopy
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Partition.Sides












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

namespace BalancedNeckChain




theorem prepend_no_return_of_epsilon_le :
    ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε)
        (P : EpsilonNeck g), ε ≤ (1 / 200) → P.epsilon = ε →
        ∀ a ∈ C.shape.active, (C.neck a).IsSeparating →
        (C.neck a).region (-ε⁻¹) (-ε⁻¹ / 2) ⊆ P.carrier →
        P.carrier ∩ (C.neck a).carrier ⊆
          P.region (-ε⁻¹ / 2) ε⁻¹ ∩ (C.neck a).region (-ε⁻¹) (ε⁻¹ / 2) →
        ∀ j ∈ C.shape.active, a ≤ j →
          Disjoint (C.neck j).carrier (P.region (-ε⁻¹) (-ε⁻¹ / 2)) := by
  intro M _ _ _ _ _ _ _ g ε C P hε heP a ha hsep hneg hwithin j hj haj
  have heA := C.epsilon_eq a ha
  have hepos : 0 < ε := heA ▸ (C.neck a).epsilon_pos
  have hi := inv_pos.mpr hepos
  rcases eq_or_lt_of_le haj with rfl | haj
  · apply disjoint_left.mpr
    intro x hxA hxP
    exact (not_lt_of_ge (hwithin ⟨hxP.1, hxA⟩).1.2.1.le) hxP.2.2
  have hactive : Ioc a j ⊆ C.shape.active :=
    fun i hi => C.shape.ordConnected_active.out ha hj ⟨hi.1.le, hi.2⟩
  let T : Set M := ⋃ i ∈ Ioc a j, (C.neck i).carrier
  have hT : IsPreconnected T := (C.isConnected_subchain_union
    (show (Ioc a j).Nonempty from ⟨j, haj, le_rfl⟩) inferInstance hactive).2
  obtain ⟨c, hc, havoid⟩ := C.exists_common_negative_end_cut ha (Finset.Ioc a j)
    (fun i hi => ⟨hactive (Finset.mem_Ioc.mp hi), (Finset.mem_Ioc.mp hi).1⟩)
    (b := -ε⁻¹ / 2) (by linarith)
  obtain ⟨s, hslo, hsc⟩ := exists_between hc.1
  have hs : s ∈ Ioo (-(C.neck a).epsilon⁻¹) (C.neck a).epsilon⁻¹ := by
    rw [heA]
    exact ⟨hslo, by linarith [hc.2]⟩
  have hsq : s < -(C.neck a).epsilon⁻¹ / 2 := by rw [heA]; exact hsc.trans hc.2
  have hcontained (q : UnitTwoSphere) : (C.neck a).coordinate_map (q, s) ∈ P.carrier := by
    apply hneg
    refine ⟨(C.neck a).coordinate_map_mem ⟨mem_univ _, hs⟩, ?_⟩
    rw [(C.neck a).coordinate_inverse_coordinate_map ⟨mem_univ _, hs⟩]
    exact ⟨hslo, hsc.trans hc.2⟩
  obtain ⟨f, hf, hdom, hrange, _⟩ := EpsilonNeck.sphereSlice_graph_and_isotopy_of_epsilon_le P (C.neck a)
    (heP.symm ▸ hε) (heA.symm ▸ hε) hs hcontained
  have hwithin' : P.carrier ∩ (C.neck a).carrier ⊆
      P.region (-P.epsilon⁻¹ / 2) P.epsilon⁻¹ ∩
        (C.neck a).region (-(C.neck a).epsilon⁻¹) ((C.neck a).epsilon⁻¹ / 2) := by
    simpa only [heP, heA] using hwithin
  have hdisj := P.disjoint_belowGraph_successor_upper (C.neck a) f hf.continuous hdom
    hs hrange hwithin'
  have hlower := P.successor_lower_subset_belowGraph (C.neck a) f hf.continuous hdom
    s hs hsq hrange.symm (by simpa only [heA] using hneg) hdisj
  have havoidT : Disjoint T
      (range (fun q : UnitTwoSphere => (C.neck a).coordinate_map (q, s))) := by
    apply disjoint_left.mpr
    rintro x hx ⟨q, rfl⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    apply disjoint_left.mp (havoid i (Finset.mem_Ioc.mpr hi)) hxi
    refine ⟨(C.neck a).coordinate_map_mem ⟨mem_univ _, hs⟩, ?_⟩
    rw [(C.neck a).coordinate_inverse_coordinate_map ⟨mem_univ _, hs⟩]
    exact ⟨hslo, hsc⟩
  have havoidV : Disjoint (P.belowGraph f)
      (range (fun q : UnitTwoSphere => (C.neck a).coordinate_map (q, s))) := by
    rw [hrange]
    apply disjoint_left.mpr
    intro x hx hxgraph
    exact (ne_of_lt hx.2) ((P.mem_coordinate_graph_iff f hdom).mp hxgraph).2
  have hpos : (C.neck a).region ((C.neck a).epsilon⁻¹ / 2) (C.neck a).epsilon⁻¹ ⊆ T := by
    rw [heA]
    have hnext : a + 1 ∈ Ioc a j := ⟨by omega, by omega⟩
    intro x hx
    exact mem_iUnion₂.mpr ⟨a + 1, hnext,
      (C.overlap_contains_quarters a ha (hactive hnext)).1 hx⟩
  have hTV := (C.neck a).disjoint_of_opposite_ends_of_isSeparating hsep hT
    (P.isConnected_belowGraph f hf.continuous hdom).2
    (show s ∈ Ioo (-(C.neck a).epsilon⁻¹) 0 from ⟨hs.1, by rw [heA] at hsq; linarith⟩)
    havoidT havoidV hlower hpos
  have hquarter : P.region (-ε⁻¹) (-ε⁻¹ / 2) ⊆ P.belowGraph f := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hfgraph : P.coordinate_map ((P.coordinate_inverse x).1, f (P.coordinate_inverse x).1) ∈
        (C.neck a).carrier := by
      have hm : P.coordinate_map ((P.coordinate_inverse x).1, f (P.coordinate_inverse x).1) ∈
          range (fun q : UnitTwoSphere => (C.neck a).coordinate_map (q, s)) :=
        hrange.symm ▸ mem_range_self (P.coordinate_inverse x).1
      obtain ⟨q, hq⟩ := hm
      rw [← hq]
      exact (C.neck a).coordinate_map_mem ⟨mem_univ _, hs⟩
    have hz : ((P.coordinate_inverse x).1, f (P.coordinate_inverse x).1) ∈ P.cylinderDomain :=
      ⟨mem_univ _, hdom _⟩
    have hlow := (hwithin ⟨P.coordinate_map_mem hz, hfgraph⟩).1.2.1
    rw [P.coordinate_inverse_coordinate_map hz] at hlow
    exact hx.2.2.trans hlow
  exact hTV.mono (fun x hx => mem_iUnion₂.mpr ⟨j, ⟨haj, le_rfl⟩, hx⟩) hquarter




theorem uniform_negative_end_exclusion_of_epsilon_le :
    ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ (1 / 200) → (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
        ∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active, i < j →
          Disjoint (C.neck j).carrier ((C.neck i).region (-ε⁻¹) (-ε⁻¹ / 2)) := by
  intro M _ _ _ _ _ _ _ g ε C hε hsep i hi j hj hij
  have hnext : i + 1 ∈ C.shape.active :=
    C.shape.ordConnected_active.out hi hj ⟨by omega, by omega⟩
  exact prepend_no_return_of_epsilon_le C (C.neck i) hε (C.epsilon_eq i hi) (i + 1) hnext (hsep _ hnext)
    (C.overlap_contains_quarters i hi hnext).2
    (C.overlap_within_three_quarters i hi hnext) j hj (by omega)

end BalancedNeckChain

end PoincareConjecture
