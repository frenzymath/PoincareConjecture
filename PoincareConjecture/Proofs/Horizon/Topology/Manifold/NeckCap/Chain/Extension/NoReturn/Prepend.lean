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

namespace EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem disjoint_of_opposite_ends_of_isSeparating (N : EpsilonNeck g)
    (hN : N.IsSeparating) {T V : Set M} (hT : IsPreconnected T) (hV : IsPreconnected V)
    {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) 0)
    (havoidT : Disjoint T (range (fun q : UnitTwoSphere => N.coordinate_map (q, s))))
    (havoidV : Disjoint V (range (fun q : UnitTwoSphere => N.coordinate_map (q, s))))
    (hneg : N.region (-N.epsilon⁻¹) s ⊆ V)
    (hpos : N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ T) : Disjoint T V := by
  apply disjoint_left.mpr
  intro x hxT hxV
  have hi := inv_pos.mpr N.epsilon_pos
  have hsdom : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := ⟨hs.1, hs.2.trans hi⟩
  obtain ⟨r, hr, hrN, hbound⟩ := N.exists_graph_collar (fun _ => s)
    continuous_const (fun _ => hsdom)
  let e := N.graphTransport hr hrN (fun _ => s) continuous_const hbound
  let W := e.symm '' (T ∪ V)
  have hW : IsPreconnected W :=
    (hT.union x hxT hxV hV).image e.symm e.symm.continuous.continuousOn
  have hWavoid : Disjoint W N.central_sphere := by
    apply disjoint_left.mpr
    rintro y ⟨z, hz, heq⟩ hy
    have hzgraph : z ∈ range (fun q : UnitTwoSphere => N.coordinate_map (q, s)) := by
      rw [← N.graphTransport_image_central_sphere hr hrN (fun _ => s)
        continuous_const hbound]
      refine ⟨y, hy, ?_⟩
      rw [← heq, e.apply_symm_apply]
    exact disjoint_left.mp (disjoint_union_left.mpr ⟨havoidT, havoidV⟩) hz hzgraph
  have hfixed (t : ℝ) (ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
      (hout : t < -r ∨ r < t) (q : UnitTwoSphere) :
      e (N.coordinate_map (q, t)) = N.coordinate_map (q, t) := by
    apply N.graphTransport_fixed hr hrN (fun _ => s) continuous_const hbound
    intro hk
    have hcoord := ((N.mem_coordinate_slab_iff (neg_lt_neg hrN) hrN).mp hk).2
    rw [N.coordinate_inverse_coordinate_map ⟨mem_univ _, ht⟩] at hcoord
    exact hout.elim (fun h => (not_le_of_gt h) hcoord.1)
      (fun h => (not_le_of_gt h) hcoord.2)
  let q := (N.coordinate_inverse N.center).1
  let tpos := (max r (N.epsilon⁻¹ / 2) + N.epsilon⁻¹) / 2
  have hmaxpos : max r (N.epsilon⁻¹ / 2) < N.epsilon⁻¹ := max_lt hrN (by linarith)
  have htpos : tpos ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    dsimp [tpos]
    constructor <;> linarith [le_max_right r (N.epsilon⁻¹ / 2)]
  have htposr : r < tpos := by dsimp [tpos]; linarith [le_max_left r (N.epsilon⁻¹ / 2)]
  have htposq : N.epsilon⁻¹ / 2 < tpos := by
    dsimp [tpos]; linarith [le_max_right r (N.epsilon⁻¹ / 2)]
  let tneg := -(max r (-s) + N.epsilon⁻¹) / 2
  have hmaxneg : max r (-s) < N.epsilon⁻¹ := max_lt hrN (by linarith [hs.1])
  have htneg : tneg ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    dsimp [tneg]
    constructor <;> linarith [le_max_left r (-s)]
  have htnegr : tneg < -r := by dsimp [tneg]; linarith [le_max_left r (-s)]
  have htnegs : tneg < s := by dsimp [tneg]; linarith [le_max_right r (-s)]
  have hzpos : N.coordinate_map (q, tpos) ∈ N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
    refine ⟨N.coordinate_map_mem ⟨mem_univ _, htpos⟩, ?_⟩
    rw [N.coordinate_inverse_coordinate_map ⟨mem_univ _, htpos⟩]
    exact ⟨htposq, htpos.2⟩
  have hzneg : N.coordinate_map (q, tneg) ∈ N.region (-N.epsilon⁻¹) s := by
    refine ⟨N.coordinate_map_mem ⟨mem_univ _, htneg⟩, ?_⟩
    rw [N.coordinate_inverse_coordinate_map ⟨mem_univ _, htneg⟩]
    exact ⟨htneg.1, htnegs⟩
  have hposW : N.coordinate_map (q, tpos) ∈ W := by
    refine ⟨N.coordinate_map (q, tpos), Or.inl (hpos hzpos), ?_⟩
    apply e.injective
    rw [e.apply_symm_apply, hfixed tpos htpos (Or.inr htposr)]
  have hnegW : N.coordinate_map (q, tneg) ∈ W := by
    refine ⟨N.coordinate_map (q, tneg), Or.inr (hneg hzneg), ?_⟩
    apply e.injective
    rw [e.apply_symm_apply, hfixed tneg htneg (Or.inl htnegr)]
  have hcomponent : W ⊆ connectedComponent N.center := by
    rw [connectedComponent_eq (N.carrier_subset_connectedComponent hzpos.1)]
    exact hW.subset_connectedComponent hposW
  apply N.not_meets_both_halves_of_isSeparating hN hW hcomponent hWavoid
  exact ⟨⟨_, hnegW, hzneg.1, hzneg.2.1, hzneg.2.2.trans hs.2⟩,
    ⟨_, hposW, hzpos.1, by linarith [hzpos.2.1], hzpos.2.2⟩⟩

end EpsilonNeck

namespace BalancedNeckChain




theorem exists_prepend_no_return_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε)
        (P : EpsilonNeck g), ε ≤ ε₀ → P.epsilon = ε →
        ∀ a ∈ C.shape.active, (C.neck a).IsSeparating →
        (C.neck a).region (-ε⁻¹) (-ε⁻¹ / 2) ⊆ P.carrier →
        P.carrier ∩ (C.neck a).carrier ⊆
          P.region (-ε⁻¹ / 2) ε⁻¹ ∩ (C.neck a).region (-ε⁻¹) (ε⁻¹ / 2) →
        ∀ j ∈ C.shape.active, a ≤ j →
          Disjoint (C.neck j).carrier (P.region (-ε⁻¹) (-ε⁻¹ / 2)) := by
  obtain ⟨ε₀, hε₀, hsmall, hgraph⟩ := EpsilonNeck.exists_sphereSlice_graph_and_isotopy.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
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
  obtain ⟨f, hf, hdom, hrange, _⟩ := hgraph P (C.neck a)
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




theorem exists_uniform_negative_end_exclusion_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
        ∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active, i < j →
          Disjoint (C.neck j).carrier ((C.neck i).region (-ε⁻¹) (-ε⁻¹ / 2)) := by
  obtain ⟨ε₀, hε₀, hsmall, hprepend⟩ := exists_prepend_no_return_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε hsep i hi j hj hij
  have hnext : i + 1 ∈ C.shape.active :=
    C.shape.ordConnected_active.out hi hj ⟨by omega, by omega⟩
  exact hprepend C (C.neck i) hε (C.epsilon_eq i hi) (i + 1) hnext (hsep _ hnext)
    (C.overlap_contains_quarters i hi hnext).2
    (C.overlap_within_three_quarters i hi hnext) j hj (by omega)

end BalancedNeckChain

end PoincareConjecture
