import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.OuterFrontier
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Reversal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.BalancedDistance

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem EpsilonNeck.closure_negative_quarter_diff_carrier_subset (N N' : EpsilonNeck g)
    (hpos : N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ N'.carrier)
    (hneg : N'.region (-N'.epsilon⁻¹) (-N'.epsilon⁻¹ / 2) ⊆ N.carrier)
    (hwithin : N.carrier ∩ N'.carrier ⊆
      N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
        N'.region (-N'.epsilon⁻¹) (N'.epsilon⁻¹ / 2)) :
    closure (N'.region (-N'.epsilon⁻¹) (-N'.epsilon⁻¹ / 2)) \ N'.carrier ⊆
      N.carrier := by
  have h := N'.reversed.closure_positive_quarter_diff_carrier_subset N.reversed
    (by simpa only [EpsilonNeck.reversed_region, EpsilonNeck.reversed_epsilon,
      EpsilonNeck.reversed_carrier, neg_div] using hneg)
    (by simpa only [EpsilonNeck.reversed_region, EpsilonNeck.reversed_epsilon,
      EpsilonNeck.reversed_carrier, neg_div, neg_neg] using hpos)
    (by simpa only [EpsilonNeck.reversed_region, EpsilonNeck.reversed_epsilon,
      EpsilonNeck.reversed_carrier, neg_div, neg_neg, inter_comm] using hwithin)
  simpa only [EpsilonNeck.reversed_region, EpsilonNeck.reversed_epsilon,
    EpsilonNeck.reversed_carrier, neg_div] using h

namespace BalancedNeckChain

variable {ε : ℝ} (C : BalancedNeckChain g ε)

theorem frontier_subset_outer_ends {a b : ℤ} (hshape : C.shape = .finite a b) :
    frontier (⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier) ⊆
      closure ((C.neck a).region (-ε⁻¹) (-ε⁻¹ / 2)) ∪
        closure ((C.neck b).region (ε⁻¹ / 2) ε⁻¹) := by
  have hactive : C.shape.active = Icc a b := by rw [hshape]; rfl
  have hfinite : C.shape.active.Finite := hactive.symm ▸ finite_Icc a b
  intro x hx
  have hout : ∀ i ∈ C.shape.active, x ∉ (C.neck i).carrier := by
    intro i hi hxi
    have hU := isOpen_iUnion fun j : {j // j ∈ C.shape.active} =>
      (C.neck j.1).carrier_open
    exact (hU.frontier_eq ▸ hx).2 (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
  obtain ⟨i, hi, hxi⟩ := C.exists_mem_frontier_of_finite hfinite hx
  have hie : (C.neck i).epsilon = ε := C.epsilon_eq i hi
  have he : 0 < ε⁻¹ := by rw [← hie]; exact inv_pos.mpr (C.neck i).epsilon_pos
  have hiab : a ≤ i ∧ i ≤ b := by simpa only [hactive, mem_Icc] using hi
  have hend := (C.neck i).frontier_subset_closure_ends
    (a := -ε⁻¹ / 2) (b := ε⁻¹ / 2)
    (by rw [hie]; linarith) (by rw [hie]; linarith) hxi
  simp only [hie, mem_union] at hend
  rcases hend with hneg | hpos
  · by_cases hia : i = a
    · exact Or.inl (hia ▸ hneg)
    have hp : i - 1 ∈ C.shape.active := by rw [hactive]; constructor <;> omega
    have hn : i - 1 + 1 ∈ C.shape.active := by simpa using hi
    have hquarters := C.overlap_contains_quarters (i - 1) hp hn
    have hwithin := C.overlap_within_three_quarters (i - 1) hp hn
    simp only [sub_add_cancel] at hquarters hwithin
    have hcapture := (C.neck (i - 1)).closure_negative_quarter_diff_carrier_subset
      (C.neck i)
      (by simpa only [C.epsilon_eq (i - 1) hp] using hquarters.1)
      (by simpa only [hie] using hquarters.2)
      (by simpa only [C.epsilon_eq (i - 1) hp, hie] using hwithin)
    exact False.elim (hout (i - 1) hp
      (hcapture ⟨by simpa only [hie] using hneg, hout i hi⟩))
  · by_cases hib : i = b
    · exact Or.inr (hib ▸ hpos)
    have hn : i + 1 ∈ C.shape.active := by rw [hactive]; constructor <;> omega
    have hquarters := C.overlap_contains_quarters i hi hn
    have hwithin := C.overlap_within_three_quarters i hi hn
    have hcapture := (C.neck i).closure_positive_quarter_diff_carrier_subset
      (C.neck (i + 1))
      (by simpa only [hie] using hquarters.1)
      (by simpa only [C.epsilon_eq (i + 1) hn] using hquarters.2)
      (by simpa only [hie, C.epsilon_eq (i + 1) hn] using hwithin)
    exact False.elim (hout (i + 1) hn
      (hcapture ⟨by simpa only [hie] using hpos, hout i hi⟩))

end BalancedNeckChain

theorem NeckOnlyCover.exists_neck_at_balanced_outer_end (H : NeckOnlyCover g)
    (hε : H.epsilon ≤ 1 / 1000) (C : BalancedNeckChain g H.epsilon)
    {a b : ℤ} (hshape : C.shape = .finite a b)
    (hcenters : ∀ i ∈ C.shape.active, (C.neck i).center ∈ H.X)
    (hmiss : ¬ H.X ⊆ ⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier) :
    ∃ N ∈ H.necks, N.center ∈ H.X ∧
      N.center ∈ frontier (⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier) ∧
      (∀ i ∈ C.shape.active, N.center ≠ (C.neck i).center) ∧
      ∃ i ∈ C.shape.active,
        ((i = a ∧ N.center ∈ closure ((C.neck a).region
          (-H.epsilon⁻¹) (-H.epsilon⁻¹ / 2))) ∨
          (i = b ∧ N.center ∈ closure ((C.neck b).region
            (H.epsilon⁻¹ / 2) H.epsilon⁻¹))) ∧
        ENNReal.ofReal ((0.99 : ℝ) * (C.neck i).scale * H.epsilon⁻¹) ≤
          g.edist (C.neck i).center N.center ∧
        g.edist (C.neck i).center N.center ≤
          ENNReal.ofReal ((1.01 : ℝ) * (C.neck i).scale * H.epsilon⁻¹) := by
  obtain ⟨N, hN, hx, hxf, hdistinct, -⟩ :=
    H.exists_neck_at_chain_frontier C hcenters hmiss
  have hactive : C.shape.active = Icc a b := by rw [hshape]; rfl
  obtain ⟨j, hj⟩ := C.active_nonempty
  have hjab : a ≤ j ∧ j ≤ b := by simpa only [hactive, mem_Icc] using hj
  have hab : a ≤ b := hjab.1.trans hjab.2
  have ha : a ∈ C.shape.active := hactive.symm ▸ ⟨le_rfl, hab⟩
  have hb : b ∈ C.shape.active := hactive.symm ▸ ⟨hab, le_rfl⟩
  have hout (i : ℤ) (hi : i ∈ C.shape.active) : N.center ∉ (C.neck i).carrier := by
    intro hxi
    have hU := isOpen_iUnion fun k : {k // k ∈ C.shape.active} =>
      (C.neck k.1).carrier_open
    exact (hU.frontier_eq ▸ hxf).2 (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
  have hdist (i : ℤ) (hi : i ∈ C.shape.active)
      (hcl : N.center ∈ closure (C.neck i).carrier) :
      ENNReal.ofReal ((0.99 : ℝ) * (C.neck i).scale * H.epsilon⁻¹) ≤
        g.edist (C.neck i).center N.center ∧
      g.edist (C.neck i).center N.center ≤
        ENNReal.ofReal ((1.01 : ℝ) * (C.neck i).scale * H.epsilon⁻¹) := by
    have hfront : N.center ∈ frontier (C.neck i).carrier := by
      rw [(C.neck i).carrier_open.frontier_eq]
      exact ⟨hcl, hout i hi⟩
    simpa only [C.epsilon_eq i hi] using (C.neck i).balanced_edist_of_mem_frontier
      (by simpa only [C.epsilon_eq i hi] using hε) hfront
  refine ⟨N, hN, hx, hxf, hdistinct, ?_⟩
  rcases C.frontier_subset_outer_ends hshape hxf with hleft | hright
  · exact ⟨a, ha, Or.inl ⟨rfl, hleft⟩,
      hdist a ha (closure_mono ((C.neck a).region_subset_carrier _ _) hleft)⟩
  · exact ⟨b, hb, Or.inr ⟨rfl, hright⟩,
      hdist b hb (closure_mono ((C.neck b).region_subset_carrier _ _) hright)⟩

end PoincareConjecture
