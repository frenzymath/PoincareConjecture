import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Partition.GraphRegions
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Ends

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem disjoint_belowGraph_successor_upper (A B : EpsilonNeck g)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hdom : ∀ q, f q ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹)
    {s : ℝ} (hs : s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹)
    (hgraph : range (fun q : UnitTwoSphere => B.coordinate_map (q, s)) =
      range (fun q : UnitTwoSphere => A.coordinate_map (q, f q)))
    (hwithin : A.carrier ∩ B.carrier ⊆
      A.region (-A.epsilon⁻¹ / 2) A.epsilon⁻¹ ∩
        B.region (-B.epsilon⁻¹) (B.epsilon⁻¹ / 2)) :
    Disjoint (A.belowGraph f) (B.region s B.epsilon⁻¹) := by
  obtain ⟨c, hc, hcA, hbound⟩ := A.exists_graph_collar f hf hdom
  have hA : 0 < A.epsilon⁻¹ := inv_pos.mpr A.epsilon_pos
  have hB : 0 < B.epsilon⁻¹ := inv_pos.mpr B.epsilon_pos
  let S := B.region s B.epsilon⁻¹
  let P := A.belowGraph f ∩ S
  let K := A.coordinate_map '' (univ ×ˢ Icc (-A.epsilon⁻¹ / 2) c)
  have hKcompact : IsCompact K := A.isCompact_coordinate_slab (by linarith) hcA
  have hKsub : K ⊆ A.carrier := A.coordinate_slab_subset_carrier (by linarith) hcA
  have hPK : P ⊆ K := by
    intro x hx
    have hover := hwithin ⟨hx.1.1, hx.2.1⟩
    refine ⟨A.coordinate_inverse x, ⟨mem_univ _, hover.1.2.1.le, ?_⟩,
      A.coordinate_map_coordinate_inverse hx.1.1⟩
    exact hx.1.2.le.trans ((le_abs_self _).trans (hbound _).le)
  have hSconnected : IsConnected S := B.isConnected_region hs.1.le le_rfl hs.2
  have hPopen : IsOpen P := (A.isOpen_belowGraph f hf).inter (B.isOpen_region _ _)
  have hclosed : closure P ∩ S ⊆ P := by
    intro x hx
    have hxA : x ∈ A.carrier := hKsub ((closure_minimal hPK hKcompact.isClosed) hx.1)
    have hcoord : ContinuousAt A.coordinate_inverse x :=
      A.coordinate_inverse_smooth.continuousOn.continuousAt (A.carrier_open.mem_nhds hxA)
    have hle : (A.coordinate_inverse x).2 ≤ f (A.coordinate_inverse x).1 :=
      ContinuousWithinAt.closure_le hx.1 hcoord.snd.continuousWithinAt
        (hf.continuousAt.comp hcoord.fst).continuousWithinAt
        (fun y hy => hy.1.2.le)
    have hne : (A.coordinate_inverse x).2 ≠ f (A.coordinate_inverse x).1 := by
      intro heq
      have hxgraph := (A.mem_coordinate_graph_iff f hdom).mpr ⟨hxA, heq⟩
      rw [← hgraph] at hxgraph
      obtain ⟨q, hq⟩ := hxgraph
      have hxs : (B.coordinate_inverse x).2 = s := by
        rw [← hq, B.coordinate_inverse_coordinate_map ⟨mem_univ _, hs⟩]
      exact (ne_of_gt hx.2.2.1) hxs
    exact ⟨⟨hxA, lt_of_le_of_ne hle hne⟩, hx.2⟩
  apply disjoint_left.mpr
  intro x hxA hxS
  have hmeet : (S ∩ P).Nonempty := ⟨x, hxS, hxA, hxS⟩
  have hSsub : S ⊆ P := hSconnected.2.subset_of_closure_inter_subset hPopen hmeet hclosed
  obtain ⟨y, hy⟩ := (B.isConnected_region
    (a := max s (B.epsilon⁻¹ / 2)) (b := B.epsilon⁻¹)
    (hs.1.le.trans (le_max_left _ _)) le_rfl (max_lt hs.2 (by linarith))).1
  have hyS : y ∈ S := ⟨hy.1, (le_max_left _ _).trans_lt hy.2.1, hy.2.2⟩
  have hover := hwithin ⟨(hSsub hyS).1.1, hy.1⟩
  exact hover.2.2.2.not_gt ((le_max_right _ _).trans_lt hy.2.1)

end PoincareConjecture.EpsilonNeck
