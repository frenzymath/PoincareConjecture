import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalGraphRegions
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalUpperSide










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem subset_graph_side_of_isPreconnected_m28 (A : EpsilonNeck g)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hdom : ∀ q, f q ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹)
    {S : Set M} (hS : IsPreconnected S) (hsub : S ⊆ A.carrier)
    (havoid : Disjoint S (range (fun q => A.coordinate_map (q, f q)))) :
    S ⊆ A.belowGraph_m28 f ∨ S ⊆ A.aboveGraph_m28 f := by
  have hc := (A.coordinate_inverse_smooth.continuousOn.snd.sub
    (hf.comp_continuousOn A.coordinate_inverse_smooth.continuousOn.fst)).mono hsub
  have hne (x : M) (hx : x ∈ S) :
      (A.coordinate_inverse x).2 - f (A.coordinate_inverse x).1 ≠ 0 := by
    intro heq
    exact disjoint_left.mp havoid hx
      ((A.mem_coordinate_graph_iff_m28 f hdom).mpr ⟨hsub hx, sub_eq_zero.mp heq⟩)
  rcases hS.mapsTo_Ioi_or_Iio hc hne with h | h
  · exact Or.inr (fun x hx => ⟨hsub hx, sub_pos.mp (h hx)⟩)
  · exact Or.inl (fun x hx => ⟨hsub hx, sub_neg.mp (h hx)⟩)

theorem successor_lower_subset_belowGraph_m28 (A B : EpsilonNeck g)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hdom : ∀ q, f q ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹)
    (s : ℝ) (hs : s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹)
    (hsq : s < -B.epsilon⁻¹ / 2)
    (hgraph : range (fun q => A.coordinate_map (q, f q)) =
      range (fun q : UnitTwoSphere => B.coordinate_map (q, s)))
    (hneg : B.region (-B.epsilon⁻¹) (-B.epsilon⁻¹ / 2) ⊆ A.carrier)
    (hdisj : Disjoint (A.belowGraph_m28 f) (B.region s B.epsilon⁻¹)) :
    B.region (-B.epsilon⁻¹) s ⊆ A.belowGraph_m28 f := by
  have hsub : B.region (-B.epsilon⁻¹) s ⊆ A.carrier :=
    fun x hx => hneg ⟨hx.1, hx.2.1, hx.2.2.trans hsq⟩
  have havoid : Disjoint (B.region (-B.epsilon⁻¹) s)
      (range (fun q => A.coordinate_map (q, f q))) := by
    rw [hgraph]
    apply disjoint_left.mpr
    rintro x hx ⟨q, rfl⟩
    have hz : (q, s) ∈ B.cylinderDomain := ⟨mem_univ _, hs⟩
    have heq := congrArg Prod.snd (B.coordinate_inverse_coordinate_map hz)
    exact (ne_of_lt hx.2.2) heq
  rcases A.subset_graph_side_of_isPreconnected_m28 f hf hdom
    (B.isConnected_region le_rfl hs.2.le hs.1).2 hsub havoid with h | h
  · exact h
  exfalso
  let q := (A.coordinate_inverse A.center).1
  have hxB : A.coordinate_map (q, f q) ∈ B.carrier := by
    have hx : A.coordinate_map (q, f q) ∈ range
        (fun q : UnitTwoSphere => B.coordinate_map (q, s)) := hgraph ▸ ⟨q, rfl⟩
    obtain ⟨p, hp⟩ := hx
    rw [← hp]
    exact B.coordinate_map_mem ⟨mem_univ _, hs⟩
  obtain ⟨x, hxB, hxbelow⟩ := mem_closure_iff_nhds.mp
    (A.coordinate_graph_mem_closure_belowGraph_m28 f hdom q)
    B.carrier (B.carrier_open.mem_nhds hxB)
  have hxlt : (B.coordinate_inverse x).2 < s := by
    rcases lt_trichotomy (B.coordinate_inverse x).2 s with hlt | heq | hgt
    · exact hlt
    · exfalso
      have hxgraph : x ∈ range (fun q => A.coordinate_map (q, f q)) := by
        rw [hgraph]
        refine ⟨(B.coordinate_inverse x).1, ?_⟩
        change B.coordinate_map ((B.coordinate_inverse x).1, s) = x
        rw [← heq, Prod.mk.eta, B.coordinate_map_coordinate_inverse hxB]
      exact (ne_of_lt hxbelow.2) ((A.mem_coordinate_graph_iff_m28 f hdom).mp hxgraph).2
    · exact False.elim (disjoint_left.mp hdisj hxbelow
        ⟨hxB, hgt, (B.coordinate_inverse_mem x hxB).2.2⟩)
  exact disjoint_left.mp (A.disjoint_belowGraph_aboveGraph_m28 f) hxbelow
    (h ⟨hxB, (B.coordinate_inverse_mem x hxB).2.1, hxlt⟩)

theorem graph_positive_side_iff_m28 (A B : EpsilonNeck g)
    (f : UnitTwoSphere → ℝ)
    (hdom : ∀ q, f q ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹)
    (s : ℝ) (hs : s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹)
    (hgraph : range (fun q => A.coordinate_map (q, f q)) =
      range (fun q : UnitTwoSphere => B.coordinate_map (q, s)))
    (hdisj : Disjoint (A.belowGraph_m28 f) (B.region s B.epsilon⁻¹))
    (hlower : B.region (-B.epsilon⁻¹) s ⊆ A.belowGraph_m28 f)
    {x : M} (hxA : x ∈ A.carrier) (hxB : x ∈ B.carrier) :
    s < (B.coordinate_inverse x).2 ↔ f (A.coordinate_inverse x).1 <
      (A.coordinate_inverse x).2 := by
  have heq : (B.coordinate_inverse x).2 = s ↔
      (A.coordinate_inverse x).2 = f (A.coordinate_inverse x).1 := by
    constructor
    · intro hx
      apply ((A.mem_coordinate_graph_iff_m28 f hdom).mp ?_).2
      rw [hgraph]
      refine ⟨(B.coordinate_inverse x).1, ?_⟩
      change B.coordinate_map ((B.coordinate_inverse x).1, s) = x
      rw [← hx, Prod.mk.eta, B.coordinate_map_coordinate_inverse hxB]
    · intro hx
      have hxgraph := (A.mem_coordinate_graph_iff_m28 f hdom).mpr ⟨hxA, hx⟩
      rw [hgraph] at hxgraph
      obtain ⟨q, hq⟩ := hxgraph
      rw [← hq, B.coordinate_inverse_coordinate_map ⟨mem_univ _, hs⟩]
  constructor
  · intro hpos
    rcases lt_trichotomy (A.coordinate_inverse x).2
        (f (A.coordinate_inverse x).1) with hlt | he | hgt
    · exact False.elim (disjoint_left.mp hdisj ⟨hxA, hlt⟩
        ⟨hxB, hpos, (B.coordinate_inverse_mem x hxB).2.2⟩)
    · exact False.elim ((ne_of_gt hpos) (heq.mpr he))
    · exact hgt
  · intro hpos
    rcases lt_trichotomy (B.coordinate_inverse x).2 s with hlt | he | hgt
    · exact False.elim ((hlower ⟨hxB, (B.coordinate_inverse_mem x hxB).2.1, hlt⟩).2.not_gt hpos)
    · exact False.elim ((ne_of_gt hpos) (heq.mp he))
    · exact hgt

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]

theorem aboveGraph_subset_successor_m28 (A B : EpsilonNeck g)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hdom : ∀ q, f q ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹)
    (s : ℝ) (hs : s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹)
    (hgraph : range (fun q => A.coordinate_map (q, f q)) =
      range (fun q : UnitTwoSphere => B.coordinate_map (q, s)))
    (hside : ∀ x ∈ A.carrier ∩ B.carrier,
      s < (B.coordinate_inverse x).2 ↔
        f (A.coordinate_inverse x).1 < (A.coordinate_inverse x).2)
    (hwithin : ∀ x ∈ A.carrier ∩ B.carrier,
      (B.coordinate_inverse x).2 < B.epsilon⁻¹ / 2) :
    A.aboveGraph_m28 f ⊆ B.carrier := by
  let P := A.aboveGraph_m28 f ∩ B.carrier
  let K := B.coordinate_map '' (univ ×ˢ Icc s (B.epsilon⁻¹ / 2))
  have hhalf : B.epsilon⁻¹ / 2 < B.epsilon⁻¹ := by
    linarith [inv_pos.mpr B.epsilon_pos]
  have hK : IsCompact K := B.isCompact_coordinate_slab hs.1 hhalf
  have hKsub : K ⊆ B.carrier := B.coordinate_slab_subset_carrier_m28 hs.1 hhalf
  have hPK : P ⊆ K := by
    intro x hx
    exact ⟨B.coordinate_inverse x, ⟨mem_univ _,
      ((hside x ⟨hx.1.1, hx.2⟩).mpr hx.1.2).le,
      (hwithin x ⟨hx.1.1, hx.2⟩).le⟩,
      B.coordinate_map_coordinate_inverse hx.2⟩
  let q := (A.coordinate_inverse A.center).1
  have hxB : A.coordinate_map (q, f q) ∈ B.carrier := by
    have hx : A.coordinate_map (q, f q) ∈ range
        (fun q : UnitTwoSphere => B.coordinate_map (q, s)) := hgraph ▸ ⟨q, rfl⟩
    obtain ⟨p, hp⟩ := hx
    rw [← hp]
    exact B.coordinate_map_mem ⟨mem_univ _, hs⟩
  obtain ⟨x, hxB, hxabove⟩ := mem_closure_iff_nhds.mp
    (A.coordinate_graph_mem_closure_aboveGraph_m28 f hdom q)
    B.carrier (B.carrier_open.mem_nhds hxB)
  have hsub : A.aboveGraph_m28 f ⊆ P :=
    (A.isConnected_aboveGraph_m28 f hf hdom).2.subset_of_closure_inter_subset
      ((A.isOpen_aboveGraph_m28 f hf).inter B.carrier_open)
      ⟨x, hxabove, hxabove, hxB⟩ (by
        intro x hx
        exact ⟨hx.2, hKsub ((closure_minimal hPK hK.isClosed) hx.1)⟩)
  exact fun x hx => (hsub hx).2

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem union_eq_graph_half_union_successor_upper_m28 (A B : EpsilonNeck g)
    (f : UnitTwoSphere → ℝ)
    (s : ℝ) (hsq : s < -B.epsilon⁻¹ / 2)
    (hneg : B.region (-B.epsilon⁻¹) (-B.epsilon⁻¹ / 2) ⊆ A.carrier)
    (hside : ∀ x ∈ A.carrier ∩ B.carrier,
      s < (B.coordinate_inverse x).2 ↔
        f (A.coordinate_inverse x).1 < (A.coordinate_inverse x).2)
    (hupper : A.aboveGraph_m28 f ⊆ B.carrier) :
    A.carrier ∪ B.carrier =
      (A.carrier \ A.aboveGraph_m28 f) ∪ B.region s B.epsilon⁻¹ ∧
    Disjoint (A.carrier \ A.aboveGraph_m28 f) (B.region s B.epsilon⁻¹) := by
  constructor
  · ext x
    constructor
    · rintro (hxA | hxB)
      · by_cases hx : x ∈ A.aboveGraph_m28 f
        · exact Or.inr ⟨hupper hx,
            (hside x ⟨hxA, hupper hx⟩).mpr hx.2,
            (B.coordinate_inverse_mem x (hupper hx)).2.2⟩
        · exact Or.inl ⟨hxA, hx⟩
      · by_cases hx : s < (B.coordinate_inverse x).2
        · exact Or.inr ⟨hxB, hx, (B.coordinate_inverse_mem x hxB).2.2⟩
        · have hxA : x ∈ A.carrier := hneg ⟨hxB,
            (B.coordinate_inverse_mem x hxB).2.1, (le_of_not_gt hx).trans_lt hsq⟩
          exact Or.inl ⟨hxA, fun ha => hx ((hside x ⟨hxA, hxB⟩).mpr ha.2)⟩
    · rintro (hx | hx)
      · exact Or.inl hx.1
      · exact Or.inr hx.1
  · apply disjoint_left.mpr
    intro x hxA hxB
    exact hxA.2 ⟨hxA.1, (hside x ⟨hxA.1, hxB.1⟩).mp hxB.2.1⟩



theorem graph_half_partition_m28 (A B : EpsilonNeck g)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hdom : ∀ q, f q ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹)
    {s : ℝ} (hs : s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹)
    (hsq : s < -B.epsilon⁻¹ / 2)
    (hgraph : range (fun q : UnitTwoSphere => B.coordinate_map (q, s)) =
      range (fun q => A.coordinate_map (q, f q)))
    (hneg : B.region (-B.epsilon⁻¹) (-B.epsilon⁻¹ / 2) ⊆ A.carrier)
    (hwithin : A.carrier ∩ B.carrier ⊆
      A.region (-A.epsilon⁻¹ / 2) A.epsilon⁻¹ ∩
        B.region (-B.epsilon⁻¹) (B.epsilon⁻¹ / 2)) :
    (∀ x ∈ A.carrier ∩ B.carrier,
      s < (B.coordinate_inverse x).2 ↔
        f (A.coordinate_inverse x).1 < (A.coordinate_inverse x).2) ∧
    A.carrier ∪ B.carrier =
      (A.carrier \ A.aboveGraph_m28 f) ∪ B.region s B.epsilon⁻¹ ∧
    Disjoint (A.carrier \ A.aboveGraph_m28 f) (B.region s B.epsilon⁻¹) := by
  have hd := A.disjoint_belowGraph_successor_upper_m28 B f hf hdom hs hgraph hwithin
  have hl := A.successor_lower_subset_belowGraph_m28 B f hf hdom s hs hsq hgraph.symm hneg hd
  have hside : ∀ x ∈ A.carrier ∩ B.carrier,
      s < (B.coordinate_inverse x).2 ↔
        f (A.coordinate_inverse x).1 < (A.coordinate_inverse x).2 := by
    intro x hx
    exact A.graph_positive_side_iff_m28 B f hdom s hs hgraph.symm hd hl hx.1 hx.2
  have hu := A.aboveGraph_subset_successor_m28 B f hf hdom s hs hgraph.symm hside
    (fun x hx => (hwithin hx).2.2.2)
  exact ⟨hside, A.union_eq_graph_half_union_successor_upper_m28 B f s hsq hneg hside hu⟩

end PoincareConjecture.EpsilonNeck
