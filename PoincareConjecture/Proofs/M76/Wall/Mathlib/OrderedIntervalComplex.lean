import PoincareConjecture.Proofs.M76.Wall.Mathlib.IntervalCarrierCoverage
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLinearChain
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem exists_ordered_edge_chain_of_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (b : Icc (0 : ℝ) 1 ≃ₜ K.space)
    (hzero : (b ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : E) ∈ K.vertices)
    (hone : (b ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : E) ∈ K.vertices) :
    ∃ (n : ℕ) (p : Fin (n + 2) → E),
      Function.Injective p ∧
      p 0 = b ⟨0, ⟨le_rfl, zero_le_one⟩⟩ ∧
      p (Fin.last (n + 1)) = b ⟨1, ⟨zero_le_one, le_rfl⟩⟩ ∧
      (∀ i : Fin (n + 1), {p i.castSucc, p i.succ} ∈ K.faces) ∧
      K.space = ⋃ i : Fin (n + 1), segment ℝ (p i.castSucc) (p i.succ) ∧
      K.vertices = range p := by
  classical
  let a : E := b ⟨0, ⟨le_rfl, zero_le_one⟩⟩
  let c : E := b ⟨1, ⟨zero_le_one, le_rfl⟩⟩
  have hac : a ≠ c := by
    intro h
    exact zero_ne_one (congrArg Subtype.val (b.injective (Subtype.ext h)))
  have hrange : range (fun t : Icc (0 : ℝ) 1 => (b t : E)) = K.space := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (b t).property
    · intro hx
      obtain ⟨t, ht⟩ := b.surjective ⟨x, hx⟩
      exact ⟨t, congrArg Subtype.val ht⟩
  have hconn : IsConnected K.space := by
    rw [← hrange]
    exact isConnected_range (continuous_subtype_val.comp b.continuous)
  obtain ⟨w, hw⟩ := (K.connected_edgeGraph_of_isConnected hK hconn).exists_isPath
    ⟨a, hzero⟩ ⟨c, hone⟩
  have hlen : 0 < w.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp
    (SimpleGraph.Walk.not_nil_of_ne
      (fun h => hac (congrArg (fun z : K.vertices => (z : E)) h)))
  obtain ⟨n, hn⟩ : ∃ n : ℕ, w.length = n + 1 := ⟨w.length - 1, by omega⟩
  let p : Fin (n + 2) → E := fun i => (w.getVert i.val : E)
  have hpinj : Function.Injective p := by
    intro i j hij
    apply Fin.ext
    apply hw.getVert_injOn (by change i.val ≤ w.length; omega)
      (by change j.val ≤ w.length; omega)
    exact Subtype.ext hij
  have hedge (i : Fin (n + 1)) : {p i.castSucc, p i.succ} ∈ K.faces := by
    have h := (w.adj_getVert_succ (i := i.val) (by omega)).2
    change ({w.getVert i.val, w.getVert (i.val + 1)} : Finset K.vertices).map
      (Function.Embedding.subtype _) ∈ K.faces at h
    simpa only [p, Fin.val_castSucc, Fin.val_succ, Finset.map_insert,
      Finset.map_singleton, Function.Embedding.coe_subtype] using h
  have hinter (i j : Fin (n + 1)) :
      segment ℝ (p i.castSucc) (p i.succ) ∩ segment ℝ (p j.castSucc) (p j.succ) ⊆
        convexHull ℝ (({p i.castSucc, p i.succ} : Set E) ∩ {p j.castSucc, p j.succ}) := by
    simpa only [Finset.coe_pair, convexHull_pair] using
      K.inter_subset_convexHull (hedge i) (hedge j)
  have hp0 : p 0 = a := by
    change (w.getVert 0 : E) = a
    rw [w.getVert_zero]
  have hp1 : p (Fin.last (n + 1)) = c := by
    change (w.getVert (n + 1) : E) = c
    rw [← hn, w.getVert_length]
  let T : Set E := ⋃ i : Fin (n + 1), segment ℝ (p i.castSucc) (p i.succ)
  have hpair : IsFinitePLBallPair ℝ T {a, c} := by
    simpa only [hp0, hp1] using isFinitePLBallPair_linear_chain p hpinj hinter
  have hTK : T ⊆ K.space := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact K.convexHull_subset_space (hedge i)
      (by simpa only [Finset.coe_pair, convexHull_pair] using hi)
  obtain ⟨H, _, hH0, hH1⟩ := hpair.exists_unitInterval_chart_with_endpoints hac
  let f : Icc (0 : ℝ) 1 → K.space := fun t => ⟨H t, hTK (H t).property⟩
  have hf : Continuous f :=
    (continuous_subtype_val.comp H.continuous).subtype_mk _
  have hfsurj : Function.Surjective f := b.surjective_of_interval_endpoints hf
    (Subtype.ext hH0) (Subtype.ext hH1)
  have hcover : K.space = T := by
    apply Subset.antisymm _ hTK
    intro x hx
    obtain ⟨t, ht⟩ := hfsurj ⟨x, hx⟩
    have htx : (H t : E) = x := congrArg Subtype.val ht
    exact htx ▸ (H t).property
  refine ⟨n, p, hpinj, hp0, hp1, hedge, hcover, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.subset (K.vertices_subset_space hx))
    have hxi : x ∈ ({p i.castSucc, p i.succ} : Finset E) :=
      (K.vertex_mem_convexHull_iff hx (hedge i)).mp
        (by simpa only [Finset.coe_pair, convexHull_pair] using hi)
    rcases Finset.mem_insert.mp hxi with h | h
    · exact ⟨i.castSucc, h.symm⟩
    · exact ⟨i.succ, (Finset.mem_singleton.mp h).symm⟩
  · rintro ⟨i, rfl⟩
    exact (w.getVert i.val).property

end Geometry.SimplicialComplex
