import PoincareConjecture.Proofs.M76.Wall.Mathlib.MarkedVertexSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLinearChain
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex






theorem exists_finitePL_arc_in_carrier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hconn : IsConnected K.space)
    {a b : E} (ha : a ∈ K.space) (hb : b ∈ K.space) (hab : a ≠ b) :
    ∃ (T : Set E) (H : Icc (0 : ℝ) 1 ≃ₜ T),
      IsFinitePLBallPair ℝ T {a, b} ∧ T ⊆ K.space ∧ H.IsFinitePL ∧
      (H ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : E) = a ∧
      (H ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : E) = b := by
  classical
  obtain ⟨L, hL, hLK, hmarks⟩ := K.exists_subdivision_with_marked_vertices hK {a, b}
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · rcases Finset.mem_singleton.mp hx with rfl
        exact hb)
  have haL : a ∈ L.vertices := hmarks a (Finset.mem_insert_self a {b})
  have hbL : b ∈ L.vertices := hmarks b
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  have hconnL : IsConnected L.space := by rwa [hLK.space_eq]
  obtain ⟨w, hw⟩ := (L.connected_edgeGraph_of_isConnected hL hconnL).exists_isPath
    ⟨a, haL⟩ ⟨b, hbL⟩
  have hlen : 0 < w.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp
    (SimpleGraph.Walk.not_nil_of_ne (fun h => hab (congrArg Subtype.val h)))
  obtain ⟨n, hn⟩ : ∃ n : ℕ, w.length = n + 1 := ⟨w.length - 1, by omega⟩
  let p : Fin (n + 2) → E := fun i => (w.getVert i.val : E)
  have hpinj : Function.Injective p := by
    intro i j hij
    apply Fin.ext
    apply hw.getVert_injOn (by change i.val ≤ w.length; omega)
      (by change j.val ≤ w.length; omega)
    exact Subtype.ext hij
  have hedge (i : Fin (n + 1)) : {p i.castSucc, p i.succ} ∈ L.faces := by
    have h := (w.adj_getVert_succ (i := i.val) (by omega)).2
    change ({w.getVert i.val, w.getVert (i.val + 1)} : Finset L.vertices).map
      (Function.Embedding.subtype _) ∈ L.faces at h
    simpa only [p, Fin.val_castSucc, Fin.val_succ, Finset.map_insert,
      Finset.map_singleton, Function.Embedding.coe_subtype] using h
  have hinter (i j : Fin (n + 1)) :
      segment ℝ (p i.castSucc) (p i.succ) ∩ segment ℝ (p j.castSucc) (p j.succ) ⊆
        convexHull ℝ (({p i.castSucc, p i.succ} : Set E) ∩ {p j.castSucc, p j.succ}) := by
    simpa only [Finset.coe_pair, convexHull_pair] using
      L.inter_subset_convexHull (hedge i) (hedge j)
  have hp0 : p 0 = a := by
    change (w.getVert 0 : E) = a
    rw [w.getVert_zero]
  have hp1 : p (Fin.last (n + 1)) = b := by
    change (w.getVert (n + 1) : E) = b
    rw [← hn, w.getVert_length]
  let T : Set E := ⋃ i : Fin (n + 1), segment ℝ (p i.castSucc) (p i.succ)
  have hpair : IsFinitePLBallPair ℝ T {a, b} := by
    simpa only [hp0, hp1] using isFinitePLBallPair_linear_chain p hpinj hinter
  have hTK : T ⊆ K.space := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    apply hLK.space_eq.subset
    apply L.convexHull_subset_space (hedge i)
    simpa only [Finset.coe_pair, convexHull_pair] using hi
  obtain ⟨H, hH, hH0, hH1⟩ := hpair.exists_unitInterval_chart_with_endpoints hab
  exact ⟨T, H, hpair, hTK, hH, hH0, hH1⟩

end Geometry.SimplicialComplex
