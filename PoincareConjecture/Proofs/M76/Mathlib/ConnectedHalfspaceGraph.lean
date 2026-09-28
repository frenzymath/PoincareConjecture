import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem preconnected_positive_vertex_graph_of_isPreconnected
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (A : E →ᵃ[ℝ] ℝ) (hconn : IsPreconnected (K.space ∩ {x | 0 < A x})) :
    (K.vertexAbstractComplex.edgeGraph.induce
      {v : K.vertices | 0 < A (v : E)}).Preconnected := by
  classical
  let G := K.vertexAbstractComplex.edgeGraph.induce {v : K.vertices | 0 < A (v : E)}
  have hvertex (t : Finset E) (ht : t ∈ K.faces) (v : E) (hv : v ∈ t) :
      v ∈ K.vertices :=
    K.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hface (t : Finset E) (ht : t ∈ K.faces)
      (u v : {v : K.vertices // 0 < A (v : E)})
      (hu : (u.val : E) ∈ t) (hv : (v.val : E) ∈ t) : G.Reachable u v := by
    by_cases huv : u = v
    · exact huv ▸ SimpleGraph.Reachable.rfl
    apply SimpleGraph.Adj.reachable
    have hune : u.val ≠ v.val := fun h => huv (Subtype.ext h)
    refine ⟨hune, ?_⟩
    change ({u.val, v.val} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces
    simp only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
    exact K.down_closed ht (by simpa only [Finset.insert_subset_iff,
      Finset.singleton_subset_iff] using And.intro hu hv) (Finset.insert_nonempty _ _)
  have hpositive {t : Finset E} {x : E}
      (hx : x ∈ convexHull ℝ (t : Set E)) (hxA : 0 < A x) :
      ∃ v ∈ t, 0 < A v := by
    by_contra h
    push_neg at h
    have hbound : convexHull ℝ (t : Set E) ⊆ {y | A y ≤ 0} :=
      convexHull_min (fun y hy => h y hy) ((convex_Iic (0 : ℝ)).affine_preimage A)
    exact hxA.not_ge (hbound hx)
  intro a b
  let Red (t : Finset E) : Prop :=
    ∃ v : {v : K.vertices // 0 < A (v : E)}, (v.val : E) ∈ t ∧ G.Reachable a v
  let U : Set E := ⋃ t ∈ {t | t ∈ K.faces ∧ Red t}, convexHull ℝ (t : Set E)
  let V : Set E := ⋃ t ∈ {t | t ∈ K.faces ∧ ¬ Red t}, convexHull ℝ (t : Set E)
  have hredFinite : {t | t ∈ K.faces ∧ Red t}.Finite := hK.subset (fun _ h => h.1)
  have hotherFinite : {t | t ∈ K.faces ∧ ¬ Red t}.Finite := hK.subset (fun _ h => h.1)
  have hU : IsClosed U := hredFinite.isClosed_biUnion
    (fun t _ => t.finite_toSet.isCompact_convexHull ℝ |>.isClosed)
  have hV : IsClosed V := hotherFinite.isClosed_biUnion
    (fun t _ => t.finite_toSet.isCompact_convexHull ℝ |>.isClosed)
  have hcover : K.space ∩ {x | 0 < A x} ⊆ U ∪ V := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx.1
    by_cases hr : Red t
    · exact Or.inl (mem_iUnion₂.mpr ⟨t, ⟨ht, hr⟩, hxt⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨t, ⟨ht, hr⟩, hxt⟩)
  have hdisj : (K.space ∩ {x | 0 < A x}) ∩ (U ∩ V) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hxU, hxV⟩
    obtain ⟨t, ⟨ht, htred⟩, hxt⟩ := mem_iUnion₂.mp hxU
    obtain ⟨u, ⟨hu, hunot⟩, hxu⟩ := mem_iUnion₂.mp hxV
    have hxinter : x ∈ convexHull ℝ ((t ∩ u : Finset E) : Set E) := by
      simpa only [Finset.coe_inter] using K.inter_subset_convexHull ht hu ⟨hxt, hxu⟩
    obtain ⟨v, hv, hvA⟩ := hpositive hxinter hx.2
    have hvt := (Finset.mem_inter.mp hv).1
    have hvu := (Finset.mem_inter.mp hv).2
    let v' : {v : K.vertices // 0 < A (v : E)} := ⟨⟨v, hvertex t ht v hvt⟩, hvA⟩
    obtain ⟨w, hwt, haw⟩ := htred
    exact hunot ⟨v', hvu, haw.trans (hface t ht w v' hwt hvt)⟩
  have haS : (a.val : E) ∈ K.space ∩ {x | 0 < A x} :=
    ⟨K.vertices_subset_space a.val.property, a.property⟩
  have haU : (a.val : E) ∈ U := by
    refine mem_iUnion₂.mpr ⟨{(a.val : E)}, ⟨a.val.property, ?_⟩, ?_⟩
    · exact ⟨a, Finset.mem_singleton_self _, SimpleGraph.Reachable.rfl⟩
    · exact subset_convexHull ℝ _ (Finset.mem_singleton_self _)
  have hside := isPreconnected_iff_subset_of_disjoint_closed.mp hconn U V hU hV hcover hdisj
  have hleft : K.space ∩ {x | 0 < A x} ⊆ U := hside.resolve_right (fun h => by
    have hx : (a.val : E) ∈ (K.space ∩ {x | 0 < A x}) ∩ (U ∩ V) :=
      ⟨haS, haU, h haS⟩
    rw [hdisj] at hx
    exact hx)
  have hbU : (b.val : E) ∈ U :=
    hleft ⟨K.vertices_subset_space b.val.property, b.property⟩
  obtain ⟨t, ⟨ht, hred⟩, hbt⟩ := mem_iUnion₂.mp hbU
  have hbmem : (b.val : E) ∈ t := (K.vertex_mem_convexHull_iff b.val.property ht).mp hbt
  obtain ⟨v, hvt, hav⟩ := hred
  exact hav.trans (hface t ht v b hvt hbmem)

end Geometry.SimplicialComplex
