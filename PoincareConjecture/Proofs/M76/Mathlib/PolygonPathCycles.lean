import PoincareConjecture.Proofs.M76.Mathlib.PathEdgeSums
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialPolygon












set_option autoImplicit false

open Set Geometry

namespace Polygon

variable {E : Type*} {m n : ℕ}




def ofPaths (u : Fin (m + 1) → E) (v : Fin (n + 1) → E) : Polygon E (m + n) :=
  mk (Fin.append (Fin.init u) (Fin.init v))




theorem injective_ofPaths (u : Fin (m + 2) → E) (v : Fin (n + 2) → E)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (huv : u (Fin.last (m + 1)) = v 0)
    (hvu : v (Fin.last (n + 1)) = u 0)
    (hinter : range u ∩ range v ⊆ {u 0, v 0}) :
    Function.Injective (ofPaths u v) := by
  apply Fin.append_injective_iff.mpr
  refine ⟨hu.comp (Fin.castSucc_injective _), hv.comp (Fin.castSucc_injective _), ?_⟩
  intro i j hij
  have hi : u i.castSucc ∈ range u ∩ range v :=
    ⟨mem_range_self _, ⟨j.castSucc, hij.symm⟩⟩
  rcases hinter hi with ha | hb
  · have hj : v j.castSucc = v (Fin.last (n + 1)) :=
      hij.symm.trans (ha.trans hvu.symm)
    exact (Fin.castSucc_ne_last j) (hv hj)
  · have hi' : u i.castSucc = u (Fin.last (m + 1)) := hb.trans huv.symm
    exact (Fin.castSucc_ne_last i) (hu hi')

variable [AddCommGroup E] [Module ℝ E]





def pathCarrier (u : Fin (n + 1) → E) : Set E :=
  ⋃ i : Fin n, segment ℝ (u i.castSucc) (u i.succ)



theorem vertex_mem_pathCarrier (u : Fin (n + 2) → E) (i : Fin (n + 2)) :
    u i ∈ pathCarrier u := by
  induction i using Fin.lastCases with
  | last =>
    exact mem_iUnion.mpr ⟨Fin.last n, right_mem_segment ℝ _ _⟩
  | cast i => exact mem_iUnion.mpr ⟨i, left_mem_segment ℝ _ _⟩




theorem pathCarrier_reverse (u : Fin (n + 1) → E) :
    pathCarrier (fun i => u i.rev) = pathCarrier u := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    simp only [Fin.rev_castSucc, Fin.rev_succ] at hi
    exact mem_iUnion.mpr ⟨i.rev, by rw [segment_symm]; exact hi⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    apply mem_iUnion.mpr
    refine ⟨i.rev, ?_⟩
    simpa only [Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev, segment_symm] using hi

omit [AddCommGroup E] [Module ℝ E] in


theorem edgeVertices_ofPaths_left [DecidableEq E]
    (u : Fin (m + 2) → E) (v : Fin (n + 2) → E)
    (huv : u (Fin.last (m + 1)) = v 0) (i : Fin (m + 1)) :
    (ofPaths u v).edgeVertices (i.castAdd (n + 1)) = {u i.castSucc, u i.succ} := by
  classical
  simp only [ofPaths, edgeVertices, Fin.append_left, Fin.append_finRotate_castAdd]
  rw [show Fin.init v 0 = u (Fin.last (m + 1)) from huv.symm, Fin.snoc_init_self]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.init]

omit [AddCommGroup E] [Module ℝ E] in


theorem edgeVertices_ofPaths_right [DecidableEq E]
    (u : Fin (m + 2) → E) (v : Fin (n + 2) → E)
    (hvu : v (Fin.last (n + 1)) = u 0) (i : Fin (n + 1)) :
    (ofPaths u v).edgeVertices (Fin.natAdd (m + 1) i) = {v i.castSucc, v i.succ} := by
  classical
  simp only [ofPaths, edgeVertices, Fin.append_right, Fin.append_finRotate_natAdd]
  rw [show Fin.init u 0 = v (Fin.last (n + 1)) from hvu.symm, Fin.snoc_init_self]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.init]




theorem boundary_ofPaths (u : Fin (m + 2) → E) (v : Fin (n + 2) → E)
    (huv : u (Fin.last (m + 1)) = v 0)
    (hvu : v (Fin.last (n + 1)) = u 0) :
    (ofPaths u v).boundary ℝ = pathCarrier u ∪ pathCarrier v := by
  classical
  have hleft (i : Fin (m + 1)) :
      (ofPaths u v).edgeSet ℝ (i.castAdd (n + 1)) =
        segment ℝ (u i.castSucc) (u i.succ) := by
    rw [edgeSet_eq_convexHull, edgeVertices_ofPaths_left u v huv,
      Finset.coe_pair, convexHull_pair]
  have hright (i : Fin (n + 1)) :
      (ofPaths u v).edgeSet ℝ (Fin.natAdd (m + 1) i) =
        segment ℝ (v i.castSucc) (v i.succ) := by
    rw [edgeSet_eq_convexHull, edgeVertices_ofPaths_right u v hvu,
      Finset.coe_pair, convexHull_pair]
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    induction i using Fin.addCases with
    | left i => exact Or.inl (mem_iUnion.mpr ⟨i, hleft i ▸ hi⟩)
    | right i => exact Or.inr (mem_iUnion.mpr ⟨i, hright i ▸ hi⟩)
  · rintro (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i.castAdd (n + 1), (hleft i).symm ▸ hi⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨Fin.natAdd (m + 1) i, (hright i).symm ▸ hi⟩





theorem hasSimplicialEdges_ofPaths [DecidableEq E]
    (K : SimplicialComplex ℝ E)
    (u : Fin (m + 2) → E) (v : Fin (n + 2) → E)
    (huv : u (Fin.last (m + 1)) = v 0)
    (hvu : v (Fin.last (n + 1)) = u 0)
    (hu : ∀ i : Fin (m + 1), ({u i.castSucc, u i.succ} : Finset E) ∈ K.faces)
    (hv : ∀ i : Fin (n + 1), ({v i.castSucc, v i.succ} : Finset E) ∈ K.faces) :
    (ofPaths u v).HasSimplicialEdges := by
  have hface (i : Fin ((m + 1) + (n + 1))) : (ofPaths u v).edgeVertices i ∈ K.faces := by
    induction i using Fin.addCases with
    | left i => rw [edgeVertices_ofPaths_left u v huv]; exact hu i
    | right i => rw [edgeVertices_ofPaths_right u v hvu]; exact hv i
  intro i j
  rw [edgeSet_eq_convexHull, edgeSet_eq_convexHull]
  exact K.inter_subset_convexHull (hface i) (hface j)

end Polygon
