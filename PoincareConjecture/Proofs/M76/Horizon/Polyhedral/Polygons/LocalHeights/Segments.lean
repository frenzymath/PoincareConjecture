import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.ZeroSet
import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalTriangleSlice









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

private theorem zero_crossing_segment (K : SimplicialComplex ℝ E)
    {A : Finset E → E →ᵃ[ℝ] ℝ} (hA : K.CompatibleTriangleZeroSets A)
    (q : K.triangleZeroVertices A) (e : K.triangleCrossingEdges A)
    (ht : insert q.val e.val ∈ K.faces) (htc : (insert q.val e.val).card = 3) :
    segment ℝ q.val (K.triangleCrossingPoint A e) =
      convexHull ℝ (↑(insert q.val e.val) : Set E) ∩ K.triangleZeroSet A := by
  let t := insert q.val e.val
  have hqt : A t q.val = 0 := K.triangleZeroVertex_zero hA q ht htc (by simp [t])
  have he := K.triangleCrossingEdge_straddles hA e ht htc (Finset.subset_insert _ _)
  rw [K.convexHull_inter_triangleZeroSet hA ht htc,
    K.triangleCrossingPoint_eq hA e ht htc (Finset.subset_insert _ _) he]
  have hecopy := he
  obtain ⟨u, v, hu, hv, heq⟩ := hecopy
  rw [(A (insert q.val e.val)).straddlingPoint_eq_zeroCrossing he hu hv heq,
    Finset.coe_insert, heq]
  exact ((A t).convexHull_zero_apex_pair_inter_zero hqt hu hv).symm



theorem triangleSliceGraph_segment (K : SimplicialComplex ℝ E)
    {A : Finset E → E →ᵃ[ℝ] ℝ} (hA : K.CompatibleTriangleZeroSets A)
    {a b : K.TriangleSliceLabel A} (hab : (K.triangleSliceGraph A).Adj a b) :
    segment ℝ (K.triangleSlicePoint A a) (K.triangleSlicePoint A b) =
      convexHull ℝ (↑(K.triangleSliceOriginalVertices A a ∪
        K.triangleSliceOriginalVertices A b) : Set E) ∩ K.triangleZeroSet A := by
  cases a with
  | inl q =>
    cases b with
    | inl r => exact False.elim (K.triangleSliceGraph_not_adj_zero A q r hab)
    | inr e =>
      change ({q.val} ∪ e.val ∈ K.faces ∧ ({q.val} ∪ e.val).card = 3) at hab
      simp only [Finset.singleton_union] at hab
      simpa only [triangleSliceOriginalVertices, triangleSlicePoint, Finset.singleton_union]
        using K.zero_crossing_segment hA q e hab.1 hab.2
  | inr e =>
    cases b with
    | inl q =>
      change (e.val ∪ {q.val} ∈ K.faces ∧ (e.val ∪ {q.val}).card = 3) at hab
      simp only [Finset.union_singleton] at hab
      simpa only [triangleSliceOriginalVertices, triangleSlicePoint, Finset.union_singleton]
        using (segment_symm ℝ (K.triangleCrossingPoint A e) q.val).trans
          (K.zero_crossing_segment hA q e hab.1 hab.2)
    | inr f =>
      change e.val ∪ f.val ∈ K.faces ∧ (e.val ∪ f.val).card = 3 at hab
      let t := e.val ∪ f.val
      have he := K.triangleCrossingEdge_straddles hA e hab.1 hab.2 Finset.subset_union_left
      have hf := K.triangleCrossingEdge_straddles hA f hab.1 hab.2 Finset.subset_union_right
      have hef : e.val ≠ f.val := by
        intro h
        have hc := hab.2
        rw [h, Finset.union_self, K.triangleCrossingEdge_card A f] at hc
        omega
      have hreg : ∀ v ∈ t, A t v ≠ 0 := by
        intro v hv
        rcases Finset.mem_union.mp hv with hv | hv
        · exact he.ne_zero hv
        · exact hf.ne_zero hv
      change segment ℝ (K.triangleCrossingPoint A e) (K.triangleCrossingPoint A f) =
        convexHull ℝ (t : Set E) ∩ K.triangleZeroSet A
      rw [K.convexHull_inter_triangleZeroSet hA hab.1 hab.2,
        K.triangleCrossingPoint_eq hA e hab.1 hab.2 Finset.subset_union_left he,
        K.triangleCrossingPoint_eq hA f hab.1 hab.2 Finset.subset_union_right hf]
      exact (A t).segment_straddlingPoints_eq_triangleSlice he hf hab.2 hreg
        Finset.subset_union_left Finset.subset_union_right hef

end Geometry.SimplicialComplex
