import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleChainKernel
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VertexTriangleIncidence











set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*} [Fintype ι] (A : PreAbstractSimplicialComplex ι)

open Classical in


theorem boundary2_ker_coordinates_of_common_edge
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card ≤ 2)
    (c : Module.Dual (ZMod 2) (Triangle A → ZMod 2))
    (hc : (edgeCoboundary A).dualMap c = 0)
    (e : Edge A) (q r : Triangle A) (heq : e.val ⊆ q.val) (her : e.val ⊆ r.val) :
    c (Pi.single q 1) = c (Pi.single r 1) := by
  by_cases hqr : q = r
  · rw [hqr]
  · have hpair := triangleCofaces_eq_pair_of_distinct A hcofaces e q r hqr heq her
    have hz : (edgeCoboundary A).dualMap c (Pi.single e 1) = 0 := by rw [hc]; rfl
    rw [boundary2_single_eq_sum_coordinates, hpair, Finset.sum_pair hqr] at hz
    exact CharTwo.add_eq_zero.mp hz

end PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.vertices]

local notation "L" => K.vertexAbstractComplex.toPreAbstractSimplicialComplex

open Classical in



theorem boundary2_ker_coordinates_of_common_vertex
    (hpure : ∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3)
    (hcofaces : ∀ e : Edge L, (triangleCofaces L e).card ≤ 2)
    (p : K.vertices)
    (hlink : (K.faceLink {p.val}).vertexAbstractComplex.edgeGraph.Preconnected)
    (c : Module.Dual (ZMod 2) (Triangle L → ZMod 2))
    (hc : (edgeCoboundary L).dualMap c = 0)
    (q r : Triangle L) (hpq : p ∈ q.val) (hpr : p ∈ r.val) :
    c (Pi.single q 1) = c (Pi.single r 1) := by
  classical
  let a : Triangle K.toPreAbstractSimplicialComplex → ZMod 2 :=
    fun t => c (Pi.single ((K.vertexFaceEquiv 3).symm t) 1)
  have hnext (w : (K.faceLink {p.val}).vertices)
      (u z : Triangle K.toPreAbstractSimplicialComplex)
      (hwu : insert w.val {p.val} ⊆ u.val)
      (hwz : insert w.val {p.val} ⊆ z.val) : a u = a z := by
    have hwface : insert w.val {p.val} ∈ K.faces := by
      simpa only [Finset.union_singleton] using w.property.2.2
    have hwc : (insert w.val {p.val} : Finset E).card = 2 := by
      rw [Finset.card_insert_of_notMem
        (K.faceLink_vertices_subset {p.val} w.property).2, Finset.card_singleton]
    let e : Edge K.toPreAbstractSimplicialComplex := ⟨insert w.val {p.val}, hwface, hwc⟩
    have heu : ((K.vertexFaceEquiv 2).symm e).val ⊆
        ((K.vertexFaceEquiv 3).symm u).val := by
      apply Finset.map_subset_map.mp
      change ((K.vertexFaceEquiv 2).symm e).val.map (Function.Embedding.subtype _) ⊆
        ((K.vertexFaceEquiv 3).symm u).val.map (Function.Embedding.subtype _)
      rw [K.vertexFaceEquiv_symm_map, K.vertexFaceEquiv_symm_map]
      exact hwu
    have hez : ((K.vertexFaceEquiv 2).symm e).val ⊆
        ((K.vertexFaceEquiv 3).symm z).val := by
      apply Finset.map_subset_map.mp
      change ((K.vertexFaceEquiv 2).symm e).val.map (Function.Embedding.subtype _) ⊆
        ((K.vertexFaceEquiv 3).symm z).val.map (Function.Embedding.subtype _)
      rw [K.vertexFaceEquiv_symm_map, K.vertexFaceEquiv_symm_map]
      exact hwz
    have hcoef := boundary2_ker_coordinates_of_common_edge L hcofaces c hc
      ((K.vertexFaceEquiv 2).symm e) ((K.vertexFaceEquiv 3).symm u)
      ((K.vertexFaceEquiv 3).symm z) heu hez
    change c (Pi.single ((K.vertexFaceEquiv 3).symm u) 1) =
      c (Pi.single ((K.vertexFaceEquiv 3).symm z) 1)
    convert hcoef using 1
    · congr 1
      funext i
      by_cases hi : i = (K.vertexFaceEquiv 3).symm u <;> simp [hi]
    · congr 1
      funext i
      by_cases hi : i = (K.vertexFaceEquiv 3).symm z <;> simp [hi]
  have hq : {p.val} ⊆ (K.vertexFaceEquiv 3 q).val := by
    apply Finset.singleton_subset_iff.mpr
    exact Finset.mem_map.mpr ⟨p, hpq, rfl⟩
  have hr : {p.val} ⊆ (K.vertexFaceEquiv 3 r).val := by
    apply Finset.singleton_subset_iff.mpr
    exact Finset.mem_map.mpr ⟨p, hpr, rfl⟩
  have h := K.triangle_coface_constancy_of_link a hpure (s := {p.val})
    (by simp) hlink hnext (K.vertexFaceEquiv 3 q) (K.vertexFaceEquiv 3 r) hq hr
  simpa only [a, Equiv.symm_apply_apply] using h

end Geometry.SimplicialComplex
