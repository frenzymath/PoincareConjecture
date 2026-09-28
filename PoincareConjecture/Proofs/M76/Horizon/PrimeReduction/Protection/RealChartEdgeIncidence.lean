import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OrderedBranchCount
import PoincareConjecture.Proofs.M76.Mathlib.PureEdgeComplexPolygon
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.Complex.Circle








set_option autoImplicit false
open Set Geometry

namespace Geometry.SimplicialComplex

theorem neighbor_count_le_two_of_real_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (v : K.vertices)
    (q : OpenPartialHomeomorph K.space ℝ)
    (hv : (⟨v, K.vertices_subset_space v.property⟩ : K.space) ∈ q.source) :
    (K.vertexAbstractComplex.edgeGraph.neighborSet v).ncard ≤ 2 := by
  classical
  let G := K.vertexAbstractComplex.edgeGraph
  let N := G.neighborSet v
  let : Finite K.vertices := (K.finite_vertices_of_finite_faces hK).to_subtype
  let : Fintype N := Fintype.ofFinite N
  have hedge (w : N) : ({(v : E), (w.val : E)} : Finset E) ∈ K.faces := by
    have h := w.property.2
    change ({v, w.val} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces at h
    simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype] using h
  have hvw (w : N) : (v : E) ≠ (w.val : E) := fun h => w.property.1 (Subtype.ext h)
  let clock : ℝ → Icc (0 : ℝ) 1 := projIcc 0 1 (by norm_num)
  let f : N → ℝ → K.space := fun w t =>
    ⟨AffineMap.lineMap (v : E) (w.val : E) (clock t : ℝ),
      K.convexHull_subset_space (hedge w) (by
        simpa only [Finset.coe_pair, convexHull_pair] using
          lineMap_mem_segment ℝ (v : E) (w.val : E) (clock t).property)⟩
  let p : K.space := ⟨v, K.vertices_subset_space v.property⟩
  have hfval (w : N) {t : ℝ} (ht : t ∈ Icc 0 1) :
      (f w t : E) = AffineMap.lineMap (v : E) (w.val : E) t := by
    dsimp only [f, clock]
    rw [projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) ht]
  have hpunct (w : N) (t : ℝ) (ht : t ∈ Ioc 0 1) : f w t ≠ p := by
    intro h
    have heq := congrArg Subtype.val h
    rw [hfval w ⟨ht.1.le,ht.2⟩] at heq
    exact (AffineMap.lineMap_eq_left_iff.mp heq).elim (hvw w) (ne_of_gt ht.1)
  have hcard := PoincareConjecture.M76.card_le_two_of_disjoint_branches_in_real_chart f p
    (fun w => ((AffineMap.lineMap_continuous.comp
      (continuous_subtype_val.comp continuous_projIcc)).subtype_mk _).continuousOn)
    (fun w => Subtype.ext (by rw [hfval w (by simp), AffineMap.lineMap_apply_zero]))
    hpunct (by
      intro a b hab
      apply disjoint_left.mpr
      rintro y ⟨s, hs, hsy⟩ ⟨t, ht, hty⟩
      have habval : (a.val : E) ≠ (b.val : E) := fun h => hab (Subtype.ext (Subtype.ext h))
      have hfaces : (({(v : E), (a.val : E)} : Finset E) : Set E) ∩
          (({(v : E), (b.val : E)} : Finset E) : Set E) = {(v : E)} := by
        ext x
        simp only [Finset.coe_pair, mem_inter_iff, mem_insert_iff, mem_singleton_iff]
        aesop
      have hya : (y : E) ∈ convexHull ℝ (({(v : E), (a.val : E)} : Finset E) : Set E) := by
        rw [← hsy, hfval a ⟨hs.1.le, hs.2⟩]
        simpa only [Finset.coe_pair, convexHull_pair] using
          lineMap_mem_segment ℝ (v : E) (a.val : E) ⟨hs.1.le, hs.2⟩
      have hyb : (y : E) ∈ convexHull ℝ (({(v : E), (b.val : E)} : Finset E) : Set E) := by
        rw [← hty, hfval b ⟨ht.1.le, ht.2⟩]
        simpa only [Finset.coe_pair, convexHull_pair] using
          lineMap_mem_segment ℝ (v : E) (b.val : E) ⟨ht.1.le, ht.2⟩
      have hyv := K.inter_subset_convexHull (hedge a) (hedge b) ⟨hya, hyb⟩
      rw [hfaces, convexHull_singleton] at hyv
      exact hpunct a s hs (hsy.trans (Subtype.ext hyv))) q hv
  change N.ncard ≤ 2
  simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_card] using hcard

theorem neighbor_count_le_two_of_homeomorph_circle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (H : K.space ≃ₜ Circle) (v : K.vertices) :
    (K.vertexAbstractComplex.edgeGraph.neighborSet v).ncard ≤ 2 := by
  let : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  let p : K.space := ⟨v, K.vertices_subset_space v.property⟩
  let e : K.space ≃ₜ AddCircle (1 : ℝ) := H.trans (AddCircle.homeomorphCircle one_ne_zero).symm
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (e p)
  let Q := AddCircle.openPartialHomeomorphCoe (1 : ℝ) (a - 1 / 2)
  have haQ : a ∈ Q.source := by
    change a - 1 / 2 < a ∧ a < a - 1 / 2 + 1
    constructor <;> linarith
  apply K.neighbor_count_le_two_of_real_chart hK v (e.transOpenPartialHomeomorph Q.symm)
  change e p ∈ Q.target
  rw [← ha]
  exact Q.map_source haQ

end Geometry.SimplicialComplex
