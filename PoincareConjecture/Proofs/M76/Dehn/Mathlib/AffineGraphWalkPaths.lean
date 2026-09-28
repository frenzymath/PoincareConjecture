import PoincareConjecture.Proofs.M76.Dehn.Mathlib.AffineGraphPartition
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.GeometricWalkPaths
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.GraphWalkConcatenation

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

private theorem concat_range_subset {X : Type*} [TopologicalSpace X] {n : ℕ}
    (p : Fin (n + 1) → X)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ)) {S : Set X}
    (hzero : p 0 ∈ S) (hF : ∀ i, range (F i) ⊆ S) :
    range (Path.concat p F) ⊆ S := by
  induction n with
  | zero =>
    rw [Path.concat_zero, Path.refl_range]
    exact singleton_subset_iff.mpr hzero
  | succ n ih =>
    erw [Path.concat_succ, Path.trans_range]
    exact union_subset
      (ih (p ∘ Fin.castSucc) (fun i => F i.castSucc) hzero (fun i => hF i.castSucc))
      (hF (Fin.last n))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E)

theorem exists_geometric_walk_homotopic_of_affine
    (hK : K.faces.Finite) (hdim : ∀ s ∈ K.faces, s.card ≤ 2)
    (A : ℝ →ᴬ[ℝ] E) {l u : ℝ} (hlu : l < u)
    (hA : MapsTo A (Icc l u) K.space)
    {a b : K.vertices} (ha : (a : E) = A l) (hb : (b : E) = A u)
    (p : Path (⟨a, K.vertices_subset_space a.property⟩ : K.space)
      ⟨b, K.vertices_subset_space b.property⟩)
    (hp : ∀ z, (p z : E) ∈ segment ℝ (A l) (A u)) :
    ∃ w : K.vertexAbstractComplex.edgeGraph.Walk a b,
      (K.geometricWalkPath w).Homotopic p := by
  have himage : A '' Icc l u = segment ℝ (A l) (A u) := by
    rw [← segment_eq_Icc hlu.le]
    exact image_segment ℝ A.toAffineMap _ _
  have hseg : segment ℝ (A l) (A u) ⊆ K.space := by
    rw [← himage]
    exact image_subset_iff.mpr hA
  rcases A.injective_or_const_real with hinj | hconst
  · obtain ⟨n, t, ht, ht0, ht1, hvertices, hfaces⟩ :=
      K.exists_affine_graph_partition hK hdim A hinj hlu hA
        (ha ▸ a.property) (hb ▸ b.property)
    let r : Fin (n + 2) → K.vertices := fun i => ⟨A (t i), hvertices i⟩
    have hr0 : r 0 = a := Subtype.ext ((congrArg A ht0).trans ha.symm)
    have hr1 : r (Fin.last (n + 1)) = b :=
      Subtype.ext ((congrArg A ht1).trans hb.symm)
    subst a
    subst b
    have hparam (i : Fin (n + 2)) : t i ∈ Icc l u := by
      constructor
      · rw [← ht0]
        exact ht.monotone (Fin.zero_le i)
      · rw [← ht1]
        exact ht.monotone (Fin.le_last i)
    have hr (i : Fin (n + 2)) : (r i : E) ∈ segment ℝ (A l) (A u) :=
      himage.subset (mem_image_of_mem A (hparam i))
    have hedge (i : Fin (n + 1)) :
        K.vertexAbstractComplex.edgeGraph.Adj (r i.castSucc) (r i.succ) := by
      constructor
      · intro he
        exact (ne_of_lt (ht Fin.castSucc_lt_succ)) (hinj (congrArg Subtype.val he))
      · change ({r i.castSucc, r i.succ} : Finset K.vertices).map
          (Function.Embedding.subtype _) ∈ K.faces
        simpa only [r, Finset.map_insert, Finset.map_singleton,
          Function.Embedding.coe_subtype] using hfaces i
    let w : (i : Fin (n + 1)) →
        K.vertexAbstractComplex.edgeGraph.Walk (r i.castSucc) (r i.succ) :=
      fun i => .cons (hedge i) .nil
    let j : K.vertices → K.space := fun x => ⟨x, K.vertices_subset_space x.property⟩
    have hstep (i : Fin (n + 1)) : range (K.geometricWalkPath (w i)) ⊆
        Subtype.val ⁻¹' segment ℝ (A l) (A u) := by
      change range ((K.geometricEdgePath (hedge i)).trans (Path.refl (j (r i.succ)))) ⊆ _
      rw [Path.trans_range, Path.refl_range]
      refine union_subset ?_ (singleton_subset_iff.mpr (hr i.succ))
      rintro _ ⟨z, rfl⟩
      exact (convex_segment (A l) (A u)).lineMap_mem (hr i.castSucc) (hr i.succ) z.property
    have hconcat := concat_range_subset (j ∘ r)
      (fun i => K.geometricWalkPath (w i)) (hr 0) hstep
    refine ⟨SimpleGraph.Walk.concatSequence r w, ?_⟩
    have hreal : (K.geometricWalkPath (SimpleGraph.Walk.concatSequence r w)).Homotopic
        (Path.concat (j ∘ r) (fun i => K.geometricWalkPath (w i))) :=
      Path.Homotopic.Quotient.eq.mp
        (SimpleGraph.Walk.realizePath_concatSequence j (fun h => K.geometricEdgePath h) r w)
    exact hreal.trans (Path.homotopic_of_convex_range (convex_segment _ _) hseg
      _ p (fun z => hconcat (mem_range_self z)) hp)
  · have hab : a = b := Subtype.ext
      (ha.trans ((hconst l).trans ((hconst u).symm.trans hb.symm)))
    subst b
    refine ⟨.nil, ?_⟩
    apply Path.homotopic_of_convex_range (convex_segment _ _) hseg _ p _ hp
    intro z
    change (a : E) ∈ segment ℝ (A l) (A u)
    rw [ha]
    exact left_mem_segment ℝ _ _

end Geometry.SimplicialComplex
