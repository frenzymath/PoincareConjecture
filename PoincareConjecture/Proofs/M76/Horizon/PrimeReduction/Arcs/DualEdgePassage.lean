import PoincareConjecture.Proofs.M76.Mathlib.BarycentricBoundaryFacetInterval
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.DualBlockUnionBoundary

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

omit [FiniteDimensional ℝ E] [DecidableEq E] in

theorem mem_vertexDualUnion_iff_of_vertex
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (S : Set K.vertices) (p : K.vertices) :
    p.val ∈ K.vertexDualUnion S ↔ p ∈ S := by
  classical
  constructor
  · intro hp
    obtain ⟨w, hwS, hpw⟩ := mem_iUnion₂.mp hp
    obtain ⟨a, ha, hpa⟩ := mem_space_iff.mp hpw
    have hpB : p.val ∈ K.barycentricSubdivision.vertices :=
      (K.mem_barycentricSubdivision_vertices_iff _).mpr
        ⟨{p.val}, p.property, by simp only [Finset.centroid_singleton, id_eq]⟩
    have hpa' := (K.barycentricSubdivision.vertex_mem_convexHull_iff hpB ha.1).mp hpa
    obtain ⟨t, ht, hwt, htp⟩ := ha.2 p.val hpa'
    have hequal : (⟨t, ht⟩ : K.faces) = ⟨{p.val}, p.property⟩ :=
      K.faceCentroid_injective (by simpa only [Finset.centroid_singleton, id_eq] using htp)
    have ht' : t = {p.val} := congrArg Subtype.val hequal
    have hwp : w = p := Subtype.ext (Finset.mem_singleton.mp
      (ht' ▸ hwt (Finset.mem_singleton_self _)))
    exact hwp ▸ hwS
  · intro hp
    apply mem_iUnion₂.mpr
    refine ⟨p, hp, ?_⟩
    have hh := (K.barycentricDualBlock {p.val}).vertices_subset_space
      (K.faceCentroid_mem_barycentricDualBlock_vertices p.property)
    simpa only [Finset.centroid_singleton, id_eq] using hh

theorem vertexDualUnion_edge_passage
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (S : Set K.vertices) (p q : K.vertices) (hpq : p ≠ q)
    (he : ({p.val, q.val} : Finset E) ∈ K.faces) (hp : p ∈ S) (hq : q ∉ S) :
    let c := ({p.val, q.val} : Finset E).centroid ℝ id
    c ≠ p.val ∧
      K.vertexDualUnion S ∩ segment ℝ p.val q.val = segment ℝ p.val c ∧
      K.vertexDualRim S ∩ segment ℝ p.val q.val = {c} := by
  classical
  let e : Finset E := {p.val, q.val}
  let c := e.centroid ℝ id
  have hpq' : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
  have he2 : e.card = 2 := Finset.card_pair hpq'
  let T : SimplicialComplex ℝ E :=
    { faces := {a | a ∈ K.faces ∧ a ⊆ e}
      indep := fun ha => K.indep ha.1
      isRelLowerSet_faces := by
        intro a ha
        refine ⟨K.nonempty_of_mem_faces ha.1, ?_⟩
        intro b hba hb
        exact ⟨K.down_closed ha.1 hba hb, hba.trans ha.2⟩
      inter_subset_convexHull := fun ha hb => K.inter_subset_convexHull ha.1 hb.1 }
  have hTK : T ≤ K := fun _ ha => ha.1
  have hT : T.faces.Finite := (Set.toFinite K.faces).subset hTK
  let : Fintype T.faces := hT.fintype
  have heT : e ∈ T.faces := ⟨he, Finset.Subset.rfl⟩
  have hTs : T.space = segment ℝ p.val q.val := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨a, ha, hxa⟩ := mem_space_iff.mp hx
      have hh := convexHull_mono ha.2 hxa
      simpa only [e, Finset.coe_pair, convexHull_pair] using hh
    · intro x hx
      exact T.convexHull_subset_space heT (by
        simpa only [e, Finset.coe_pair, convexHull_pair] using hx)
  have hcard (a : Finset E) (ha : a ∈ T.faces) : a.card ≤ 1 + 1 :=
    (Finset.card_le_card ha.2).trans_eq he2
  have hblock {w : E} (hw : w ∈ e) :
      (T.barycentricDualBlock {w}).space = segment ℝ w c := by
    have hwT : ({w} : Finset E) ∈ T.faces :=
      T.down_closed heT (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty _)
    have hco (a : Finset E) (ha : a ∈ T.faces) (_ : {w} ⊆ a)
        (ha2 : a.card = 1 + 1) : a = e :=
      Finset.eq_of_subset_of_card_le ha.2 (by omega)
    have hh := (T.barycentricDualBlock_of_single_coface hcard hwT heT
      (Finset.card_singleton _) he2 (Finset.singleton_subset_iff.mpr hw) hco).1
    simpa only [Finset.centroid_singleton, id_eq] using hh
  have hnot {w : E} (hw : w ∉ e) : (T.barycentricDualBlock {w}).space = ∅ :=
    T.barycentricDualBlock_space_eq_empty_of_not_face (Finset.singleton_nonempty _)
      (fun h => hw (h.2 (Finset.mem_singleton_self _)))
  have hrestrict (w : K.vertices) :
      (K.barycentricDualBlock {w.val}).space ∩ segment ℝ p.val q.val =
        (T.barycentricDualBlock {w.val}).space := by
    rw [← hTs]
    exact K.barycentricDualBlock_space_inter_subcomplex T hTK _
  have hunion (A : Set K.vertices) :
      K.vertexDualUnion A ∩ segment ℝ p.val q.val =
        (⋃ (_ : p ∈ A), segment ℝ p.val c) ∪ (⋃ (_ : q ∈ A), segment ℝ q.val c) := by
    ext x
    constructor
    · rintro ⟨hx, hxe⟩
      obtain ⟨w, hwA, hxw⟩ := mem_iUnion₂.mp hx
      have hxT := (hrestrict w).subset ⟨hxw, hxe⟩
      by_cases hwp : w = p
      · subst w
        rw [hblock (Finset.mem_insert_self _ _)] at hxT
        exact Or.inl (mem_iUnion.mpr ⟨hwA, hxT⟩)
      by_cases hwq : w = q
      · subst w
        rw [hblock (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))] at hxT
        exact Or.inr (mem_iUnion.mpr ⟨hwA, hxT⟩)
      · have hwe : w.val ∉ e := by
          simpa only [e, Finset.mem_insert, Finset.mem_singleton, not_or] using
            And.intro (fun h => hwp (Subtype.ext h)) (fun h => hwq (Subtype.ext h))
        rw [hnot hwe] at hxT
        exact hxT.elim
    · rintro (hx | hx)
      · obtain ⟨hpA, hx⟩ := mem_iUnion.mp hx
        have hxT := (hblock (Finset.mem_insert_self p.val {q.val})).symm.subset hx
        have hh := (hrestrict p).symm.subset hxT
        exact ⟨mem_iUnion₂.mpr ⟨p, hpA, hh.1⟩, hh.2⟩
      · obtain ⟨hqA, hx⟩ := mem_iUnion.mp hx
        have hxT := (hblock (Finset.mem_insert_of_mem (Finset.mem_singleton_self q.val))).symm.subset hx
        have hh := (hrestrict q).symm.subset hxT
        exact ⟨mem_iUnion₂.mpr ⟨q, hqA, hh.1⟩, hh.2⟩
  have hselected : K.vertexDualUnion S ∩ segment ℝ p.val q.val = segment ℝ p.val c := by
    simpa only [hp, hq, iUnion_true, iUnion_false, union_empty] using hunion S
  have hother : K.vertexDualUnion Sᶜ ∩ segment ℝ p.val q.val = segment ℝ q.val c := by
    simpa only [mem_compl_iff, hp, hq, not_true_eq_false, not_false_eq_true,
      iUnion_true, iUnion_false, empty_union] using hunion Sᶜ
  have hfull : (T.barycentricDualBlock e).space = {c} := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨a, ha, hxa⟩ := mem_space_iff.mp hx
      have hasub : (a : Set E) ⊆ {c} := by
        intro y hy
        obtain ⟨t, ht, het, hty⟩ := ha.2 y hy
        have hte : t = e := Finset.Subset.antisymm ht.2 het
        exact hty.symm.trans (congrArg (fun v : Finset E => v.centroid ℝ id) hte)
      simpa only [convexHull_singleton] using convexHull_mono hasub hxa
    · rintro x rfl
      exact (T.barycentricDualBlock e).vertices_subset_space
        (T.faceCentroid_mem_barycentricDualBlock_vertices heT)
  have hmeet : segment ℝ p.val c ∩ segment ℝ q.val c = {c} := by
    rw [← hblock (Finset.mem_insert_self p.val {q.val}),
      ← hblock (Finset.mem_insert_of_mem (Finset.mem_singleton_self q.val)),
      T.barycentricDualBlock_space_inter]
    simpa only [Finset.singleton_union] using hfull
  have hcp : c ≠ p.val := by
    intro h
    have hpT : ({p.val} : Finset E) ∈ T.faces :=
      T.down_closed heT (by simp [e]) (Finset.singleton_nonempty _)
    have hequal : (⟨e, heT⟩ : T.faces) = ⟨{p.val}, hpT⟩ :=
      T.faceCentroid_injective (by simpa only [Finset.centroid_singleton, id_eq] using h)
    have hh : e = {p.val} := congrArg Subtype.val hequal
    have := congrArg Finset.card hh
    simp only [he2, Finset.card_singleton] at this
    omega
  refine ⟨hcp, hselected, ?_⟩
  change (K.vertexDualUnion S ∩ K.vertexDualUnion Sᶜ) ∩ _ = _
  rw [inter_inter_distrib_right, hselected, hother, hmeet]

end Geometry.SimplicialComplex
