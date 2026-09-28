import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ModTwoCochainIncidence

set_option autoImplicit false

open Set
open scoped BigOperators

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*} (A : PreAbstractSimplicialComplex ι)

abbrev Tetrahedron := {s : Finset ι // s ∈ A.faces ∧ s.card = 4}

variable [Fintype ι]

open Classical in

noncomputable def tetrahedronTriangles (q : Tetrahedron A) : Finset (Triangle A) :=
  Finset.univ.filter (fun t => t.val ⊆ q.val)

open Classical in

noncomputable def edgeTetrahedronTriangles (e : Edge A) (q : Tetrahedron A) :
    Finset (Triangle A) :=
  Finset.univ.filter (fun t => e.val ⊆ t.val ∧ t.val ⊆ q.val)

noncomputable def triangleCoboundary :
    (Triangle A → ZMod 2) →ₗ[ZMod 2] (Tetrahedron A → ZMod 2) :=
  LinearMap.pi fun q => ∑ t ∈ tetrahedronTriangles A q, LinearMap.proj t

theorem triangleCoboundary_apply (c : Triangle A → ZMod 2) (q : Tetrahedron A) :
    triangleCoboundary A c q = ∑ t ∈ tetrahedronTriangles A q, c t := by
  simp [triangleCoboundary]

open Classical in

theorem edgeTetrahedronTriangles_card (e : Edge A) (q : Tetrahedron A) :
    (edgeTetrahedronTriangles A e q).card = if e.val ⊆ q.val then 2 else 0 := by
  classical
  by_cases heq : e.val ⊆ q.val
  · rw [if_pos heq]
    have hdiff : (q.val \ e.val).card = 2 := by
      rw [Finset.card_sdiff_of_subset heq, q.property.2, e.property.2]
    obtain ⟨i, j, hij, hdiff⟩ := Finset.card_eq_two.mp hdiff
    have hi : i ∈ q.val ∧ i ∉ e.val := Finset.mem_sdiff.mp (by rw [hdiff]; simp)
    have hj : j ∈ q.val ∧ j ∉ e.val := Finset.mem_sdiff.mp (by rw [hdiff]; simp)
    have hface (v : ι) (hvq : v ∈ q.val) (hve : v ∉ e.val) :
        insert v e.val ∈ A.faces ∧ (insert v e.val).card = 3 := by
      refine ⟨(A.isRelLowerSet_faces q.property.1).2
        (Finset.insert_subset_iff.mpr ⟨hvq, heq⟩) (Finset.insert_nonempty v e.val), ?_⟩
      rw [Finset.card_insert_of_notMem hve, e.property.2]
    let ti : Triangle A := ⟨insert i e.val, hface i hi.1 hi.2⟩
    let tj : Triangle A := ⟨insert j e.val, hface j hj.1 hj.2⟩
    have htij : ti ≠ tj := by
      intro h
      have hm : i ∈ tj.val := congrArg Subtype.val h ▸ Finset.mem_insert_self i e.val
      exact hij ((Finset.mem_insert.mp hm).resolve_right hi.2)
    have hset : edgeTetrahedronTriangles A e q = {ti, tj} := by
      ext t
      simp only [edgeTetrahedronTriangles, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨het, htq⟩
        have hdiffT : (t.val \ e.val).card = 1 := by
          rw [Finset.card_sdiff_of_subset het, t.property.2, e.property.2]
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hdiffT
        have hvmem : v ∈ t.val \ e.val := hv.symm ▸ Finset.mem_singleton_self v
        have hvq : v ∈ q.val \ e.val :=
          Finset.mem_sdiff.mpr ⟨htq (Finset.mem_sdiff.mp hvmem).1,
            (Finset.mem_sdiff.mp hvmem).2⟩
        have ht : insert v e.val = t.val := by
          rw [← Finset.singleton_union, ← hv, Finset.sdiff_union_of_subset het]
        rw [hdiff] at hvq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hvq
        rcases hvq with rfl | rfl
        · exact Or.inl (Subtype.ext ht.symm)
        · exact Or.inr (Subtype.ext ht.symm)
      · rintro (rfl | rfl)
        · exact ⟨Finset.subset_insert i e.val, Finset.insert_subset_iff.mpr ⟨hi.1, heq⟩⟩
        · exact ⟨Finset.subset_insert j e.val, Finset.insert_subset_iff.mpr ⟨hj.1, heq⟩⟩
    rw [hset, Finset.card_pair htij]
  · rw [if_neg heq]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact heq ((Finset.mem_filter.mp ht).2.1.trans (Finset.mem_filter.mp ht).2.2)

theorem triangleCoboundary_edgeCoboundary (z : Edge A → ZMod 2) :
    triangleCoboundary A (edgeCoboundary A z) = 0 := by
  classical
  funext q
  rw [triangleCoboundary_apply]
  simp_rw [edgeCoboundary_apply]
  calc
    (∑ t ∈ tetrahedronTriangles A q, ∑ e ∈ triangleEdges A t, z e) =
        ∑ e : Edge A, ∑ t ∈ edgeTetrahedronTriangles A e q, z e := by
      simp only [tetrahedronTriangles, triangleEdges, edgeTetrahedronTriangles,
        Finset.sum_filter, Finset.ite_sum_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro t _
      by_cases het : e.val ⊆ t.val <;> by_cases htq : t.val ⊆ q.val <;> simp [het, htq]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      rw [Finset.sum_const, edgeTetrahedronTriangles_card]
      by_cases heq : e.val ⊆ q.val
      · rw [if_pos heq]
        exact CharTwo.two_nsmul (z e)
      · rw [if_neg heq, zero_nsmul]

theorem boundary2_boundary3
    (z : Module.Dual (ZMod 2) (Tetrahedron A → ZMod 2)) :
    (edgeCoboundary A).dualMap ((triangleCoboundary A).dualMap z) = 0 := by
  ext a
  change z (triangleCoboundary A (edgeCoboundary A a)) = 0
  rw [triangleCoboundary_edgeCoboundary, map_zero]

end PreAbstractSimplicialComplex.ModTwoCochains
