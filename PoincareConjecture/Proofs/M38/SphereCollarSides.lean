import PoincareConjecture.Proofs.M38.ProjectiveReverse
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Components

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M38

theorem exists_sphere_collar_sides
    {M : Type*} [TopologicalSpace M] [T2Space M] [SimplyConnectedSpace M]
    [LocallyPathConnectedSpace M]
    (c : OpenPartialHomeomorph RoundCylinderSpace M)
    {δ : ℝ} (hδ : 0 < δ) (hcs : c.source = univ ×ˢ Ioo (-δ) δ) :
    let S := range (fun z : UnitTwoSphere => c (z, 0))
    ∃ A B : Set M,
      IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = Sᶜ ∧ frontier A = S ∧ frontier B = S ∧
      c '' (univ ×ˢ Ioo (-δ) 0) ⊆ A ∧
      c '' (univ ×ˢ Ioo 0 δ) ⊆ B := by
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := StandardCapSpace)
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 zero_le_one)
  let j : (UnitTwoSphere × Ioo (-δ) δ) ≃ₜ c.target :=
    ((Homeomorph.Set.prod (univ : Set UnitTwoSphere) (Ioo (-δ) δ)).trans
      ((Homeomorph.Set.univ UnitTwoSphere).prodCongr (Homeomorph.refl _))).symm.trans
        ((Homeomorph.setCongr hcs.symm).trans c.toHomeomorphSourceTarget)
  obtain ⟨A, B, hA, hB, hcA, hcB, hd, hcover, hfA, hfB, hn, hp⟩ :=
    Poincare.Topology.exists_collar_complementary_regions hδ c.open_target j
  refine ⟨A, B, hA, hB, hcA, hcB, hd, hcover, hfA, hfB, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hn ⟨(z.1, ⟨z.2, hz.2.1, hz.2.2.trans hδ⟩), hz.2.2, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hp ⟨(z.1, ⟨z.2, (neg_lt_zero.mpr hδ).trans hz.2.1, hz.2.2⟩), hz.2.1, rfl⟩

theorem sphere_collar_positive_closed_side
    {M : Type*} [TopologicalSpace M]
    {A B : Set M} (hA : IsOpen A) (hB : IsOpen B) (hd : Disjoint A B)
    (c : OpenPartialHomeomorph RoundCylinderSpace M)
    {δ : ℝ} (hδ : 0 < δ) (hcs : c.source = univ ×ˢ Ioo (-δ) δ)
    (hfB : frontier B = range (fun z : UnitTwoSphere => c (z, 0)))
    (hn : c '' (univ ×ˢ Ioo (-δ) 0) ⊆ A)
    (hp : c '' (univ ×ˢ Ioo 0 δ) ⊆ B) :
    interior (closure B) = B ∧
      frontier (closure B) = range (fun z : UnitTwoSphere => c (z, 0)) ∧
      ∀ y ∈ c.target, y ∈ closure B ↔ 0 ≤ (c.symm y).2 := by
  have hcl : closure B ⊆ Aᶜ := closure_minimal (disjoint_right.mp hd) hA.isClosed_compl
  have hzero (z : UnitTwoSphere) : (z, (0 : ℝ)) ∈ c.source :=
    hcs.symm ▸ ⟨mem_univ _, neg_lt_zero.mpr hδ, hδ⟩
  have hside (y : M) (hy : y ∈ c.target) :
      y ∈ closure B ↔ 0 ≤ (c.symm y).2 := by
    have hz := hcs ▸ c.map_target hy
    constructor
    · intro hclB
      by_contra ht
      exact hcl hclB (hn ⟨c.symm y,
        ⟨mem_univ _, hz.2.1, lt_of_not_ge ht⟩, c.right_inv hy⟩)
    · intro ht
      rcases lt_or_eq_of_le ht with ht | ht
      · exact subset_closure (hp ⟨c.symm y,
          ⟨mem_univ _, ht, hz.2.2⟩, c.right_inv hy⟩)
      · have hz0 : c.symm y = ((c.symm y).1, 0) := Prod.ext rfl ht.symm
        have hf : c ((c.symm y).1, 0) ∈ frontier B := hfB.symm ▸ mem_range_self _
        rw [← hz0, c.right_inv hy] at hf
        exact frontier_subset_closure hf
  have hi : interior (closure B) = B := by
    apply Subset.antisymm _ hB.subset_interior_closure
    intro y hy
    by_contra hyB
    have hyf : y ∈ frontier B := hB.frontier_eq.symm ▸ ⟨interior_subset hy, hyB⟩
    obtain ⟨z, rfl⟩ := hfB.subset hyf
    have himage : c.symm.IsImage (closure B) (univ ×ˢ Ici (0 : ℝ)) := by
      intro w hw
      simpa only [mem_prod, mem_univ, true_and, mem_Ici] using (hside w hw).symm
    have hpos := (himage.interior (c.map_source (hzero z))).mpr hy
    rw [c.left_inv (hzero z)] at hpos
    simp only [interior_prod_eq, interior_univ, interior_Ici, mem_prod,
      mem_univ, true_and, mem_Ioi, lt_self_iff_false] at hpos
  refine ⟨hi, ?_, hside⟩
  rw [isClosed_closure.frontier_eq, hi, ← hB.frontier_eq, hfB]

end PoincareConjecture.M38
