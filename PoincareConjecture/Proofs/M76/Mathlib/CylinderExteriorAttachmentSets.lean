import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalFrontier










set_option autoImplicit false

open Set

namespace Set

variable {X : Type*} [TopologicalSpace X]





theorem top_face_inter_inner_cylinderExterior {u Q C d : Set X}
    (huQ : u ⊆ Q) (hQC : Q ⊆ C) (hcontact : u ∩ frontier Q = d) :
    (u ×ˢ {(1 : ℝ)}) ∩
        (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior Q ×ˢ {1}) = d ×ˢ {1} := by
  ext x
  constructor
  · intro hx
    have hxf : x.1 ∈ frontier Q :=
      ⟨subset_closure (huQ hx.1.1), fun hi => hx.2.2 ⟨hi, hx.1.2⟩⟩
    exact ⟨hcontact.subset ⟨hx.1.1, hxf⟩, hx.1.2⟩
  · intro hx
    have hxd := hcontact.symm.subset hx.1
    have htop : x ∈ u ×ˢ {(1 : ℝ)} := ⟨hxd.1, hx.2⟩
    exact ⟨htop, prod_singleton_one_subset_frontier_cylinder (huQ.trans hQC) htop,
      fun hi => hxd.2.2 hi.1⟩





theorem cylinderExterior_eq_union_of_boundary_cut {Q C b u d l : Set X}
    (hQC : Q ⊆ C) (hunion : b ∪ u = Q) (hinter : b ∩ u = l)
    (hfront : frontier b = d ∪ l) (hd : d ⊆ frontier Q) :
    frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior b ×ˢ {(1 : ℝ)} =
      (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior Q ×ˢ {1}) ∪ (u ×ˢ {1}) := by
  have hbQ : b ⊆ Q := fun _ hx => hunion.subset (Or.inl hx)
  have huQ : u ⊆ Q := fun _ hx => hunion.subset (Or.inr hx)
  have hibQ : interior b ⊆ interior Q := interior_mono hbQ
  apply Subset.antisymm
  · intro x hx
    by_cases hxtop : x ∈ interior Q ×ˢ {(1 : ℝ)}
    · have hxQ : x.1 ∈ Q := interior_subset hxtop.1
      rcases hunion.symm.subset hxQ with hxb | hxu
      · have hxfb : x.1 ∈ frontier b :=
          ⟨subset_closure hxb, fun hi => hx.2 ⟨hi, hxtop.2⟩⟩
        rcases hfront.subset hxfb with hxd | hxl
        · exact ((hd hxd).2 hxtop.1).elim
        · exact Or.inr ⟨(hinter.symm.subset hxl).2, hxtop.2⟩
      · exact Or.inr ⟨hxu, hxtop.2⟩
    · exact Or.inl ⟨hx.1, hxtop⟩
  · intro x hx
    rcases hx with hx | hx
    · exact ⟨hx.1, fun hi => hx.2 ⟨hibQ hi.1, hi.2⟩⟩
    · refine ⟨prod_singleton_one_subset_frontier_cylinder (huQ.trans hQC) hx, ?_⟩
      intro hi
      have hxl : x.1 ∈ l := hinter.subset ⟨interior_subset hi.1, hx.1⟩
      exact (hfront.symm.subset (Or.inr hxl)).2 hi.1

end Set
