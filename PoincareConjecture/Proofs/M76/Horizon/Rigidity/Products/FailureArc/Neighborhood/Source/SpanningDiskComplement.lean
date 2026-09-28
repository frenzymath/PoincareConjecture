import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FinitePLDiskAttachment
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryAttachedDisk

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem exists_shell_complement_of_spanning_disk
    {S T D U V : Set P2} {a b c d : P2}
    (hS : IsFinitePLBallPair P2 S (frontier S))
    (hT : IsFinitePLBallPair P2 T (frontier T))
    (hD : IsFinitePLBallPair P2 D (frontier D))
    (hST : S ⊆ interior T) (hDT : D ⊆ T)
    (hU : IsFinitePLBallPair ℝ U {a,b}) (hV : IsFinitePLBallPair ℝ V {c,d})
    (hab : a ≠ b) (hcd : c ≠ d)
    (hDS : S ∩ D = V) (hVQ : V ⊆ frontier S) (hVD : V ⊆ frontier D)
    (hDU : D ∩ frontier T = U) :
    ∃ E : Set P2, IsFinitePLBallPair P2 E (frontier E) ∧
      E ∪ D = T \ interior S ∧
      E ∩ D = frontier D \ ((V \ {c,d}) ∪ (U \ {a,b})) ∧
      E ⊆ T \ interior S ∧
      frontier E = (E ∩ (frontier T ∪ frontier S)) ∪ (E ∩ D) := by
  let K := S ∪ D
  let Q := (frontier S ∪ frontier D) \ (V \ {c,d})
  have hK : IsFinitePLBallPair P2 K Q :=
    hS.union_of_boundary_interval hD hV hVQ hVD hcd hDS
  have hKQ : frontier K = Q := hK.frontier_eq_of_finrank_eq rfl
  have hKT : K ⊆ T := union_subset (hST.trans interior_subset) hDT
  have hSfront : Disjoint S (frontier T) :=
    disjoint_left.mpr (fun x hx hxt => hxt.2 (hST hx))
  have hKU : K ∩ frontier T = U := by
    change (S ∪ D) ∩ frontier T = U
    rw [union_inter_distrib_right,hSfront.inter_eq,empty_union,hDU]
  have hUQ : U ⊆ Q := by
    intro x hx
    obtain ⟨hxK,hxT⟩ := hKU.superset hx
    rw [←hKQ]
    exact ⟨subset_closure hxK,fun hi => hxT.2 (interior_mono hKT hi)⟩
  obtain ⟨W,hW,hUW,hUiW⟩ := hK.exists_boundary_arc_complement hU hUQ hab
  have hK' : IsFinitePLBallPair P2 K (U ∪ W) := hUW.symm ▸ hK
  have hproper : W \ {a,b} ⊆ T \ frontier T := by
    intro x hx
    have hxQ := hUW.subset (Or.inr hx.1)
    refine ⟨hKT (hK.1 hxQ),?_⟩
    intro hxT
    exact hx.2 (hUiW.subset ⟨hKU.subset ⟨hK.1 hxQ,hxT⟩,hx.1⟩)
  obtain ⟨Z,hZ,hUZ,hUiZ,hE,hcover,hinter,_,hEouter⟩ :=
    hT.exists_boundary_attached_disk_complement hK' hKT hU
      (fun _ hx => (hDU.superset hx).2) hW hab hproper
  let E := T \ (K \ W)
  have hEq : frontier E = W ∪ Z := hE.frontier_eq_of_finrank_eq rfl
  have hEsub : E ⊆ T \ interior S := by
    intro x hx
    refine ⟨hx.1,?_⟩
    intro hxS
    have hxK : x ∈ K := Or.inl (interior_subset hxS)
    have hxW := hinter.subset ⟨hxK,hx⟩
    have hxQ := hUW.subset (Or.inr hxW)
    have hfront := hKQ.superset hxQ
    exact hfront.2 (interior_mono (subset_union_left : S ⊆ K) hxS)
  have hDsub : D ⊆ T \ interior S := by
    intro x hx
    refine ⟨hDT hx,?_⟩
    intro hxS
    exact (hVQ (hDS.subset ⟨interior_subset hxS,hx⟩)).2 hxS
  have hED : E ∪ D = T \ interior S := by
    apply Subset.antisymm (union_subset hEsub hDsub)
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inr hxD
    · apply Or.inl
      refine ⟨hx.1,?_⟩
      rintro ⟨hxK,hxW⟩
      have hxS : x ∈ S := hxK.resolve_right hxD
      have hxQ : x ∈ Q := by
        exact ⟨Or.inl ⟨subset_closure hxS,hx.2⟩,
          fun hv => hxD ((hDS.superset hv.1).2)⟩
      rcases hUW.superset hxQ with hxU | hxW'
      · exact hxD ((hDU.superset hxU).1)
      · exact hxW hxW'
  have hDW : D ∩ W = frontier D \ ((V \ {c,d}) ∪ (U \ {a,b})) := by
    ext x
    constructor
    · rintro ⟨hxD,hxW⟩
      have hxQ := hUW.subset (Or.inr hxW)
      have hxfront : x ∈ frontier D := by
        rcases hxQ.1 with hxS | hxDq
        · exact hVD (hDS.subset ⟨hS.1 hxS,hxD⟩)
        · exact hxDq
      refine ⟨hxfront,?_⟩
      rintro (hxV | hxU)
      · exact hxQ.2 hxV
      · exact hxU.2 (hUiW.subset ⟨hxU.1,hxW⟩)
    · rintro ⟨hxD,hx⟩
      have hxQ : x ∈ Q := ⟨Or.inr hxD,fun h => hx (Or.inl h)⟩
      refine ⟨hD.1 hxD,?_⟩
      rcases hUW.superset hxQ with hxU | hxW
      · by_cases hend : x ∈ ({a,b} : Set P2)
        · exact hW.1 hend
        · exact (hx (Or.inr ⟨hxU,hend⟩)).elim
      · exact hxW
  refine ⟨E,hEq ▸ hE,hED,?_,hEsub,?_⟩
  · rw [←hDW]
    ext x
    constructor
    · exact fun h => ⟨h.2,hinter.subset ⟨Or.inr h.2,h.1⟩⟩
    · exact fun h => ⟨(hinter.superset h.2).2,h.1⟩
  · rw [hEq]
    ext x
    constructor
    · intro hx
      have hxE := hE.1 hx
      rcases hx with hxW | hxZ
      · rcases (hUW.subset (Or.inr hxW)).1 with hxS | hxD
        · exact Or.inl ⟨hxE,Or.inr hxS⟩
        · exact Or.inr ⟨hxE,hD.1 hxD⟩
      · exact Or.inl ⟨hxE,Or.inl ((hEouter.superset hxZ).2)⟩
    · rintro (⟨hxE,hxT|hxS⟩ | ⟨hxE,hxD⟩)
      · exact Or.inr (hEouter.subset ⟨hxE,hxT⟩)
      · by_cases hxD : x ∈ D
        · exact Or.inl (hinter.subset ⟨Or.inr hxD,hxE⟩)
        · have hxQ : x ∈ Q := ⟨Or.inl hxS,fun hv => hxD ((hDS.superset hv.1).2)⟩
          rcases hUW.superset hxQ with hxU | hxW
          · exact (hxD ((hDU.superset hxU).1)).elim
          · exact Or.inl hxW
      · exact Or.inl (hinter.subset ⟨Or.inr hxD,hxE⟩)

end PoincareConjecture.M76.Dehn.Annuli
