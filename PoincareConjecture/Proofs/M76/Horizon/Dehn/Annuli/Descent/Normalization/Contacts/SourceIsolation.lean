import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Contacts.FaceCharts

set_option autoImplicit false

open Set Geometry Topology

namespace Geometry.SimplicialComplex

theorem exists_projected_branch_face_neighborhood
    {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    {j : V → X} (hji : IsEmbedding (fun x : K.space ↦ j x))
    {p : X → Y} (branch : OpenPartialHomeomorph X Y)
    (hbranch : (branch : X → Y) = p)
    {a : Finset V} (ha : a ∈ K.faces)
    (hmax : ∀ b ∈ K.faces, a ⊆ b → b = a)
    {v : V} (hv : v ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set V)))
    (hvbranch : j v ∈ branch.source) :
    ∃ W : Set Y, IsOpen W ∧ p (j v) ∈ W ∧ W ⊆ branch.target ∧
      ∀ z ∈ W, ∀ q ∈ K.space, j q ∈ branch.source → p (j q) = z →
        q ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set V)) := by
  classical
  let bad : Set V := ⋃ b ∈ K.faces \ {a}, convexHull ℝ (b : Set V)
  have hbad : IsCompact bad :=
    (hK.sdiff : (K.faces \ {a}).Finite).isCompact_biUnion
      fun b _ ↦ b.finite_toSet.isCompact_convexHull ℝ
  have hbadK : bad ⊆ K.space := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp hx
    exact K.convexHull_subset_space hb.1 hxb
  have hjc : ContinuousOn j K.space := continuousOn_iff_continuous_domRestrict.mpr hji.continuous
  have hclosed : IsClosed (j '' bad) :=
    (hbad.image_of_continuousOn (hjc.mono hbadK)).isClosed
  have hvK : v ∈ K.space := K.convexHull_subset_space ha (intrinsicInterior_subset hv)
  have hvnot : v ∉ bad := by
    intro hvbad
    obtain ⟨b, hb, hvb⟩ := mem_iUnion₂.mp hvbad
    have hba := hmax b hb.1 (K.subset_of_mem_intrinsicInterior_face ha hb.1 hv hvb)
    exact hb.2 (mem_singleton_iff.mpr hba)
  let W := branch.target ∩ branch.symm ⁻¹' (j '' bad)ᶜ
  have hW : IsOpen W := branch.isOpen_inter_preimage_symm hclosed.isOpen_compl
  have hinverse {q : X} (hq : q ∈ branch.source) : branch.symm (p q) = q := by
    rw [← congrFun hbranch q]
    exact branch.left_inv hq
  refine ⟨W, hW, ?_, inter_subset_left, ?_⟩
  · refine ⟨congrFun hbranch (j v) ▸ branch.map_source hvbranch, ?_⟩
    change branch.symm (p (j v)) ∉ j '' bad
    rw [hinverse hvbranch]
    rintro ⟨q, hq, hqv⟩
    have heq : q = v := congrArg Subtype.val
      (hji.injective (a₁ := ⟨q, hbadK hq⟩) (a₂ := ⟨v, hvK⟩) hqv)
    exact hvnot (heq ▸ hq)
  · intro z hz q hq hqb hqz
    have hqnot : q ∉ bad := by
      intro hqbad
      apply hz.2
      have hqinv : branch.symm z = j q := by
        rw [← hqz]
        exact hinverse hqb
      exact ⟨q, hqbad, hqinv.symm⟩
    obtain ⟨b, hb, hqb⟩ := K.exists_face_intrinsicInterior_of_finite hK hq
    by_cases hba : b = a
    · exact hba ▸ hqb
    · exact False.elim (hqnot (mem_iUnion₂.mpr
        ⟨b, ⟨hb, hba⟩, intrinsicInterior_subset hqb⟩))

end Geometry.SimplicialComplex
