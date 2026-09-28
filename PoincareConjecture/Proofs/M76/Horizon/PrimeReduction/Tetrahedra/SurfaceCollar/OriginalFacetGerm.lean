import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalBoundaryGraph

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_original_tetrahedron_facet_frontier_germ
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X)
    (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (s : K.FaceOfCard 3) (hst : s.1 ⊆ t) {x : E}
    (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s.1 : Set E))) :
    ∃ W : Set X, IsOpen W ∧ g x ∈ W ∧
      ∀ y ∈ W, y ∈ g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ↔
        y ∈ g '' convexHull ℝ (s.1 : Set E) := by
  classical
  let F := {u : K.FaceOfCard 3 // u.1 ⊆ t}
  let := K.finite_faceOfCard hK 3
  have hfacet (u : F) : convexHull ℝ (u.1.1 : Set E) ⊆
      intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) := by
    apply (K.indep ht).convexHull_subset_intrinsicFrontier
    exact Finset.ssubset_iff_subset_ne.mpr ⟨u.2, fun heq => by
      have h := congrArg Finset.card heq
      rw [u.1.2.2,ht4] at h
      omega⟩
  have hcover : intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) =
      ⋃ u : F, convexHull ℝ (u.1.1 : Set E) := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨v,hv,hzv⟩ := ((K.indep ht).mem_intrinsicFrontier_convexHull_finset
        (K.nonempty_of_mem_faces ht) z).mp hz
      have hc : (t.erase v).card = 3 := by rw [Finset.card_erase_of_mem hv,ht4]
      have hface := K.down_closed ht (Finset.erase_subset v t)
        (Finset.card_pos.mp (show 0 < (t.erase v).card by omega))
      exact mem_iUnion.mpr ⟨⟨⟨t.erase v,hface,hc⟩,Finset.erase_subset v t⟩,hzv⟩
    · exact iUnion_subset hfacet
  have hxnot (u : F) (hu : u.1 ≠ s) : x ∉ convexHull ℝ (u.1.1 : Set E) := by
    intro hxu
    have hxs := intrinsicInterior_subset hx
    have hinter := K.inter_subset_convexHull s.2.1 u.1.2.1 ⟨hxs,hxu⟩
    have hproper : s.1 ∩ u.1.1 ⊂ s.1 := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.inter_subset_left,?_⟩
      intro h
      have hsub : s.1 ⊆ u.1.1 := by rw [←h]; exact Finset.inter_subset_right
      have heq : s.1 = u.1.1 := Finset.eq_of_subset_of_card_le hsub
        (by rw [s.2.2,u.1.2.2])
      exact hu (Subtype.ext heq.symm)
    have hxf := (K.indep s.2.1).convexHull_subset_intrinsicFrontier hproper
      (by simpa only [Finset.coe_inter] using hinter)
    rw [←intrinsicClosure_sdiff_intrinsicInterior] at hxf
    exact hxf.2 hx
  let bad := ⋃ u : {u : F // u.1 ≠ s}, g '' convexHull ℝ (u.1.1.1 : Set E)
  have hbad : IsClosed bad := isClosed_iUnion_of_finite fun u =>
    ((u.1.1.1.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
      (hgc.mono (K.convexHull_subset_space u.1.1.2.1))).isClosed
  refine ⟨badᶜ,hbad.isOpen_compl,?_,?_⟩
  · intro h
    obtain ⟨u,z,hz,hzg⟩ := mem_iUnion.mp h
    have heq := hgi (K.convexHull_subset_space u.1.1.2.1 hz)
      (K.convexHull_subset_space s.2.1 (intrinsicInterior_subset hx)) hzg
    exact hxnot u.1 u.2 (heq ▸ hz)
  · intro y hy
    constructor
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨u,hzu⟩ := mem_iUnion.mp (hcover.subset hz)
      by_cases hus : u.1 = s
      · exact ⟨z,by simpa only [hus] using hzu,rfl⟩
      · exact False.elim (hy (mem_iUnion.mpr ⟨⟨u,hus⟩,z,hzu,rfl⟩))
    · intro h
      exact image_mono (hfacet ⟨s,hst⟩) h

end PoincareConjecture.M76
