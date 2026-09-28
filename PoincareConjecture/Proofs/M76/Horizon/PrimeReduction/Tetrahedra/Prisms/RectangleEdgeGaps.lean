import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.EdgeIntervalMatching

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
open TriangleCorner

theorem rectangle_edge_gaps
    {E : Type*} (e : (ℝ × ℝ) → E) (he : Function.Injective e)
    {M Q T D Z : Set E} {a b u v : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) (hv : 0 < v)
    (hDZ : Disjoint D Z)
    (hMQ : M ∩ Q = e '' edgeIntervals a b u v)
    (hMT : M ∩ T = D ∪ Z)
    (hDQ : D ∩ Q = e '' ({(0,b),(a,0)} : Set (ℝ × ℝ)))
    (hZQ : Z ∩ Q = e '' ({(0,v),(u,0)} : Set (ℝ × ℝ))) :
    a < u ∧ b < v ∧
      Disjoint (e '' ({0} ×ˢ Ioo b v)) T ∧
      Disjoint (e '' (Ioo a u ×ˢ {0})) T ∧
      e (0,b) ∈ T ∧ e (a,0) ∈ T ∧ e (0,v) ∈ T ∧ e (u,0) ∈ T := by
  have hpD : e (0,b) ∈ D ∩ Q := hDQ.symm.subset (mem_image_of_mem e (by simp))
  have hqD : e (a,0) ∈ D ∩ Q := hDQ.symm.subset (mem_image_of_mem e (by simp))
  have hpZ : e (0,v) ∈ Z ∩ Q := hZQ.symm.subset (mem_image_of_mem e (by simp))
  have hqZ : e (u,0) ∈ Z ∩ Q := hZQ.symm.subset (mem_image_of_mem e (by simp))
  have hDM : D ⊆ M := fun x hx => (hMT.symm.subset (Or.inl hx)).1
  have hZM : Z ⊆ M := fun x hx => (hMT.symm.subset (Or.inr hx)).1
  have hDT : D ⊆ T := fun x hx => (hMT.symm.subset (Or.inl hx)).2
  have hZT : Z ⊆ T := fun x hx => (hMT.symm.subset (Or.inr hx)).2
  have hau : a < u := by
    have hm := he.mem_set_image.mp (hMQ.subset ⟨hDM hqD.1,hqD.2⟩)
    rcases hm with hm | hm
    · exact (ha.ne' hm.1).elim
    · apply lt_of_le_of_ne hm.1.2
      intro hau
      subst u
      exact disjoint_left.mp hDZ hqD.1 hqZ.1
  have hbv : b < v := by
    have hm := he.mem_set_image.mp (hMQ.subset ⟨hDM hpD.1,hpD.2⟩)
    rcases hm with hm | hm
    · apply lt_of_le_of_ne hm.2.2
      intro hbv
      subst v
      exact disjoint_left.mp hDZ hpD.1 hpZ.1
    · exact (hb.ne' hm.2).elim
  refine ⟨hau,hbv,?_,?_,hDT hpD.1,hDT hqD.1,hZT hpZ.1,hZT hqZ.1⟩
  · apply disjoint_left.mpr
    rintro x ⟨⟨s,t⟩,⟨hs,ht⟩,rfl⟩ hxT
    have hs0 : s = 0 := hs
    subst s
    have hxMQ := hMQ.symm.subset (mem_image_of_mem e
      (show (0,t) ∈ edgeIntervals a b u v from Or.inl ⟨by simp,ht.1.le,ht.2.le⟩))
    rcases hMT.subset ⟨hxMQ.1,hxT⟩ with hxD | hxZ
    · have hm := he.mem_set_image.mp (hDQ.subset ⟨hxD,hxMQ.2⟩)
      rcases hm with hm | hm
      · exact ht.1.ne' (congrArg Prod.snd hm)
      · exact ha.ne' (congrArg Prod.fst (mem_singleton_iff.mp hm)).symm
    · have hm := he.mem_set_image.mp (hZQ.subset ⟨hxZ,hxMQ.2⟩)
      rcases hm with hm | hm
      · exact ht.2.ne (congrArg Prod.snd hm)
      · exact hu.ne' (congrArg Prod.fst (mem_singleton_iff.mp hm)).symm
  · apply disjoint_left.mpr
    rintro x ⟨⟨s,t⟩,⟨hs,ht⟩,rfl⟩ hxT
    have ht0 : t = 0 := ht
    subst t
    have hxMQ := hMQ.symm.subset (mem_image_of_mem e (Or.inr ⟨⟨hs.1.le,hs.2.le⟩,rfl⟩))
    rcases hMT.subset ⟨hxMQ.1,hxT⟩ with hxD | hxZ
    · have hm := he.mem_set_image.mp (hDQ.subset ⟨hxD,hxMQ.2⟩)
      rcases hm with hm | hm
      · exact hb.ne' (congrArg Prod.snd hm).symm
      · exact hs.1.ne' (congrArg Prod.fst (mem_singleton_iff.mp hm))
    · have hm := he.mem_set_image.mp (hZQ.subset ⟨hxZ,hxMQ.2⟩)
      rcases hm with hm | hm
      · exact hv.ne' (congrArg Prod.snd hm).symm
      · exact hs.2.ne (congrArg Prod.fst (mem_singleton_iff.mp hm))

end PoincareConjecture.M76.PrismBelt
