import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.ClosedComplement










set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K L₀ L₁ : SimplicialComplex ℝ E)



theorem not_face_meets_both_of_full_union
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ L₀.vertices ∪ L₁.vertices) →
      s ∈ L₀.faces ∨ s ∈ L₁.faces)
    (hdis : Disjoint L₀.space L₁.space) {s : Finset E} (hs : s ∈ K.faces) :
    ¬ ((∃ v ∈ s, v ∈ L₀.vertices) ∧ ∃ v ∈ s, v ∈ L₁.vertices) := by
  classical
  rintro ⟨⟨v, hv, hv₀⟩, w, hw, hw₁⟩
  have he : ({v, w} : Finset E) ∈ K.faces :=
    K.down_closed hs (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hv
      · exact hw) (Finset.insert_nonempty _ _)
  have hemark := hfull {v, w} he (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Or.inl hv₀
    · exact Or.inr hw₁)
  rcases hemark with he₀ | he₁
  · exact disjoint_left.mp hdis (L₀.subset_space he₀ (show w ∈ ({v, w} : Finset E) by simp))
      (L₁.subset_space hw₁ (Finset.mem_singleton_self w))
  · exact disjoint_left.mp hdis (L₀.subset_space hv₀ (Finset.mem_singleton_self v))
      (L₁.subset_space he₁ (show v ∈ ({v, w} : Finset E) by simp))


theorem barycentricNeighborhood_disjoint_of_full_union [Fintype K.faces]
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ L₀.vertices ∪ L₁.vertices) →
      s ∈ L₀.faces ∨ s ∈ L₁.faces)
    (hdis : Disjoint L₀.space L₁.space) :
    Disjoint (K.barycentricNeighborhood L₀).space (K.barycentricNeighborhood L₁).space := by
  classical
  rw [disjoint_left]
  intro x hx₀ hx₁
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx₀
  obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx₁
  have hxst := K.barycentricSubdivision.inter_subset_convexHull hs.1 ht.1 ⟨hxs, hxt⟩
  obtain ⟨z, hzs, hzt⟩ := convexHull_nonempty_iff.mp ⟨x, hxst⟩
  obtain ⟨a, ha, hav, haz⟩ := hs.2 z hzs
  obtain ⟨b, hb, hbv, hbz⟩ := ht.2 z hzt
  have hab : a = b := congrArg Subtype.val
    (K.faceCentroid_injective (show (⟨a, ha⟩ : K.faces).val.centroid ℝ id =
      (⟨b, hb⟩ : K.faces).val.centroid ℝ id from haz.trans hbz.symm))
  exact K.not_face_meets_both_of_full_union L₀ L₁ hfull hdis ha
    ⟨hav, hab.symm ▸ hbv⟩



theorem barycentricNeighborhood_union_faces [Fintype K.faces]
    (L : SimplicialComplex ℝ E) (hLv : L.vertices = L₀.vertices ∪ L₁.vertices)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ L₀.vertices ∪ L₁.vertices) →
      s ∈ L₀.faces ∨ s ∈ L₁.faces)
    (hdis : Disjoint L₀.space L₁.space) :
    (K.barycentricNeighborhood L).faces =
      (K.barycentricNeighborhood L₀).faces ∪ (K.barycentricNeighborhood L₁).faces := by
  classical
  ext t
  constructor
  · intro ht
    obtain ⟨a, ha, hfaces, hchain, heq⟩ :=
      (K.barycentricSubdivision_faces_of_face_chains t).mp ht.1
    obtain ⟨s, hs⟩ := ha
    have hscent : s.centroid ℝ id ∈ t := heq.symm ▸ Finset.mem_image_of_mem _ hs
    obtain ⟨u, hu, huv, hus⟩ := ht.2 _ hscent
    have hus' : u = s := congrArg Subtype.val (K.faceCentroid_injective
      (show (⟨u, hu⟩ : K.faces).val.centroid ℝ id =
        (⟨s, hfaces s hs⟩ : K.faces).val.centroid ℝ id from hus))
    subst u
    obtain ⟨v, hv, hvL⟩ := huv
    rcases hLv.subset hvL with hv₀ | hv₁
    · left
      refine ⟨ht.1, ?_⟩
      intro z hz
      obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp (heq ▸ hz)
      obtain ⟨u, hu, huv, huz⟩ := ht.2 z hz
      have huw : u = w := congrArg Subtype.val (K.faceCentroid_injective
        (show (⟨u, hu⟩ : K.faces).val.centroid ℝ id =
          (⟨w, hfaces w hw⟩ : K.faces).val.centroid ℝ id from huz.trans hwz.symm))
      subst u
      refine ⟨w, hfaces w hw, ?_, hwz⟩
      obtain ⟨q, hq, hqL⟩ := huv
      rcases hLv.subset hqL with hq₀ | hq₁
      · exact ⟨q, hq, hq₀⟩
      · rcases hchain s hs w hw with hsw | hws
        · exact (K.not_face_meets_both_of_full_union L₀ L₁ hfull hdis (hfaces w hw)
            ⟨⟨v, hsw hv, hv₀⟩, q, hq, hq₁⟩).elim
        · exact (K.not_face_meets_both_of_full_union L₀ L₁ hfull hdis (hfaces s hs)
            ⟨⟨v, hv, hv₀⟩, q, hws hq, hq₁⟩).elim
    · right
      refine ⟨ht.1, ?_⟩
      intro z hz
      obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp (heq ▸ hz)
      obtain ⟨u, hu, huv, huz⟩ := ht.2 z hz
      have huw : u = w := congrArg Subtype.val (K.faceCentroid_injective
        (show (⟨u, hu⟩ : K.faces).val.centroid ℝ id =
          (⟨w, hfaces w hw⟩ : K.faces).val.centroid ℝ id from huz.trans hwz.symm))
      subst u
      refine ⟨w, hfaces w hw, ?_, hwz⟩
      obtain ⟨q, hq, hqL⟩ := huv
      rcases hLv.subset hqL with hq₀ | hq₁
      · rcases hchain s hs w hw with hsw | hws
        · exact (K.not_face_meets_both_of_full_union L₀ L₁ hfull hdis (hfaces w hw)
            ⟨⟨q, hq, hq₀⟩, v, hsw hv, hv₁⟩).elim
        · exact (K.not_face_meets_both_of_full_union L₀ L₁ hfull hdis (hfaces s hs)
            ⟨⟨q, hws hq, hq₀⟩, v, hv, hv₁⟩).elim
      · exact ⟨q, hq, hq₁⟩
  · rintro (ht | ht)
    · refine ⟨ht.1, ?_⟩
      intro z hz
      obtain ⟨s, hs, ⟨v, hv, hvL⟩, hsz⟩ := ht.2 z hz
      exact ⟨s, hs, ⟨v, hv, hLv.symm.subset (Or.inl hvL)⟩, hsz⟩
    · refine ⟨ht.1, ?_⟩
      intro z hz
      obtain ⟨s, hs, ⟨v, hv, hvL⟩, hsz⟩ := ht.2 z hz
      exact ⟨s, hs, ⟨v, hv, hLv.symm.subset (Or.inr hvL)⟩, hsz⟩

end Geometry.SimplicialComplex
