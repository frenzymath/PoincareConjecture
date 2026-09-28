import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Models
import PoincareConjecture.Proofs.M54.ConnectedSum.Coordinates

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.SmoothProjectiveDoubleModel

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  (D : SmoothProjectiveDoubleModel M)

def collarRegion : Set M := D.collar '' (univ ×ˢ Ioo (-1 : ℝ) 1)

theorem isSimplyConnected_collar_image (a b : ℝ) (hab : a < b)
    (ha : -1 ≤ a) (hb : b ≤ 1) :
    IsSimplyConnected (D.collar '' (univ ×ˢ Ioo a b)) := by
  let S : Set RoundCylinderSpace := univ ×ˢ Ioo a b
  have hsub : S ⊆ univ ×ˢ Ioo (-1 : ℝ) 1 := by
    rintro z ⟨_, hz⟩
    exact ⟨mem_univ _, lt_of_le_of_lt ha hz.1, lt_of_lt_of_le hz.2 hb⟩
  have hval : IsLocalHomeomorph (Subtype.val : S → RoundCylinderSpace) :=
    (isOpen_univ.prod isOpen_Ioo).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hlocal : IsLocalHomeomorph (fun z : S => D.collar z) := by
    apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    exact D.collar_local_diffeomorph.isLocalHomeomorphOn.comp
      hval.isLocalHomeomorphOn (fun z _ => hsub z.property)
  have hinj : Function.Injective (fun z : S => D.collar z) := by
    intro z w h
    exact Subtype.ext (D.collar_injective (hsub z.property) (hsub w.property) h)
  have he := hlocal.isOpenEmbedding_of_injective hinj
  let : SimplyConnectedSpace S := SurgeryCoordinates.cylinder_interval_simplyConnected a b hab
  have h := (he.isEmbedding.isSimplyConnected_image (s := univ)).mpr
    (Homeomorph.Set.univ S).toHomotopyEquiv.simplyConnectedSpace
  have himage : (fun z : S => D.collar z) '' univ = D.collar '' S := by
    ext y
    simp only [mem_image, mem_univ, true_and, Subtype.exists, exists_prop]
  exact himage ▸ h

theorem first_inter_collarRegion :
    D.first_region ∩ D.collarRegion = D.collar '' (univ ×ˢ Ioo (-1 : ℝ) 0) := by
  ext y
  constructor
  · rintro ⟨hy, z, hz, rfl⟩
    refine ⟨z, ⟨mem_univ _, hz.2.1, ?_⟩, rfl⟩
    rcases lt_trichotomy z.2 0 with hn | he | hp
    · exact hn
    · exfalso
      have hs : D.collar z ∈ D.sphere :=
        D.collar_sphere ▸ mem_image_of_mem D.collar ⟨mem_univ _, he⟩
      exact Set.disjoint_left.mp D.sphere_disjoint hs (Or.inl hy)
    · exact (Set.disjoint_left.mp D.disjoint hy
        (D.collar_positive (mem_image_of_mem D.collar ⟨mem_univ _, hp, hz.2.2⟩))).elim
  · rintro ⟨z, hz, rfl⟩
    exact ⟨D.collar_negative (mem_image_of_mem D.collar hz),
      mem_image_of_mem D.collar ⟨mem_univ _, hz.2.1, hz.2.2.trans (by norm_num)⟩⟩

theorem second_inter_collarRegion :
    D.second_region ∩ D.collarRegion = D.collar '' (univ ×ˢ Ioo (0 : ℝ) 1) := by
  ext y
  constructor
  · rintro ⟨hy, z, hz, rfl⟩
    refine ⟨z, ⟨mem_univ _, ?_, hz.2.2⟩, rfl⟩
    rcases lt_trichotomy z.2 0 with hn | he | hp
    · exact (Set.disjoint_left.mp D.disjoint
        (D.collar_negative (mem_image_of_mem D.collar ⟨mem_univ _, hz.2.1, hn⟩)) hy).elim
    · exfalso
      have hs : D.collar z ∈ D.sphere :=
        D.collar_sphere ▸ mem_image_of_mem D.collar ⟨mem_univ _, he⟩
      exact Set.disjoint_left.mp D.sphere_disjoint hs (Or.inr hy)
    · exact hp
  · rintro ⟨z, hz, rfl⟩
    exact ⟨D.collar_positive (mem_image_of_mem D.collar hz),
      mem_image_of_mem D.collar ⟨mem_univ _, (by norm_num : (-1 : ℝ) < 0).trans hz.2.1,
        hz.2.2⟩⟩

theorem collarRegion_simplyConnected : IsSimplyConnected D.collarRegion :=
  D.isSimplyConnected_collar_image (-1) 1 (by norm_num) le_rfl le_rfl

theorem first_inter_collarRegion_simplyConnected :
    IsSimplyConnected (D.first_region ∩ D.collarRegion) := by
  rw [D.first_inter_collarRegion]
  exact D.isSimplyConnected_collar_image (-1) 0 (by norm_num) le_rfl (by norm_num)

theorem second_inter_collarRegion_simplyConnected :
    IsSimplyConnected (D.second_region ∩ D.collarRegion) := by
  rw [D.second_inter_collarRegion]
  exact D.isSimplyConnected_collar_image 0 1 (by norm_num) (by norm_num) le_rfl

theorem enlarged_cover :
    (D.first_region ∪ D.collarRegion) ∪ (D.second_region ∪ D.collarRegion) = univ := by
  apply eq_univ_of_forall
  intro x
  have hx : x ∈ D.first_region ∪ D.second_region ∪ D.sphere := D.cover ▸ mem_univ x
  rcases hx with (h | h) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)
  · obtain ⟨z, hz, rfl⟩ := D.collar_sphere.symm ▸ h
    exact Or.inl (Or.inr (mem_image_of_mem D.collar
      ⟨mem_univ _, by simpa only [mem_singleton_iff.mp hz.2] using
        (show (0 : ℝ) ∈ Ioo (-1) 1 by norm_num)⟩))

theorem enlarged_inter :
    (D.first_region ∪ D.collarRegion) ∩ (D.second_region ∪ D.collarRegion) =
      D.collarRegion := by
  ext x
  constructor
  · rintro ⟨h | h, k | k⟩
    · exact (Set.disjoint_left.mp D.disjoint h k).elim
    · exact k
    · exact h
    · exact h
  · exact fun h => ⟨Or.inr h, Or.inr h⟩

end PoincareConjecture.SmoothProjectiveDoubleModel
