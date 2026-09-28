import PoincareConjecture.Proofs.M76.Rigidity.OriginalLowerProducts
import PoincareConjecture.Proofs.M76.Rigidity.OriginalEdgeProducts










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)




theorem exists_lower_products : Nonempty (OriginalLowerProducts T) := by
  classical
  obtain ⟨F⟩ := T.exists_triangle_fibers
  let S := {s : Finset (T.index → ℝ × V3) // s ∈ (T.marked 2).faces ∧ 2 ≤ s.card}
  have hpieces (s : S) : ∃ P : OriginalDiskFaceProduct T s,
      (∀ t ∈ (T.marked 2).faces, t.card = 3 → (s : Finset (T.index → ℝ × V3)) ⊆ t →
        ∀ x ∈ T.diskDualBase t ×ˢ I, P.map x = F.map t x.2) ∧
      ((s : Finset (T.index → ℝ × V3)).card = 2 →
        (s : Finset (T.index → ℝ × V3)) ∈ (T.marked 1).faces →
        (fun r : ℝ => P.map ((s : Finset (T.index → ℝ × V3)).centroid ℝ id, r)) '' I =
          T.dualRegion s ∩ (T.marked 1).space) := by
    have hbound := T.disk_face_card_le s.property.1
    by_cases hc : (s : Finset (T.index → ℝ × V3)).card = 2
    · obtain ⟨P, hP, hPB⟩ := F.exists_edge_product s.property.1 hc
      exact ⟨P, hP, fun _ => hPB⟩
    · have hsc : (s : Finset (T.index → ℝ × V3)).card = 3 := by omega
      obtain ⟨P, hP⟩ := F.exists_triangle_product s.property.1 hsc
      refine ⟨P, ?_, fun h => False.elim (hc h)⟩
      intro t _ htc hst x _
      have he : (s : Finset (T.index → ℝ × V3)) = t :=
        Finset.eq_of_subset_of_card_le hst (by omega)
      exact (hP x).trans
        (congrArg (fun v : Finset (T.index → ℝ × V3) => F.map v x.2) he)
  choose P htri hfront using hpieces
  let g : Finset (T.index → ℝ × V3) → (T.index → ℝ × V3) × ℝ → (T.index → ℝ × V3) :=
    fun s => if h : s ∈ (T.marked 2).faces ∧ 2 ≤ s.card then (P ⟨s, h⟩).map else fun _ => 0
  have hval (s : S) : g s = (P s).map := by
    simp only [g, dif_pos s.property]
    rfl
  have hrestrict {s t : Finset (T.index → ℝ × V3)}
      (hs : s ∈ (T.marked 2).faces) (hsc : 2 ≤ s.card)
      (ht : t ∈ (T.marked 2).faces) (hst : s ⊆ t) :
      EqOn (g s) (g t) (T.diskDualBase t ×ˢ I) := by
    have htc : 2 ≤ t.card := hsc.trans (Finset.card_le_card hst)
    by_cases he : s = t
    · subst t
      exact fun _ _ => rfl
    · have hc3 : t.card = 3 := by
        have hstrict := Finset.card_lt_card (hst.ssubset_of_ne he)
        have hbound := T.disk_face_card_le ht
        omega
      intro x hx
      rw [hval ⟨s, hs, hsc⟩, hval ⟨t, ht, htc⟩]
      exact (htri ⟨s, hs, hsc⟩ t ht hc3 hst x hx).trans
        (htri ⟨t, ht, htc⟩ t ht hc3 Subset.rfl x hx).symm
  have hbaseinter (s t : Finset (T.index → ℝ × V3)) :
      T.diskDualBase s ∩ T.diskDualBase t = T.diskDualBase (s ∪ t) := by
    change (T.dualRegion s ∩ (T.marked 2).space) ∩
      (T.dualRegion t ∩ (T.marked 2).space) = T.dualRegion (s ∪ t) ∩ (T.marked 2).space
    rw [← T.dualRegion_inter]
    ext x
    exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2⟩,
      fun h => ⟨⟨h.1.1, h.2⟩, h.1.2, h.2⟩⟩
  have hempty {s t : Finset (T.index → ℝ × V3)}
      (hs : s ∈ (T.marked 2).faces) (ht : t ∈ (T.marked 2).faces)
      (hu : s ∪ t ∉ (T.marked 2).faces) : T.dualRegion (s ∪ t) = ∅ := by
    apply T.dualRegion_eq_empty_of_not_disk_face
      (((T.marked 2).nonempty_of_mem_faces hs).mono Finset.subset_union_left) ?_ hu
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (T.marked 2).face_subset_vertices hs hx
    · exact (T.marked 2).face_subset_vertices ht hx
  have hbaseempty {s t : Finset (T.index → ℝ × V3)}
      (hs : s ∈ (T.marked 2).faces) (ht : t ∈ (T.marked 2).faces)
      (hu : s ∪ t ∉ (T.marked 2).faces) : T.diskDualBase (s ∪ t) = ∅ := by
    change T.dualRegion (s ∪ t) ∩ (T.marked 2).space = ∅
    rw [hempty hs ht hu, empty_inter]
  refine ⟨⟨g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact (P ⟨s, hs, hc⟩).piecewiseAffine
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact (P ⟨s, hs, hc⟩).injective
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact (P ⟨s, hs, hc⟩).image_eq
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact (P ⟨s, hs, hc⟩).central
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact (P ⟨s, hs, hc⟩).proper
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact (P ⟨s, hs, hc⟩).rim
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact (P ⟨s, hs, hc⟩).positive
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact (P ⟨s, hs, hc⟩).negative
  · intro s hs hc t ht hst x hx
    exact hrestrict hs hc ht hst hx
  · intro s hs hsc t ht htc x hx
    have hxU : x ∈ T.diskDualBase (s ∪ t) ×ˢ I :=
      ⟨(hbaseinter s t).subset hx.1, hx.2⟩
    by_cases hu : s ∪ t ∈ (T.marked 2).faces
    · exact (hrestrict hs hsc hu Finset.subset_union_left hxU).trans
        (hrestrict ht htc hu Finset.subset_union_right hxU).symm
    · exact False.elim ((hbaseempty hs ht hu).subset hxU.1)
  · intro s hs hsc t ht htc
    rw [hbaseinter, T.dualRegion_inter]
    by_cases hu : s ∪ t ∈ (T.marked 2).faces
    · have huc : 2 ≤ (s ∪ t).card :=
        hsc.trans (Finset.card_le_card Finset.subset_union_left)
      calc
        g s '' (T.diskDualBase (s ∪ t) ×ˢ I) =
            g (s ∪ t) '' (T.diskDualBase (s ∪ t) ×ˢ I) :=
          image_congr (hrestrict hs hsc hu Finset.subset_union_left)
        _ = T.dualRegion (s ∪ t) := by
          rw [hval ⟨s ∪ t, hu, huc⟩]
          exact (P ⟨s ∪ t, hu, huc⟩).image_eq
    · rw [hbaseempty hs ht hu, empty_prod, image_empty, hempty hs ht hu]
  · intro s hs hc hsB
    have hsc : 2 ≤ s.card := by omega
    rw [hval ⟨s, hs, hsc⟩]
    exact hfront ⟨s, hs, hsc⟩ hc hsB

end PoincareConjecture.M76.OriginalProperDiskTriangulation
