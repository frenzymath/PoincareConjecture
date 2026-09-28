import PoincareConjecture.Proofs.M76.Mathlib.DerivedStarFaces
import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier










set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

open PoincareConjecture.Proofs.M02.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]
  (c : K.faces → E)
  (hc : ∀ s : K.faces, ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
    (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c s)




theorem derived_closedStar_faceCenter_space_of_maximal [DecidableEq E]
    (s : K.faces) (hmax : ∀ t : K.faces, s ≤ t → t = s) :
    ((K.derivedSubdivision c hc).closedStar (c s)).space =
      convexHull ℝ (s.val : Set E) := by
  classical
  have hcinj := K.positiveFaceCenter_injective c hc
  have hcenter (i : K.faces) : c i ∈ convexHull ℝ (i.val : Set E) := by
    obtain ⟨w, hw, hsum, hval⟩ := hc i
    exact Finset.mem_convexHull'.mpr
      ⟨w, fun v hv => (hw v hv).le, hsum, hval⟩
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
    obtain ⟨b, _, hchain, hbt⟩ :=
      (K.derivedSubdivision_faces c hc (insert (c s) t)).mp ht.2
    have hsb : s ∈ b := by
      have hcs : c s ∈ b.image c := by
        rw [← hbt]
        exact Finset.mem_insert_self _ _
      obtain ⟨j, hj, hjs⟩ := Finset.mem_image.mp hcs
      exact hcinj hjs ▸ hj
    apply (convexHull_min ?_ (convex_convexHull ℝ _)) hxt
    intro z hz
    have hzb : z ∈ b.image c := by
      rw [← hbt]
      exact Finset.mem_insert_of_mem hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hzb
    have hjs : j ≤ s := by
      rcases hchain j hj s hsb with h | h
      · exact h
      · rw [hmax j h]
    exact convexHull_mono hjs (hcenter j)
  · intro hx
    have hclosed (u : Finset E) (hu : u ∈ K.faces) (t : Finset E) (htu : t ⊆ u)
        (ht : ∃ z ∈ convexHull ℝ (t : Set E), (0 : E →ᵃ[ℝ] ℝ) z = 0) :
        t ∈ K.faces := by
      obtain ⟨z, hz, _⟩ := ht
      exact K.down_closed hu htu
        (Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨z, hz⟩))
    obtain ⟨a, ha, hchain, has, hxa⟩ := exists_geometric_affine_section_flag
      (0 : E →ᵃ[ℝ] ℝ) K.faces hclosed c (fun i => ⟨rfl, hc i⟩) s x hx rfl
    apply mem_space_iff.mpr
    refine ⟨a.image c, ⟨?_, ?_⟩, ?_⟩
    · exact (K.derivedSubdivision_faces c hc _).mpr ⟨a, ha, hchain, rfl⟩
    · apply (K.derivedSubdivision_faces c hc _).mpr
      refine ⟨insert s a, Finset.insert_nonempty _ _, ?_, ?_⟩
      · intro i hi j hj
        rcases Finset.mem_insert.mp hi with his | hi
        · rw [his]
          rcases Finset.mem_insert.mp hj with hjs | hj
          · rw [hjs]
            exact Or.inl le_rfl
          · exact Or.inr (has j hj)
        · rcases Finset.mem_insert.mp hj with hjs | hj
          · rw [hjs]
            exact Or.inl (has i hi)
          · exact hchain i hi j hj
      · simp only [Finset.image_insert]
    · simpa only [Finset.coe_image] using hxa





theorem derived_link_faceCenter_space_of_maximal [DecidableEq E]
    (s : K.faces) (hmax : ∀ t : K.faces, s ≤ t → t = s) :
    ((K.derivedSubdivision c hc).link (c s)).space =
      intrinsicFrontier ℝ (convexHull ℝ (s.val : Set E)) := by
  classical
  have hcinj := K.positiveFaceCenter_injective c hc
  have hcenter (i : K.faces) : c i ∈ convexHull ℝ (i.val : Set E) := by
    obtain ⟨w, hw, hsum, hval⟩ := hc i
    exact Finset.mem_convexHull'.mpr
      ⟨w, fun v hv => (hw v hv).le, hsum, hval⟩
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
    obtain ⟨a, ha, hchaina, hat⟩ := (K.derivedSubdivision_faces c hc t).mp ht.1
    obtain ⟨b, _, hchainb, hbt⟩ :=
      (K.derivedSubdivision_faces c hc (insert (c s) t)).mp ht.2.2
    have hsb : s ∈ b := by
      have hcs : c s ∈ b.image c := by
        rw [← hbt]
        exact Finset.mem_insert_self _ _
      obtain ⟨j, hj, hjs⟩ := Finset.mem_image.mp hcs
      exact hcinj hjs ▸ hj
    obtain ⟨m, hm, hmaxm⟩ := Finset.exists_maximal ha
    have hcmt : c m ∈ t := by
      rw [hat]
      exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
    have hmb : m ∈ b := by
      have hcmb : c m ∈ b.image c := by
        rw [← hbt]
        exact Finset.mem_insert_of_mem hcmt
      obtain ⟨j, hj, hjm⟩ := Finset.mem_image.mp hcmb
      exact hcinj hjm ▸ hj
    have hms : m ≤ s := by
      rcases hchainb m hmb s hsb with h | h
      · exact h
      · rw [hmax m h]
    have hne : m.val ≠ s.val := by
      intro h
      have hms' : m = s := Subtype.ext h
      exact ht.2.1 (hms' ▸ hcmt)
    apply (K.indep s.property).convexHull_subset_intrinsicFrontier
      (lt_of_le_of_ne hms hne)
    apply (convexHull_min ?_ (convex_convexHull ℝ _)) hxt
    intro z hz
    rw [hat] at hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have him : i ≤ m := by
      rcases hchaina i hi m hm with h | h
      · exact h
      · exact hmaxm hi h
    exact convexHull_mono him (hcenter i)
  · intro hx
    obtain ⟨v, hv, hxv⟩ := ((K.indep s.property).mem_intrinsicFrontier_convexHull_finset
      (K.nonempty_of_mem_faces s.property) x).mp hx
    have hnonempty : (s.val.erase v).Nonempty :=
      Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxv⟩)
    let u : K.faces := ⟨s.val.erase v,
      K.down_closed s.property (Finset.erase_subset _ _) hnonempty⟩
    have hclosed (w : Finset E) (hw : w ∈ K.faces) (t : Finset E) (htw : t ⊆ w)
        (ht : ∃ z ∈ convexHull ℝ (t : Set E), (0 : E →ᵃ[ℝ] ℝ) z = 0) :
        t ∈ K.faces := by
      obtain ⟨z, hz, _⟩ := ht
      exact K.down_closed hw htw
        (Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨z, hz⟩))
    obtain ⟨a, ha, hchain, hau, hxa⟩ := exists_geometric_affine_section_flag
      (0 : E →ᵃ[ℝ] ℝ) K.faces hclosed c (fun i => ⟨rfl, hc i⟩) u x hxv rfl
    have has (i : K.faces) (hi : i ∈ a) : i ≤ s :=
      (hau i hi).trans (Finset.erase_subset _ _)
    have hsa : s ∉ a := by
      intro hs
      exact Finset.notMem_erase v s.val (hau s hs hv)
    apply mem_space_iff.mpr
    refine ⟨a.image c, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact (K.derivedSubdivision_faces c hc _).mpr ⟨a, ha, hchain, rfl⟩
    · rintro hcs
      obtain ⟨i, hi, his⟩ := Finset.mem_image.mp hcs
      exact hsa (hcinj his ▸ hi)
    · apply (K.derivedSubdivision_faces c hc _).mpr
      refine ⟨insert s a, Finset.insert_nonempty _ _, ?_, ?_⟩
      · intro i hi j hj
        rcases Finset.mem_insert.mp hi with his | hi
        · rw [his]
          rcases Finset.mem_insert.mp hj with hjs | hj
          · rw [hjs]
            exact Or.inl le_rfl
          · exact Or.inr (has j hj)
        · rcases Finset.mem_insert.mp hj with hjs | hj
          · rw [hjs]
            exact Or.inl (has i hi)
          · exact hchain i hi j hj
      · simp only [Finset.image_insert]
    · simpa only [Finset.coe_image] using hxa

end Geometry.SimplicialComplex
